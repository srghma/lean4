// Lean compiler output
// Module: Lake.Util.Log
// Imports: Lean.Data.Json Lake.Util.Error Lake.Util.EStateT Lean.Message Lake.Util.Lift Init.Data.String.TakeDrop Init.Data.String.Modify
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Control::State::l_instMonadStateOfStateTOfMonad___redArg;
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any,
    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold, l_Array_append___redArg,
    l_Array_shrink___redArg, l_List_foldl___at___00Array_appendList_spec__0___redArg,
};
use crate::r#gen::Init::Data::Repr::l_Repr_addAppParen;
use crate::r#gen::Init::Data::String::Modify::{
    initialize_Init_Data_String_Modify, runtime_initialize_Init_Data_String_Modify,
};
use crate::r#gen::Init::Data::String::Slice::{l_String_Slice_toString, l_String_Slice_trimAscii};
use crate::r#gen::Init::Data::String::TakeDrop::{
    initialize_Init_Data_String_TakeDrop, runtime_initialize_Init_Data_String_TakeDrop,
};
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Init::Prelude::{
    l_Array_extract___redArg, l_ByteArray_empty, l_Char_utf8Size, l_ReaderT_instMonad___redArg,
    l_panic___redArg,
};
use crate::r#gen::Init::System::IO::{
    l_IO_FS_Stream_ofBuffer, l_IO_FS_Stream_putStrLn, l_IO_mkRef___boxed, l_IO_setStderr___boxed,
    l_IO_setStdout___boxed, l_instMonadBaseIO, l_instMonadEIO, lean_stream_of_handle,
};
use crate::r#gen::Init::System::IOError::lean_io_error_to_string;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lake::Util::EStateT::{
    initialize_Lake_Util_EStateT, l_Lake_EResult_result_x3f___boxed,
    l_Lake_EResult_toExcept___boxed, l_Lake_EResult_toProd, l_Lake_EResult_toProd_x3f,
    l_Lake_EStateT_instFunctor___redArg, l_Lake_EStateT_instMonad___redArg___lam__1,
    l_Lake_EStateT_instMonad___redArg___lam__3, l_Lake_EStateT_instMonad___redArg___lam__5,
    l_Lake_EStateT_instMonad___redArg___lam__9, l_Lake_EStateT_instMonadStateOfOfPure___redArg,
    l_Lake_EStateT_instPure___redArg___lam__0, runtime_initialize_Lake_Util_EStateT,
};
use crate::r#gen::Lake::Util::Error::{
    initialize_Lake_Util_Error, runtime_initialize_Lake_Util_Error,
};
use crate::r#gen::Lake::Util::Lift::{
    initialize_Lake_Util_Lift, runtime_initialize_Lake_Util_Lift,
};
use crate::r#gen::Lean::Data::Json::Basic::{
    l_Lean_Json_getObjValD, l_Lean_Json_getStr_x3f, l_Lean_Json_mkObj,
};
use crate::r#gen::Lean::Data::Json::FromToJson::Basic::{
    l_Array_fromJson_x3f___redArg, l_Array_toJson___redArg, l_Lean_Json_getTag_x3f,
};
use crate::r#gen::Lean::Data::Json::{
    initialize_Lean_Data_Json, runtime_initialize_Lean_Data_Json,
};
use crate::r#gen::Lean::Message::{
    initialize_Lean_Message, l_Lean_MessageData_toString, l_Lean_mkErrorStringWithPos,
    runtime_initialize_Lean_Message,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_array_uget_borrowed;
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::String::Basic::{
    lean_string_utf8_extract, lean_string_utf8_get_fast, lean_string_validate_utf8,
};
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::String::Modify::lean_string_utf8_set;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_uint32_add, lean_usize_add, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_push, lean_array_to_list, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_string_dec_eq,
    lean_string_from_utf8_unchecked, lean_string_utf8_byte_size, lean_uint32_dec_le,
    lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::IO::{lean_get_stderr, lean_get_stdout};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
pub static l_Lake_instReprVerbosity_repr___closed__0_value: crate::leanh::LeanStringObject<21> =
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
            76, 97, 107, 101, 46, 86, 101, 114, 98, 111, 115, 105, 116, 121, 46, 113, 117, 105,
            101, 116, 0,
        ],
    };
static mut l_Lake_instReprVerbosity_repr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprVerbosity_repr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprVerbosity_repr___closed__1_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprVerbosity_repr___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprVerbosity_repr___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprVerbosity_repr___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprVerbosity_repr___closed__2_value: crate::leanh::LeanStringObject<22> =
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
            76, 97, 107, 101, 46, 86, 101, 114, 98, 111, 115, 105, 116, 121, 46, 110, 111, 114,
            109, 97, 108, 0,
        ],
    };
static mut l_Lake_instReprVerbosity_repr___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprVerbosity_repr___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprVerbosity_repr___closed__3_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprVerbosity_repr___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprVerbosity_repr___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprVerbosity_repr___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprVerbosity_repr___closed__4_value: crate::leanh::LeanStringObject<23> =
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
            76, 97, 107, 101, 46, 86, 101, 114, 98, 111, 115, 105, 116, 121, 46, 118, 101, 114, 98,
            111, 115, 101, 0,
        ],
    };
static mut l_Lake_instReprVerbosity_repr___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprVerbosity_repr___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprVerbosity_repr___closed__5_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprVerbosity_repr___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprVerbosity_repr___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprVerbosity_repr___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_instReprVerbosity_repr___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprVerbosity_repr___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instReprVerbosity_repr___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprVerbosity_repr___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprVerbosity___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instReprVerbosity_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instReprVerbosity___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprVerbosity___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instReprVerbosity: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprVerbosity___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instOrdVerbosity___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instOrdVerbosity_ord___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instOrdVerbosity___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instOrdVerbosity___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instOrdVerbosity: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instOrdVerbosity___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instLTVerbosity: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lake_instLEVerbosity: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_instMinVerbosity___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instMinVerbosity___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instMinVerbosity___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMinVerbosity___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instMinVerbosity: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMinVerbosity___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_instMaxVerbosity___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instMaxVerbosity___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instMaxVerbosity___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMaxVerbosity___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instMaxVerbosity: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMaxVerbosity___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instInhabitedVerbosity: u8 = 0;
pub static l_Lake_instReprAnsiMode_repr___closed__0_value: crate::leanh::LeanStringObject<19> =
    crate::leanh::LeanStringObject {
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
            76, 97, 107, 101, 46, 65, 110, 115, 105, 77, 111, 100, 101, 46, 97, 117, 116, 111, 0,
        ],
    };
static mut l_Lake_instReprAnsiMode_repr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprAnsiMode_repr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprAnsiMode_repr___closed__1_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprAnsiMode_repr___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprAnsiMode_repr___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprAnsiMode_repr___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprAnsiMode_repr___closed__2_value: crate::leanh::LeanStringObject<19> =
    crate::leanh::LeanStringObject {
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
            76, 97, 107, 101, 46, 65, 110, 115, 105, 77, 111, 100, 101, 46, 97, 110, 115, 105, 0,
        ],
    };
static mut l_Lake_instReprAnsiMode_repr___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprAnsiMode_repr___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprAnsiMode_repr___closed__3_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprAnsiMode_repr___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprAnsiMode_repr___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprAnsiMode_repr___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprAnsiMode_repr___closed__4_value: crate::leanh::LeanStringObject<21> =
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
            76, 97, 107, 101, 46, 65, 110, 115, 105, 77, 111, 100, 101, 46, 110, 111, 65, 110, 115,
            105, 0,
        ],
    };
static mut l_Lake_instReprAnsiMode_repr___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprAnsiMode_repr___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprAnsiMode_repr___closed__5_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprAnsiMode_repr___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprAnsiMode_repr___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprAnsiMode_repr___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprAnsiMode___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instReprAnsiMode_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instReprAnsiMode___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprAnsiMode___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instReprAnsiMode: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprAnsiMode___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Ansi_chalk___closed__0_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [27, 91, 49, 59, 0],
    };
static mut l_Lake_Ansi_chalk___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Ansi_chalk___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Ansi_chalk___closed__1_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [109, 0],
    };
static mut l_Lake_Ansi_chalk___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Ansi_chalk___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Ansi_chalk___closed__2_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [27, 91, 109, 0],
    };
static mut l_Lake_Ansi_chalk___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Ansi_chalk___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_instCoeStreamOutStream___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instCoeStreamOutStream___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instCoeStreamOutStream___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instCoeStreamOutStream___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instCoeStreamOutStream: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instCoeStreamOutStream___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instCoeHandleOutStream___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instCoeHandleOutStream___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instCoeHandleOutStream___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instCoeHandleOutStream___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instCoeHandleOutStream: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instCoeHandleOutStream___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instInhabitedLogLevel_default: u8 = 0;
pub static mut l_Lake_instInhabitedLogLevel: u8 = 0;
pub static l_Lake_instReprLogLevel_repr___closed__0_value: crate::leanh::LeanStringObject<20> =
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
            76, 97, 107, 101, 46, 76, 111, 103, 76, 101, 118, 101, 108, 46, 116, 114, 97, 99, 101,
            0,
        ],
    };
static mut l_Lake_instReprLogLevel_repr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLogLevel_repr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprLogLevel_repr___closed__1_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprLogLevel_repr___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprLogLevel_repr___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLogLevel_repr___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprLogLevel_repr___closed__2_value: crate::leanh::LeanStringObject<19> =
    crate::leanh::LeanStringObject {
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
            76, 97, 107, 101, 46, 76, 111, 103, 76, 101, 118, 101, 108, 46, 105, 110, 102, 111, 0,
        ],
    };
static mut l_Lake_instReprLogLevel_repr___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLogLevel_repr___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprLogLevel_repr___closed__3_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprLogLevel_repr___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprLogLevel_repr___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLogLevel_repr___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprLogLevel_repr___closed__4_value: crate::leanh::LeanStringObject<22> =
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
            76, 97, 107, 101, 46, 76, 111, 103, 76, 101, 118, 101, 108, 46, 119, 97, 114, 110, 105,
            110, 103, 0,
        ],
    };
static mut l_Lake_instReprLogLevel_repr___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLogLevel_repr___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprLogLevel_repr___closed__5_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprLogLevel_repr___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprLogLevel_repr___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLogLevel_repr___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprLogLevel_repr___closed__6_value: crate::leanh::LeanStringObject<20> =
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
            76, 97, 107, 101, 46, 76, 111, 103, 76, 101, 118, 101, 108, 46, 101, 114, 114, 111,
            114, 0,
        ],
    };
static mut l_Lake_instReprLogLevel_repr___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLogLevel_repr___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprLogLevel_repr___closed__7_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprLogLevel_repr___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprLogLevel_repr___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLogLevel_repr___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprLogLevel___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instReprLogLevel_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instReprLogLevel___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLogLevel___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instReprLogLevel: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLogLevel___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_instOrdLogLevel___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instOrdLogLevel_ord___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instOrdLogLevel___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instOrdLogLevel___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instOrdLogLevel: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instOrdLogLevel___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_instToJsonLogLevel_toJson___closed__0_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [116, 114, 97, 99, 101, 0],
    };
static mut l_Lake_instToJsonLogLevel_toJson___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToJsonLogLevel_toJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instToJsonLogLevel_toJson___closed__1_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instToJsonLogLevel_toJson___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instToJsonLogLevel_toJson___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToJsonLogLevel_toJson___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instToJsonLogLevel_toJson___closed__2_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [105, 110, 102, 111, 0],
    };
static mut l_Lake_instToJsonLogLevel_toJson___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToJsonLogLevel_toJson___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instToJsonLogLevel_toJson___closed__3_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instToJsonLogLevel_toJson___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instToJsonLogLevel_toJson___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToJsonLogLevel_toJson___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instToJsonLogLevel_toJson___closed__4_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [119, 97, 114, 110, 105, 110, 103, 0],
    };
static mut l_Lake_instToJsonLogLevel_toJson___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToJsonLogLevel_toJson___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instToJsonLogLevel_toJson___closed__5_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instToJsonLogLevel_toJson___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instToJsonLogLevel_toJson___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToJsonLogLevel_toJson___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instToJsonLogLevel_toJson___closed__6_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [101, 114, 114, 111, 114, 0],
    };
static mut l_Lake_instToJsonLogLevel_toJson___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToJsonLogLevel_toJson___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instToJsonLogLevel_toJson___closed__7_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instToJsonLogLevel_toJson___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instToJsonLogLevel_toJson___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToJsonLogLevel_toJson___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instToJsonLogLevel___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instToJsonLogLevel_toJson___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instToJsonLogLevel___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToJsonLogLevel___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instToJsonLogLevel: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToJsonLogLevel___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instFromJsonLogLevel_fromJson___closed__0_value: crate::leanh::LeanStringObject<
    23,
> = crate::leanh::LeanStringObject {
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
        110, 111, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 116, 97, 103, 32, 102, 111,
        117, 110, 100, 0,
    ],
};
static mut l_Lake_instFromJsonLogLevel_fromJson___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instFromJsonLogLevel_fromJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instFromJsonLogLevel_fromJson___closed__1_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instFromJsonLogLevel_fromJson___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instFromJsonLogLevel_fromJson___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instFromJsonLogLevel_fromJson___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instFromJsonLogLevel_fromJson___closed__2_value: crate::leanh::LeanStringObject<
    33,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 33,
    m_capacity: 33,
    m_length: 32,
    m_data: [
        110, 111, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 99, 111, 110, 115, 116, 114,
        117, 99, 116, 111, 114, 32, 109, 97, 116, 99, 104, 101, 100, 0,
    ],
};
static mut l_Lake_instFromJsonLogLevel_fromJson___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instFromJsonLogLevel_fromJson___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instFromJsonLogLevel_fromJson___closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instFromJsonLogLevel_fromJson___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instFromJsonLogLevel_fromJson___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instFromJsonLogLevel_fromJson___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instFromJsonLogLevel_fromJson___closed__4_value: crate::leanh::LeanCtorObject<1> =
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
static mut l_Lake_instFromJsonLogLevel_fromJson___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instFromJsonLogLevel_fromJson___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instFromJsonLogLevel_fromJson___closed__5_value: crate::leanh::LeanCtorObject<1> =
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
static mut l_Lake_instFromJsonLogLevel_fromJson___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instFromJsonLogLevel_fromJson___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instFromJsonLogLevel_fromJson___closed__6_value: crate::leanh::LeanCtorObject<1> =
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
static mut l_Lake_instFromJsonLogLevel_fromJson___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instFromJsonLogLevel_fromJson___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instFromJsonLogLevel_fromJson___closed__7_value: crate::leanh::LeanCtorObject<1> =
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
static mut l_Lake_instFromJsonLogLevel_fromJson___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instFromJsonLogLevel_fromJson___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instFromJsonLogLevel___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instFromJsonLogLevel_fromJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instFromJsonLogLevel___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instFromJsonLogLevel___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instFromJsonLogLevel: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instFromJsonLogLevel___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instLTLogLevel: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lake_instLELogLevel: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_instMinLogLevel___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instMinLogLevel___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instMinLogLevel___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMinLogLevel___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instMinLogLevel: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMinLogLevel___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_instMaxLogLevel___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instMaxLogLevel___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instMaxLogLevel___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMaxLogLevel___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instMaxLogLevel: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMaxLogLevel___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_LogLevel_ansiColor___closed__0_value: crate::leanh::LeanStringObject<3> =
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
        m_data: [51, 51, 0],
    };
static mut l_Lake_LogLevel_ansiColor___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LogLevel_ansiColor___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LogLevel_ansiColor___closed__1_value: crate::leanh::LeanStringObject<3> =
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
        m_data: [51, 49, 0],
    };
static mut l_Lake_LogLevel_ansiColor___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LogLevel_ansiColor___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LogLevel_ansiColor___closed__2_value: crate::leanh::LeanStringObject<3> =
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
        m_data: [51, 52, 0],
    };
static mut l_Lake_LogLevel_ansiColor___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LogLevel_ansiColor___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LogLevel_ofString_x3f___closed__0_value: crate::leanh::LeanCtorObject<1> =
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
static mut l_Lake_LogLevel_ofString_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LogLevel_ofString_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LogLevel_ofString_x3f___closed__1_value: crate::leanh::LeanCtorObject<1> =
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
static mut l_Lake_LogLevel_ofString_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LogLevel_ofString_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LogLevel_ofString_x3f___closed__2_value: crate::leanh::LeanStringObject<12> =
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
        m_data: [105, 110, 102, 111, 114, 109, 97, 116, 105, 111, 110, 0],
    };
static mut l_Lake_LogLevel_ofString_x3f___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LogLevel_ofString_x3f___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LogLevel_ofString_x3f___closed__3_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [119, 97, 114, 110, 0],
    };
static mut l_Lake_LogLevel_ofString_x3f___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LogLevel_ofString_x3f___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LogLevel_ofString_x3f___closed__4_value: crate::leanh::LeanCtorObject<1> =
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
static mut l_Lake_LogLevel_ofString_x3f___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LogLevel_ofString_x3f___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LogLevel_ofString_x3f___closed__5_value: crate::leanh::LeanCtorObject<1> =
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
static mut l_Lake_LogLevel_ofString_x3f___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LogLevel_ofString_x3f___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Util_Log_0__Lake_instToStringLogLevel___closed__0_value:
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
    m_fun: l_Lake_LogLevel_toString___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lake_Util_Log_0__Lake_instToStringLogLevel___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Util_Log_0__Lake_instToStringLogLevel___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l___private_Lake_Util_Log_0__Lake_instToStringLogLevel:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Util_Log_0__Lake_instToStringLogLevel___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instInhabitedLogEntry_default___closed__0_value: crate::leanh::LeanStringObject<
    1,
> = crate::leanh::LeanStringObject {
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
static mut l_Lake_instInhabitedLogEntry_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedLogEntry_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instInhabitedLogEntry_default___closed__1_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_instInhabitedLogEntry_default___closed__0_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instInhabitedLogEntry_default___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedLogEntry_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instInhabitedLogEntry_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedLogEntry_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instInhabitedLogEntry: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedLogEntry_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instToJsonLogEntry_toJson___closed__0_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [108, 101, 118, 101, 108, 0],
    };
static mut l_Lake_instToJsonLogEntry_toJson___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToJsonLogEntry_toJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instToJsonLogEntry_toJson___closed__1_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [109, 101, 115, 115, 97, 103, 101, 0],
    };
static mut l_Lake_instToJsonLogEntry_toJson___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToJsonLogEntry_toJson___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instToJsonLogEntry_toJson___closed__2_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Lake_instToJsonLogEntry_toJson___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToJsonLogEntry_toJson___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instToJsonLogEntry___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instToJsonLogEntry_toJson___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instToJsonLogEntry___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToJsonLogEntry___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instToJsonLogEntry: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToJsonLogEntry___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instFromJsonLogEntry_fromJson___closed__0_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [76, 97, 107, 101, 0],
};
static mut l_Lake_instFromJsonLogEntry_fromJson___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instFromJsonLogEntry_fromJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instFromJsonLogEntry_fromJson___closed__1_value: crate::leanh::LeanStringObject<
    9,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [76, 111, 103, 69, 110, 116, 114, 121, 0],
};
static mut l_Lake_instFromJsonLogEntry_fromJson___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instFromJsonLogEntry_fromJson___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_instFromJsonLogEntry_fromJson___closed__2_value_aux_0: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_instFromJsonLogEntry_fromJson___closed__0_value)
            as *mut crate::leanh::LeanObject,
        13012506173997729135 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lake_instFromJsonLogEntry_fromJson___closed__2_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instFromJsonLogEntry_fromJson___closed__2_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_instFromJsonLogEntry_fromJson___closed__1_value)
                as *mut crate::leanh::LeanObject,
            4218417399028539424 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instFromJsonLogEntry_fromJson___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instFromJsonLogEntry_fromJson___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_instFromJsonLogEntry_fromJson___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instFromJsonLogEntry_fromJson___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instFromJsonLogEntry_fromJson___closed__4_value: crate::leanh::LeanStringObject<
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
    m_data: [46, 0],
};
static mut l_Lake_instFromJsonLogEntry_fromJson___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instFromJsonLogEntry_fromJson___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_instFromJsonLogEntry_fromJson___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instFromJsonLogEntry_fromJson___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instFromJsonLogEntry_fromJson___closed__6_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_instToJsonLogEntry_toJson___closed__0_value)
                as *mut crate::leanh::LeanObject,
            18250387975948097528 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instFromJsonLogEntry_fromJson___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instFromJsonLogEntry_fromJson___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_instFromJsonLogEntry_fromJson___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instFromJsonLogEntry_fromJson___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instFromJsonLogEntry_fromJson___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instFromJsonLogEntry_fromJson___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instFromJsonLogEntry_fromJson___closed__9_value: crate::leanh::LeanStringObject<
    3,
> = crate::leanh::LeanStringObject {
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
static mut l_Lake_instFromJsonLogEntry_fromJson___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instFromJsonLogEntry_fromJson___closed__9_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_instFromJsonLogEntry_fromJson___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instFromJsonLogEntry_fromJson___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instFromJsonLogEntry_fromJson___closed__11_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_instToJsonLogEntry_toJson___closed__1_value)
            as *mut crate::leanh::LeanObject,
        982637797389909653 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_instFromJsonLogEntry_fromJson___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instFromJsonLogEntry_fromJson___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_instFromJsonLogEntry_fromJson___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instFromJsonLogEntry_fromJson___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instFromJsonLogEntry_fromJson___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instFromJsonLogEntry_fromJson___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instFromJsonLogEntry_fromJson___closed__14_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instFromJsonLogEntry_fromJson___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instFromJsonLogEntry___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instFromJsonLogEntry_fromJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instFromJsonLogEntry___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instFromJsonLogEntry___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instFromJsonLogEntry: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instFromJsonLogEntry___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LogEntry_toString___closed__0_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [58, 0],
    };
static mut l_Lake_LogEntry_toString___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LogEntry_toString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LogEntry_toString___closed__1_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [32, 0],
    };
static mut l_Lake_LogEntry_toString___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LogEntry_toString___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instToStringLogEntry___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instToStringLogEntry___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instToStringLogEntry___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToStringLogEntry___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instToStringLogEntry: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToStringLogEntry___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LogEntry_ofSerialMessage___closed__0_value: crate::leanh::LeanStringObject<3> =
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
        m_data: [58, 10, 0],
    };
static mut l_Lake_LogEntry_ofSerialMessage___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LogEntry_ofSerialMessage___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instInhabitedLog_default___closed__0_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Lake_instInhabitedLog_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedLog_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instInhabitedLog_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedLog_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instInhabitedLog: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedLog_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instToJsonLog___closed__0_value: crate::leanh::LeanClosureObject<1> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_instToJsonLog___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lake_instToJsonLogEntry___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instToJsonLog___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToJsonLog___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instToJsonLog: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToJsonLog___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_instFromJsonLog___closed__0_value: crate::leanh::LeanClosureObject<1> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_instFromJsonLog___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lake_instFromJsonLogEntry___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instFromJsonLog___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instFromJsonLog___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instFromJsonLog: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instFromJsonLog___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Log_instInhabitedPos_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_Log_instInhabitedPos: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lake_instOfNatPos: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_instOrdPos___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instOrdPos___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instOrdPos___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instOrdPos___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instOrdPos: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instOrdPos___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instLTPos: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lake_instLEPos: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_instMinPos___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instMinPos___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instMinPos___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMinPos___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instMinPos: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMinPos___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_instMaxPos___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instMaxPos___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instMaxPos___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMaxPos___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instMaxPos: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMaxPos___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Log_empty___closed__0_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Lake_Log_empty___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Log_empty___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Log_empty: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Log_empty___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Log_instEmptyCollection: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Log_empty___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Log_instAppend___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_Log_append___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Log_instAppend___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Log_instAppend___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Log_instAppend: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Log_instAppend___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_toString_spec__0___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [10, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_toString_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_toString_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Log_instToString___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_Log_toString___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Log_instToString___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Log_instToString___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Log_instToString: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Log_instToString___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Log_filter___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Lake_Log_filter___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Log_filter___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Log_filter___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Lake_Log_filter___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Log_filter___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Log_filter___closed__2_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Lake_Log_filter___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Log_filter___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Log_filter___closed__3_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Lake_Log_filter___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Log_filter___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Log_filter___closed__4_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Lake_Log_filter___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Log_filter___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Log_filter___closed__5_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Lake_Log_filter___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Log_filter___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Log_filter___closed__6_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Lake_Log_filter___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Log_filter___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Log_filter___closed__7_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_Log_filter___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Log_filter___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Log_filter___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Log_filter___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Log_filter___closed__8_value: crate::leanh::LeanCtorObject<5> =
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
            core::ptr::addr_of!(l_Lake_Log_filter___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Log_filter___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Log_filter___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Log_filter___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Log_filter___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Log_filter___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Log_filter___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Log_filter___closed__9_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_Log_filter___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Log_filter___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Log_filter___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Log_filter___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_getLogPos___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_getLogPos___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_getLogPos___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getLogPos___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_takeLog___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_takeLog___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_takeLog___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_takeLog___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_withLoggedIO___redArg___lam__3___closed__0_value: crate::leanh::LeanStringObject<
    16,
> = crate::leanh::LeanStringObject {
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
        115, 116, 100, 111, 117, 116, 47, 115, 116, 100, 101, 114, 114, 58, 10, 0,
    ],
};
static mut l_Lake_withLoggedIO___redArg___lam__3___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_withLoggedIO___redArg___lam__3___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_withLoggedIO___redArg___lam__3___closed__1_value: crate::leanh::LeanStringObject<
    23,
> = crate::leanh::LeanStringObject {
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
        73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 83, 116, 114, 105, 110, 103, 46, 66, 97, 115,
        105, 99, 0,
    ],
};
static mut l_Lake_withLoggedIO___redArg___lam__3___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_withLoggedIO___redArg___lam__3___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_withLoggedIO___redArg___lam__3___closed__2_value: crate::leanh::LeanStringObject<
    17,
> = crate::leanh::LeanStringObject {
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
static mut l_Lake_withLoggedIO___redArg___lam__3___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_withLoggedIO___redArg___lam__3___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_withLoggedIO___redArg___lam__3___closed__3_value: crate::leanh::LeanStringObject<
    21,
> = crate::leanh::LeanStringObject {
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
        105, 110, 118, 97, 108, 105, 100, 32, 85, 84, 70, 45, 56, 32, 115, 116, 114, 105, 110, 103,
        0,
    ],
};
static mut l_Lake_withLoggedIO___redArg___lam__3___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_withLoggedIO___redArg___lam__3___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_withLoggedIO___redArg___lam__3___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_withLoggedIO___redArg___lam__3___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_withLoggedIO___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_withLoggedIO___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_withLoggedIO___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_withLoggedIO___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_withLoggedIO___redArg___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_withLoggedIO___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_withLoggedIO___redArg___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_withLoggedIO___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_LogT_run_x27___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_LogT_run_x27___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LogT_run_x27___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LogT_run_x27___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instMonadErrorELogTOfMonad___redArg___closed__0_value:
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
    m_fun: l_Lake_instMonadErrorELogTOfMonad___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instMonadErrorELogTOfMonad___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadErrorELogTOfMonad___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_ELogT_run_x27___redArg___closed__0_value: crate::leanh::LeanClosureObject<3> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_EResult_toExcept___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 3,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_ELogT_run_x27___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ELogT_run_x27___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_ELogT_toLogT___redArg___closed__0_value: crate::leanh::LeanClosureObject<3> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_EResult_toProd as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 3,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_ELogT_toLogT___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ELogT_toLogT___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_ELogT_toLogT_x3f___redArg___closed__0_value: crate::leanh::LeanClosureObject<3> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_EResult_toProd_x3f as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 3,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_ELogT_toLogT_x3f___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ELogT_toLogT_x3f___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_ELogT_run_x3f_x27___redArg___closed__0_value: crate::leanh::LeanClosureObject<3> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_EResult_result_x3f___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 3,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_ELogT_run_x3f_x27___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ELogT_run_x3f_x27___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LogIO_instMonadLiftIO___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_LogIO_instMonadLiftIO___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LogIO_instMonadLiftIO___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LogIO_instMonadLiftIO___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_LogIO_instMonadLiftIO: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LogIO_instMonadLiftIO___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LoggerIO_instMonadError___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_LoggerIO_instMonadError___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LoggerIO_instMonadError___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LoggerIO_instMonadError___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_LoggerIO_instMonadError: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LoggerIO_instMonadError___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LoggerIO_instMonadLiftIO___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_LoggerIO_instMonadLiftIO___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LoggerIO_instMonadLiftIO___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LoggerIO_instMonadLiftIO___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_LoggerIO_instMonadLiftIO: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LoggerIO_instMonadLiftIO___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LoggerIO_instMonadLiftLogIO___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_LoggerIO_instMonadLiftLogIO___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LoggerIO_instMonadLiftLogIO___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LoggerIO_instMonadLiftLogIO___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_LoggerIO_instMonadLiftLogIO___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LoggerIO_instMonadLiftLogIO___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_LoggerIO_instMonadLiftLogIO___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LoggerIO_instMonadLiftLogIO___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_LoggerIO_instMonadLiftLogIO___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LoggerIO_instMonadLiftLogIO___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_LoggerIO_instMonadLiftLogIO: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lake_Verbosity_ctorIdx(mut v_x_4042_: u8) -> *mut crate::leanh::LeanObject {
    match v_x_4042_ {
        0 => {
            let mut v___x_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4043_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_4043_;
        }
        1 => {
            let mut v___x_4044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4044_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_4044_;
        }
        _ => {
            let mut v___x_4045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4045_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_4045_;
        }
    }
}
pub unsafe fn l_Lake_Verbosity_ctorIdx___boxed(
    mut v_x_4046_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_4047_: u8 = 0;
    let mut v_res_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_4047_ = (crate::leanh::lean_unbox(v_x_4046_) as u8);
    v_res_4048_ = l_Lake_Verbosity_ctorIdx(v_x_boxed_4047_);
    return v_res_4048_;
}
pub unsafe fn l_Lake_Verbosity_toCtorIdx(mut v_x_4049_: u8) -> *mut crate::leanh::LeanObject {
    let mut v___x_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4050_ = l_Lake_Verbosity_ctorIdx(v_x_4049_);
    return v___x_4050_;
}
pub unsafe fn l_Lake_Verbosity_toCtorIdx___boxed(
    mut v_x_4051_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4__boxed_4052_: u8 = 0;
    let mut v_res_4053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_4052_ = (crate::leanh::lean_unbox(v_x_4051_) as u8);
    v_res_4053_ = l_Lake_Verbosity_toCtorIdx(v_x_4__boxed_4052_);
    return v_res_4053_;
}
pub unsafe fn l_Lake_Verbosity_ctorElim___redArg(
    mut v_k_4054_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_4054_);
    return v_k_4054_;
}
pub unsafe fn l_Lake_Verbosity_ctorElim___redArg___boxed(
    mut v_k_4055_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4056_ = l_Lake_Verbosity_ctorElim___redArg(v_k_4055_);
    crate::leanh::lean_dec(v_k_4055_);
    return v_res_4056_;
}
pub unsafe fn l_Lake_Verbosity_ctorElim(
    mut v_motive_4057_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_4058_: *mut crate::leanh::LeanObject,
    mut v_t_4059_: u8,
    mut v_h_4060_: *mut crate::leanh::LeanObject,
    mut v_k_4061_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_4061_);
    return v_k_4061_;
}
pub unsafe fn l_Lake_Verbosity_ctorElim___boxed(
    mut v_motive_4062_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_4063_: *mut crate::leanh::LeanObject,
    mut v_t_4064_: *mut crate::leanh::LeanObject,
    mut v_h_4065_: *mut crate::leanh::LeanObject,
    mut v_k_4066_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_4067_: u8 = 0;
    let mut v_res_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_4067_ = (crate::leanh::lean_unbox(v_t_4064_) as u8);
    v_res_4068_ = l_Lake_Verbosity_ctorElim(
        v_motive_4062_,
        v_ctorIdx_4063_,
        v_t_boxed_4067_,
        v_h_4065_,
        v_k_4066_,
    );
    crate::leanh::lean_dec(v_k_4066_);
    crate::leanh::lean_dec(v_ctorIdx_4063_);
    return v_res_4068_;
}
pub unsafe fn l_Lake_Verbosity_quiet_elim___redArg(
    mut v_quiet_4069_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_quiet_4069_);
    return v_quiet_4069_;
}
pub unsafe fn l_Lake_Verbosity_quiet_elim___redArg___boxed(
    mut v_quiet_4070_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4071_ = l_Lake_Verbosity_quiet_elim___redArg(v_quiet_4070_);
    crate::leanh::lean_dec(v_quiet_4070_);
    return v_res_4071_;
}
pub unsafe fn l_Lake_Verbosity_quiet_elim(
    mut v_motive_4072_: *mut crate::leanh::LeanObject,
    mut v_t_4073_: u8,
    mut v_h_4074_: *mut crate::leanh::LeanObject,
    mut v_quiet_4075_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_quiet_4075_);
    return v_quiet_4075_;
}
pub unsafe fn l_Lake_Verbosity_quiet_elim___boxed(
    mut v_motive_4076_: *mut crate::leanh::LeanObject,
    mut v_t_4077_: *mut crate::leanh::LeanObject,
    mut v_h_4078_: *mut crate::leanh::LeanObject,
    mut v_quiet_4079_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_4080_: u8 = 0;
    let mut v_res_4081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_4080_ = (crate::leanh::lean_unbox(v_t_4077_) as u8);
    v_res_4081_ =
        l_Lake_Verbosity_quiet_elim(v_motive_4076_, v_t_boxed_4080_, v_h_4078_, v_quiet_4079_);
    crate::leanh::lean_dec(v_quiet_4079_);
    return v_res_4081_;
}
pub unsafe fn l_Lake_Verbosity_normal_elim___redArg(
    mut v_normal_4082_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_normal_4082_);
    return v_normal_4082_;
}
pub unsafe fn l_Lake_Verbosity_normal_elim___redArg___boxed(
    mut v_normal_4083_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4084_ = l_Lake_Verbosity_normal_elim___redArg(v_normal_4083_);
    crate::leanh::lean_dec(v_normal_4083_);
    return v_res_4084_;
}
pub unsafe fn l_Lake_Verbosity_normal_elim(
    mut v_motive_4085_: *mut crate::leanh::LeanObject,
    mut v_t_4086_: u8,
    mut v_h_4087_: *mut crate::leanh::LeanObject,
    mut v_normal_4088_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_normal_4088_);
    return v_normal_4088_;
}
pub unsafe fn l_Lake_Verbosity_normal_elim___boxed(
    mut v_motive_4089_: *mut crate::leanh::LeanObject,
    mut v_t_4090_: *mut crate::leanh::LeanObject,
    mut v_h_4091_: *mut crate::leanh::LeanObject,
    mut v_normal_4092_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_4093_: u8 = 0;
    let mut v_res_4094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_4093_ = (crate::leanh::lean_unbox(v_t_4090_) as u8);
    v_res_4094_ =
        l_Lake_Verbosity_normal_elim(v_motive_4089_, v_t_boxed_4093_, v_h_4091_, v_normal_4092_);
    crate::leanh::lean_dec(v_normal_4092_);
    return v_res_4094_;
}
pub unsafe fn l_Lake_Verbosity_verbose_elim___redArg(
    mut v_verbose_4095_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_verbose_4095_);
    return v_verbose_4095_;
}
pub unsafe fn l_Lake_Verbosity_verbose_elim___redArg___boxed(
    mut v_verbose_4096_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4097_ = l_Lake_Verbosity_verbose_elim___redArg(v_verbose_4096_);
    crate::leanh::lean_dec(v_verbose_4096_);
    return v_res_4097_;
}
pub unsafe fn l_Lake_Verbosity_verbose_elim(
    mut v_motive_4098_: *mut crate::leanh::LeanObject,
    mut v_t_4099_: u8,
    mut v_h_4100_: *mut crate::leanh::LeanObject,
    mut v_verbose_4101_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_verbose_4101_);
    return v_verbose_4101_;
}
pub unsafe fn l_Lake_Verbosity_verbose_elim___boxed(
    mut v_motive_4102_: *mut crate::leanh::LeanObject,
    mut v_t_4103_: *mut crate::leanh::LeanObject,
    mut v_h_4104_: *mut crate::leanh::LeanObject,
    mut v_verbose_4105_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_4106_: u8 = 0;
    let mut v_res_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_4106_ = (crate::leanh::lean_unbox(v_t_4103_) as u8);
    v_res_4107_ =
        l_Lake_Verbosity_verbose_elim(v_motive_4102_, v_t_boxed_4106_, v_h_4104_, v_verbose_4105_);
    crate::leanh::lean_dec(v_verbose_4105_);
    return v_res_4107_;
}
pub unsafe fn _init_l_Lake_instReprVerbosity_repr___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_4117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4117_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_4118_ = lean_nat_to_int(v___x_4117_);
    return v___x_4118_;
}
pub unsafe fn _init_l_Lake_instReprVerbosity_repr___closed__7() -> *mut crate::leanh::LeanObject {
    let mut v___x_4119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4119_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_4120_ = lean_nat_to_int(v___x_4119_);
    return v___x_4120_;
}
pub unsafe fn l_Lake_instReprVerbosity_repr(
    mut v_x_4121_: u8,
    mut v_prec_4122_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: u8 = 0;
    let mut v___x_4128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4134_: u8 = 0;
    let mut v___x_4135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4141_: u8 = 0;
    let mut v___x_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4145_: u8 = 0;
    let mut v___x_4146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: u8 = 0;
    let mut v___x_4150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4153_: u8 = 0;
    let mut v___x_4154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match v_x_4121_ {
                0 => {
                    v___x_4144_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_4145_ = lean_nat_dec_le(v___x_4144_, v_prec_4122_);
                    if v___x_4145_ == 0 {
                        v___x_4146_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprVerbosity_repr___closed__6),
                            core::ptr::addr_of_mut!(l_Lake_instReprVerbosity_repr___closed__6_once),
                            _init_l_Lake_instReprVerbosity_repr___closed__6,
                        );
                        v___y_4124_ = v___x_4146_;
                        state = 1;
                        continue;
                    } else {
                        v___x_4147_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprVerbosity_repr___closed__7),
                            core::ptr::addr_of_mut!(l_Lake_instReprVerbosity_repr___closed__7_once),
                            _init_l_Lake_instReprVerbosity_repr___closed__7,
                        );
                        v___y_4124_ = v___x_4147_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v___x_4148_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_4149_ = lean_nat_dec_le(v___x_4148_, v_prec_4122_);
                    if v___x_4149_ == 0 {
                        v___x_4150_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprVerbosity_repr___closed__6),
                            core::ptr::addr_of_mut!(l_Lake_instReprVerbosity_repr___closed__6_once),
                            _init_l_Lake_instReprVerbosity_repr___closed__6,
                        );
                        v___y_4131_ = v___x_4150_;
                        state = 2;
                        continue;
                    } else {
                        v___x_4151_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprVerbosity_repr___closed__7),
                            core::ptr::addr_of_mut!(l_Lake_instReprVerbosity_repr___closed__7_once),
                            _init_l_Lake_instReprVerbosity_repr___closed__7,
                        );
                        v___y_4131_ = v___x_4151_;
                        state = 2;
                        continue;
                    }
                }
                _ => {
                    v___x_4152_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_4153_ = lean_nat_dec_le(v___x_4152_, v_prec_4122_);
                    if v___x_4153_ == 0 {
                        v___x_4154_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprVerbosity_repr___closed__6),
                            core::ptr::addr_of_mut!(l_Lake_instReprVerbosity_repr___closed__6_once),
                            _init_l_Lake_instReprVerbosity_repr___closed__6,
                        );
                        v___y_4138_ = v___x_4154_;
                        state = 3;
                        continue;
                    } else {
                        v___x_4155_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprVerbosity_repr___closed__7),
                            core::ptr::addr_of_mut!(l_Lake_instReprVerbosity_repr___closed__7_once),
                            _init_l_Lake_instReprVerbosity_repr___closed__7,
                        );
                        v___y_4138_ = v___x_4155_;
                        state = 3;
                        continue;
                    }
                }
            },
            1 => {
                v___x_4125_ = l_Lake_instReprVerbosity_repr___closed__1;
                crate::leanh::lean_inc(v___y_4124_);
                v___x_4126_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4126_, 0, v___y_4124_);
                crate::leanh::lean_ctor_set(v___x_4126_, 1, v___x_4125_);
                v___x_4127_ = 0;
                v___x_4128_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4128_, 0, v___x_4126_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4128_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4127_,
                );
                v___x_4129_ = l_Repr_addAppParen(v___x_4128_, v_prec_4122_);
                return v___x_4129_;
            }
            2 => {
                v___x_4132_ = l_Lake_instReprVerbosity_repr___closed__3;
                crate::leanh::lean_inc(v___y_4131_);
                v___x_4133_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4133_, 0, v___y_4131_);
                crate::leanh::lean_ctor_set(v___x_4133_, 1, v___x_4132_);
                v___x_4134_ = 0;
                v___x_4135_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4135_, 0, v___x_4133_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4135_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4134_,
                );
                v___x_4136_ = l_Repr_addAppParen(v___x_4135_, v_prec_4122_);
                return v___x_4136_;
            }
            3 => {
                v___x_4139_ = l_Lake_instReprVerbosity_repr___closed__5;
                crate::leanh::lean_inc(v___y_4138_);
                v___x_4140_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4140_, 0, v___y_4138_);
                crate::leanh::lean_ctor_set(v___x_4140_, 1, v___x_4139_);
                v___x_4141_ = 0;
                v___x_4142_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4142_, 0, v___x_4140_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4142_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4141_,
                );
                v___x_4143_ = l_Repr_addAppParen(v___x_4142_, v_prec_4122_);
                return v___x_4143_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instReprVerbosity_repr___boxed(
    mut v_x_4156_: *mut crate::leanh::LeanObject,
    mut v_prec_4157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_177__boxed_4158_: u8 = 0;
    let mut v_res_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_177__boxed_4158_ = (crate::leanh::lean_unbox(v_x_4156_) as u8);
    v_res_4159_ = l_Lake_instReprVerbosity_repr(v_x_177__boxed_4158_, v_prec_4157_);
    crate::leanh::lean_dec(v_prec_4157_);
    return v_res_4159_;
}
pub unsafe fn l_Lake_Verbosity_ofNat(mut v_n_4162_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_4163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: u8 = 0;
    v___x_4163_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4164_ = lean_nat_dec_le(v_n_4162_, v___x_4163_);
    if v___x_4164_ == 0 {
        let mut v___x_4165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4166_: u8 = 0;
        v___x_4165_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_4166_ = lean_nat_dec_le(v_n_4162_, v___x_4165_);
        if v___x_4166_ == 0 {
            let mut v___x_4167_: u8 = 0;
            v___x_4167_ = 2;
            return v___x_4167_;
        } else {
            let mut v___x_4168_: u8 = 0;
            v___x_4168_ = 1;
            return v___x_4168_;
        }
    } else {
        let mut v___x_4169_: u8 = 0;
        v___x_4169_ = 0;
        return v___x_4169_;
    }
}
pub unsafe fn l_Lake_Verbosity_ofNat___boxed(
    mut v_n_4170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4171_: u8 = 0;
    let mut v_r_4172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4171_ = l_Lake_Verbosity_ofNat(v_n_4170_);
    crate::leanh::lean_dec(v_n_4170_);
    v_r_4172_ = crate::leanh::lean_box((v_res_4171_) as usize);
    return v_r_4172_;
}
pub unsafe fn l_Lake_instDecidableEqVerbosity(mut v_x_4173_: u8, mut v_y_4174_: u8) -> u8 {
    let mut v___x_4175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: u8 = 0;
    v___x_4175_ = l_Lake_Verbosity_ctorIdx(v_x_4173_);
    v___x_4176_ = l_Lake_Verbosity_ctorIdx(v_y_4174_);
    v___x_4177_ = lean_nat_dec_eq(v___x_4175_, v___x_4176_);
    crate::leanh::lean_dec(v___x_4176_);
    crate::leanh::lean_dec(v___x_4175_);
    return v___x_4177_;
}
pub unsafe fn l_Lake_instDecidableEqVerbosity___boxed(
    mut v_x_4178_: *mut crate::leanh::LeanObject,
    mut v_y_4179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_13__boxed_4180_: u8 = 0;
    let mut v_y_14__boxed_4181_: u8 = 0;
    let mut v_res_4182_: u8 = 0;
    let mut v_r_4183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_13__boxed_4180_ = (crate::leanh::lean_unbox(v_x_4178_) as u8);
    v_y_14__boxed_4181_ = (crate::leanh::lean_unbox(v_y_4179_) as u8);
    v_res_4182_ = l_Lake_instDecidableEqVerbosity(v_x_13__boxed_4180_, v_y_14__boxed_4181_);
    v_r_4183_ = crate::leanh::lean_box((v_res_4182_) as usize);
    return v_r_4183_;
}
pub unsafe fn l_Lake_instOrdVerbosity_ord(mut v_x_4184_: u8, mut v_y_4185_: u8) -> u8 {
    let mut v___x_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: u8 = 0;
    v___x_4186_ = l_Lake_Verbosity_ctorIdx(v_x_4184_);
    v___x_4187_ = l_Lake_Verbosity_ctorIdx(v_y_4185_);
    v___x_4188_ = lean_nat_dec_lt(v___x_4186_, v___x_4187_);
    if v___x_4188_ == 0 {
        let mut v___x_4189_: u8 = 0;
        v___x_4189_ = lean_nat_dec_eq(v___x_4186_, v___x_4187_);
        crate::leanh::lean_dec(v___x_4187_);
        crate::leanh::lean_dec(v___x_4186_);
        if v___x_4189_ == 0 {
            let mut v___x_4190_: u8 = 0;
            v___x_4190_ = 2;
            return v___x_4190_;
        } else {
            let mut v___x_4191_: u8 = 0;
            v___x_4191_ = 1;
            return v___x_4191_;
        }
    } else {
        let mut v___x_4192_: u8 = 0;
        crate::leanh::lean_dec(v___x_4187_);
        crate::leanh::lean_dec(v___x_4186_);
        v___x_4192_ = 0;
        return v___x_4192_;
    }
}
pub unsafe fn l_Lake_instOrdVerbosity_ord___boxed(
    mut v_x_4193_: *mut crate::leanh::LeanObject,
    mut v_y_4194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_30__boxed_4195_: u8 = 0;
    let mut v_y_31__boxed_4196_: u8 = 0;
    let mut v_res_4197_: u8 = 0;
    let mut v_r_4198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_30__boxed_4195_ = (crate::leanh::lean_unbox(v_x_4193_) as u8);
    v_y_31__boxed_4196_ = (crate::leanh::lean_unbox(v_y_4194_) as u8);
    v_res_4197_ = l_Lake_instOrdVerbosity_ord(v_x_30__boxed_4195_, v_y_31__boxed_4196_);
    v_r_4198_ = crate::leanh::lean_box((v_res_4197_) as usize);
    return v_r_4198_;
}
pub unsafe fn _init_l_Lake_instLTVerbosity() -> *mut crate::leanh::LeanObject {
    let mut v___x_4201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4201_ = crate::leanh::lean_box(0);
    return v___x_4201_;
}
pub unsafe fn _init_l_Lake_instLEVerbosity() -> *mut crate::leanh::LeanObject {
    let mut v___x_4202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4202_ = crate::leanh::lean_box(0);
    return v___x_4202_;
}
pub unsafe fn l_Lake_instMinVerbosity___lam__0(mut v_x_4203_: u8, mut v_y_4204_: u8) -> u8 {
    let mut v___x_4205_: u8 = 0;
    v___x_4205_ = l_Lake_instOrdVerbosity_ord(v_x_4203_, v_y_4204_);
    if v___x_4205_ == 2 {
        return v_y_4204_;
    } else {
        return v_x_4203_;
    }
}
pub unsafe fn l_Lake_instMinVerbosity___lam__0___boxed(
    mut v_x_4206_: *mut crate::leanh::LeanObject,
    mut v_y_4207_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_4208_: u8 = 0;
    let mut v_y_boxed_4209_: u8 = 0;
    let mut v_res_4210_: u8 = 0;
    let mut v_r_4211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_4208_ = (crate::leanh::lean_unbox(v_x_4206_) as u8);
    v_y_boxed_4209_ = (crate::leanh::lean_unbox(v_y_4207_) as u8);
    v_res_4210_ = l_Lake_instMinVerbosity___lam__0(v_x_boxed_4208_, v_y_boxed_4209_);
    v_r_4211_ = crate::leanh::lean_box((v_res_4210_) as usize);
    return v_r_4211_;
}
pub unsafe fn l_Lake_instMaxVerbosity___lam__0(mut v_x_4214_: u8, mut v_y_4215_: u8) -> u8 {
    let mut v___x_4216_: u8 = 0;
    v___x_4216_ = l_Lake_instOrdVerbosity_ord(v_x_4214_, v_y_4215_);
    if v___x_4216_ == 2 {
        return v_x_4214_;
    } else {
        return v_y_4215_;
    }
}
pub unsafe fn l_Lake_instMaxVerbosity___lam__0___boxed(
    mut v_x_4217_: *mut crate::leanh::LeanObject,
    mut v_y_4218_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_4219_: u8 = 0;
    let mut v_y_boxed_4220_: u8 = 0;
    let mut v_res_4221_: u8 = 0;
    let mut v_r_4222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_4219_ = (crate::leanh::lean_unbox(v_x_4217_) as u8);
    v_y_boxed_4220_ = (crate::leanh::lean_unbox(v_y_4218_) as u8);
    v_res_4221_ = l_Lake_instMaxVerbosity___lam__0(v_x_boxed_4219_, v_y_boxed_4220_);
    v_r_4222_ = crate::leanh::lean_box((v_res_4221_) as usize);
    return v_r_4222_;
}
pub unsafe fn _init_l_Lake_instInhabitedVerbosity() -> u8 {
    let mut v___x_4225_: u8 = 0;
    v___x_4225_ = 1;
    return v___x_4225_;
}
pub unsafe fn l_Lake_AnsiMode_ctorIdx(mut v_x_4226_: u8) -> *mut crate::leanh::LeanObject {
    match v_x_4226_ {
        0 => {
            let mut v___x_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4227_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_4227_;
        }
        1 => {
            let mut v___x_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4228_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_4228_;
        }
        _ => {
            let mut v___x_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4229_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_4229_;
        }
    }
}
pub unsafe fn l_Lake_AnsiMode_ctorIdx___boxed(
    mut v_x_4230_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_4231_: u8 = 0;
    let mut v_res_4232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_4231_ = (crate::leanh::lean_unbox(v_x_4230_) as u8);
    v_res_4232_ = l_Lake_AnsiMode_ctorIdx(v_x_boxed_4231_);
    return v_res_4232_;
}
pub unsafe fn l_Lake_AnsiMode_toCtorIdx(mut v_x_4233_: u8) -> *mut crate::leanh::LeanObject {
    let mut v___x_4234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4234_ = l_Lake_AnsiMode_ctorIdx(v_x_4233_);
    return v___x_4234_;
}
pub unsafe fn l_Lake_AnsiMode_toCtorIdx___boxed(
    mut v_x_4235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4__boxed_4236_: u8 = 0;
    let mut v_res_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_4236_ = (crate::leanh::lean_unbox(v_x_4235_) as u8);
    v_res_4237_ = l_Lake_AnsiMode_toCtorIdx(v_x_4__boxed_4236_);
    return v_res_4237_;
}
pub unsafe fn l_Lake_AnsiMode_ctorElim___redArg(
    mut v_k_4238_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_4238_);
    return v_k_4238_;
}
pub unsafe fn l_Lake_AnsiMode_ctorElim___redArg___boxed(
    mut v_k_4239_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4240_ = l_Lake_AnsiMode_ctorElim___redArg(v_k_4239_);
    crate::leanh::lean_dec(v_k_4239_);
    return v_res_4240_;
}
pub unsafe fn l_Lake_AnsiMode_ctorElim(
    mut v_motive_4241_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_4242_: *mut crate::leanh::LeanObject,
    mut v_t_4243_: u8,
    mut v_h_4244_: *mut crate::leanh::LeanObject,
    mut v_k_4245_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_4245_);
    return v_k_4245_;
}
pub unsafe fn l_Lake_AnsiMode_ctorElim___boxed(
    mut v_motive_4246_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_4247_: *mut crate::leanh::LeanObject,
    mut v_t_4248_: *mut crate::leanh::LeanObject,
    mut v_h_4249_: *mut crate::leanh::LeanObject,
    mut v_k_4250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_4251_: u8 = 0;
    let mut v_res_4252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_4251_ = (crate::leanh::lean_unbox(v_t_4248_) as u8);
    v_res_4252_ = l_Lake_AnsiMode_ctorElim(
        v_motive_4246_,
        v_ctorIdx_4247_,
        v_t_boxed_4251_,
        v_h_4249_,
        v_k_4250_,
    );
    crate::leanh::lean_dec(v_k_4250_);
    crate::leanh::lean_dec(v_ctorIdx_4247_);
    return v_res_4252_;
}
pub unsafe fn l_Lake_AnsiMode_auto_elim___redArg(
    mut v_auto_4253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_auto_4253_);
    return v_auto_4253_;
}
pub unsafe fn l_Lake_AnsiMode_auto_elim___redArg___boxed(
    mut v_auto_4254_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4255_ = l_Lake_AnsiMode_auto_elim___redArg(v_auto_4254_);
    crate::leanh::lean_dec(v_auto_4254_);
    return v_res_4255_;
}
pub unsafe fn l_Lake_AnsiMode_auto_elim(
    mut v_motive_4256_: *mut crate::leanh::LeanObject,
    mut v_t_4257_: u8,
    mut v_h_4258_: *mut crate::leanh::LeanObject,
    mut v_auto_4259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_auto_4259_);
    return v_auto_4259_;
}
pub unsafe fn l_Lake_AnsiMode_auto_elim___boxed(
    mut v_motive_4260_: *mut crate::leanh::LeanObject,
    mut v_t_4261_: *mut crate::leanh::LeanObject,
    mut v_h_4262_: *mut crate::leanh::LeanObject,
    mut v_auto_4263_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_4264_: u8 = 0;
    let mut v_res_4265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_4264_ = (crate::leanh::lean_unbox(v_t_4261_) as u8);
    v_res_4265_ =
        l_Lake_AnsiMode_auto_elim(v_motive_4260_, v_t_boxed_4264_, v_h_4262_, v_auto_4263_);
    crate::leanh::lean_dec(v_auto_4263_);
    return v_res_4265_;
}
pub unsafe fn l_Lake_AnsiMode_ansi_elim___redArg(
    mut v_ansi_4266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_ansi_4266_);
    return v_ansi_4266_;
}
pub unsafe fn l_Lake_AnsiMode_ansi_elim___redArg___boxed(
    mut v_ansi_4267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4268_ = l_Lake_AnsiMode_ansi_elim___redArg(v_ansi_4267_);
    crate::leanh::lean_dec(v_ansi_4267_);
    return v_res_4268_;
}
pub unsafe fn l_Lake_AnsiMode_ansi_elim(
    mut v_motive_4269_: *mut crate::leanh::LeanObject,
    mut v_t_4270_: u8,
    mut v_h_4271_: *mut crate::leanh::LeanObject,
    mut v_ansi_4272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_ansi_4272_);
    return v_ansi_4272_;
}
pub unsafe fn l_Lake_AnsiMode_ansi_elim___boxed(
    mut v_motive_4273_: *mut crate::leanh::LeanObject,
    mut v_t_4274_: *mut crate::leanh::LeanObject,
    mut v_h_4275_: *mut crate::leanh::LeanObject,
    mut v_ansi_4276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_4277_: u8 = 0;
    let mut v_res_4278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_4277_ = (crate::leanh::lean_unbox(v_t_4274_) as u8);
    v_res_4278_ =
        l_Lake_AnsiMode_ansi_elim(v_motive_4273_, v_t_boxed_4277_, v_h_4275_, v_ansi_4276_);
    crate::leanh::lean_dec(v_ansi_4276_);
    return v_res_4278_;
}
pub unsafe fn l_Lake_AnsiMode_noAnsi_elim___redArg(
    mut v_noAnsi_4279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_noAnsi_4279_);
    return v_noAnsi_4279_;
}
pub unsafe fn l_Lake_AnsiMode_noAnsi_elim___redArg___boxed(
    mut v_noAnsi_4280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4281_ = l_Lake_AnsiMode_noAnsi_elim___redArg(v_noAnsi_4280_);
    crate::leanh::lean_dec(v_noAnsi_4280_);
    return v_res_4281_;
}
pub unsafe fn l_Lake_AnsiMode_noAnsi_elim(
    mut v_motive_4282_: *mut crate::leanh::LeanObject,
    mut v_t_4283_: u8,
    mut v_h_4284_: *mut crate::leanh::LeanObject,
    mut v_noAnsi_4285_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_noAnsi_4285_);
    return v_noAnsi_4285_;
}
pub unsafe fn l_Lake_AnsiMode_noAnsi_elim___boxed(
    mut v_motive_4286_: *mut crate::leanh::LeanObject,
    mut v_t_4287_: *mut crate::leanh::LeanObject,
    mut v_h_4288_: *mut crate::leanh::LeanObject,
    mut v_noAnsi_4289_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_4290_: u8 = 0;
    let mut v_res_4291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_4290_ = (crate::leanh::lean_unbox(v_t_4287_) as u8);
    v_res_4291_ =
        l_Lake_AnsiMode_noAnsi_elim(v_motive_4286_, v_t_boxed_4290_, v_h_4288_, v_noAnsi_4289_);
    crate::leanh::lean_dec(v_noAnsi_4289_);
    return v_res_4291_;
}
pub unsafe fn l_Lake_instReprAnsiMode_repr(
    mut v_x_4301_: u8,
    mut v_prec_4302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4307_: u8 = 0;
    let mut v___x_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4314_: u8 = 0;
    let mut v___x_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: u8 = 0;
    let mut v___x_4322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4325_: u8 = 0;
    let mut v___x_4326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: u8 = 0;
    let mut v___x_4330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: u8 = 0;
    let mut v___x_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match v_x_4301_ {
                0 => {
                    v___x_4324_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_4325_ = lean_nat_dec_le(v___x_4324_, v_prec_4302_);
                    if v___x_4325_ == 0 {
                        v___x_4326_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprVerbosity_repr___closed__6),
                            core::ptr::addr_of_mut!(l_Lake_instReprVerbosity_repr___closed__6_once),
                            _init_l_Lake_instReprVerbosity_repr___closed__6,
                        );
                        v___y_4304_ = v___x_4326_;
                        state = 1;
                        continue;
                    } else {
                        v___x_4327_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprVerbosity_repr___closed__7),
                            core::ptr::addr_of_mut!(l_Lake_instReprVerbosity_repr___closed__7_once),
                            _init_l_Lake_instReprVerbosity_repr___closed__7,
                        );
                        v___y_4304_ = v___x_4327_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v___x_4328_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_4329_ = lean_nat_dec_le(v___x_4328_, v_prec_4302_);
                    if v___x_4329_ == 0 {
                        v___x_4330_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprVerbosity_repr___closed__6),
                            core::ptr::addr_of_mut!(l_Lake_instReprVerbosity_repr___closed__6_once),
                            _init_l_Lake_instReprVerbosity_repr___closed__6,
                        );
                        v___y_4311_ = v___x_4330_;
                        state = 2;
                        continue;
                    } else {
                        v___x_4331_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprVerbosity_repr___closed__7),
                            core::ptr::addr_of_mut!(l_Lake_instReprVerbosity_repr___closed__7_once),
                            _init_l_Lake_instReprVerbosity_repr___closed__7,
                        );
                        v___y_4311_ = v___x_4331_;
                        state = 2;
                        continue;
                    }
                }
                _ => {
                    v___x_4332_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_4333_ = lean_nat_dec_le(v___x_4332_, v_prec_4302_);
                    if v___x_4333_ == 0 {
                        v___x_4334_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprVerbosity_repr___closed__6),
                            core::ptr::addr_of_mut!(l_Lake_instReprVerbosity_repr___closed__6_once),
                            _init_l_Lake_instReprVerbosity_repr___closed__6,
                        );
                        v___y_4318_ = v___x_4334_;
                        state = 3;
                        continue;
                    } else {
                        v___x_4335_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprVerbosity_repr___closed__7),
                            core::ptr::addr_of_mut!(l_Lake_instReprVerbosity_repr___closed__7_once),
                            _init_l_Lake_instReprVerbosity_repr___closed__7,
                        );
                        v___y_4318_ = v___x_4335_;
                        state = 3;
                        continue;
                    }
                }
            },
            1 => {
                v___x_4305_ = l_Lake_instReprAnsiMode_repr___closed__1;
                crate::leanh::lean_inc(v___y_4304_);
                v___x_4306_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4306_, 0, v___y_4304_);
                crate::leanh::lean_ctor_set(v___x_4306_, 1, v___x_4305_);
                v___x_4307_ = 0;
                v___x_4308_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4308_, 0, v___x_4306_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4308_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4307_,
                );
                v___x_4309_ = l_Repr_addAppParen(v___x_4308_, v_prec_4302_);
                return v___x_4309_;
            }
            2 => {
                v___x_4312_ = l_Lake_instReprAnsiMode_repr___closed__3;
                crate::leanh::lean_inc(v___y_4311_);
                v___x_4313_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4313_, 0, v___y_4311_);
                crate::leanh::lean_ctor_set(v___x_4313_, 1, v___x_4312_);
                v___x_4314_ = 0;
                v___x_4315_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4315_, 0, v___x_4313_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4315_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4314_,
                );
                v___x_4316_ = l_Repr_addAppParen(v___x_4315_, v_prec_4302_);
                return v___x_4316_;
            }
            3 => {
                v___x_4319_ = l_Lake_instReprAnsiMode_repr___closed__5;
                crate::leanh::lean_inc(v___y_4318_);
                v___x_4320_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4320_, 0, v___y_4318_);
                crate::leanh::lean_ctor_set(v___x_4320_, 1, v___x_4319_);
                v___x_4321_ = 0;
                v___x_4322_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4322_, 0, v___x_4320_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4322_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4321_,
                );
                v___x_4323_ = l_Repr_addAppParen(v___x_4322_, v_prec_4302_);
                return v___x_4323_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instReprAnsiMode_repr___boxed(
    mut v_x_4336_: *mut crate::leanh::LeanObject,
    mut v_prec_4337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_173__boxed_4338_: u8 = 0;
    let mut v_res_4339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_173__boxed_4338_ = (crate::leanh::lean_unbox(v_x_4336_) as u8);
    v_res_4339_ = l_Lake_instReprAnsiMode_repr(v_x_173__boxed_4338_, v_prec_4337_);
    crate::leanh::lean_dec(v_prec_4337_);
    return v_res_4339_;
}
pub unsafe fn l_Lake_AnsiMode_isEnabled(
    mut v_out_4342_: *mut crate::leanh::LeanObject,
    mut v_x_4343_: u8,
) -> u8 {
    match v_x_4343_ {
        0 => {
            let mut v_isTty_4345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4347_: u8 = 0;
            v_isTty_4345_ = crate::leanh::lean_ctor_get(v_out_4342_, 5);
            crate::leanh::lean_inc_ref(v_isTty_4345_);
            crate::leanh::lean_dec_ref(v_out_4342_);
            v___x_4346_ = crate::leanh::lean_apply_1(v_isTty_4345_, crate::leanh::lean_box(0));
            v___x_4347_ = (crate::leanh::lean_unbox(v___x_4346_) as u8);
            return v___x_4347_;
        }
        1 => {
            let mut v___x_4348_: u8 = 0;
            crate::leanh::lean_dec_ref(v_out_4342_);
            v___x_4348_ = 1;
            return v___x_4348_;
        }
        _ => {
            let mut v___x_4349_: u8 = 0;
            crate::leanh::lean_dec_ref(v_out_4342_);
            v___x_4349_ = 0;
            return v___x_4349_;
        }
    }
}
pub unsafe fn l_Lake_AnsiMode_isEnabled___boxed(
    mut v_out_4350_: *mut crate::leanh::LeanObject,
    mut v_x_4351_: *mut crate::leanh::LeanObject,
    mut v_a_4352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_146__boxed_4353_: u8 = 0;
    let mut v_res_4354_: u8 = 0;
    let mut v_r_4355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_146__boxed_4353_ = (crate::leanh::lean_unbox(v_x_4351_) as u8);
    v_res_4354_ = l_Lake_AnsiMode_isEnabled(v_out_4350_, v_x_146__boxed_4353_);
    v_r_4355_ = crate::leanh::lean_box((v_res_4354_) as usize);
    return v_r_4355_;
}
pub unsafe fn l_Lake_Ansi_chalk(
    mut v_colorCode_4359_: *mut crate::leanh::LeanObject,
    mut v_text_4360_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4361_ = l_Lake_Ansi_chalk___closed__0;
    v___x_4362_ = lean_string_append(v___x_4361_, v_colorCode_4359_);
    v___x_4363_ = l_Lake_Ansi_chalk___closed__1;
    v___x_4364_ = lean_string_append(v___x_4362_, v___x_4363_);
    v___x_4365_ = lean_string_append(v___x_4364_, v_text_4360_);
    v___x_4366_ = l_Lake_Ansi_chalk___closed__2;
    v___x_4367_ = lean_string_append(v___x_4365_, v___x_4366_);
    return v___x_4367_;
}
pub unsafe fn l_Lake_Ansi_chalk___boxed(
    mut v_colorCode_4368_: *mut crate::leanh::LeanObject,
    mut v_text_4369_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4370_ = l_Lake_Ansi_chalk(v_colorCode_4368_, v_text_4369_);
    crate::leanh::lean_dec_ref(v_text_4369_);
    crate::leanh::lean_dec_ref(v_colorCode_4368_);
    return v_res_4370_;
}
pub unsafe fn l_Lake_OutStream_ctorIdx(
    mut v_x_4371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_4371_) {
        0 => {
            let mut v___x_4372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4372_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_4372_;
        }
        1 => {
            let mut v___x_4373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4373_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_4373_;
        }
        _ => {
            let mut v___x_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4374_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_4374_;
        }
    }
}
pub unsafe fn l_Lake_OutStream_ctorIdx___boxed(
    mut v_x_4375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4376_ = l_Lake_OutStream_ctorIdx(v_x_4375_);
    crate::leanh::lean_dec(v_x_4375_);
    return v_res_4376_;
}
pub unsafe fn l_Lake_OutStream_ctorElim___redArg(
    mut v_t_4377_: *mut crate::leanh::LeanObject,
    mut v_k_4378_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_4377_) == 2 {
        let mut v_s_4379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_s_4379_ = crate::leanh::lean_ctor_get(v_t_4377_, 0);
        crate::leanh::lean_inc_ref(v_s_4379_);
        crate::leanh::lean_dec_ref_known(v_t_4377_, 1);
        v___x_4380_ = crate::leanh::lean_apply_1(v_k_4378_, v_s_4379_);
        return v___x_4380_;
    } else {
        crate::leanh::lean_dec(v_t_4377_);
        return v_k_4378_;
    }
}
pub unsafe fn l_Lake_OutStream_ctorElim(
    mut v_motive_4381_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_4382_: *mut crate::leanh::LeanObject,
    mut v_t_4383_: *mut crate::leanh::LeanObject,
    mut v_h_4384_: *mut crate::leanh::LeanObject,
    mut v_k_4385_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4386_ = l_Lake_OutStream_ctorElim___redArg(v_t_4383_, v_k_4385_);
    return v___x_4386_;
}
pub unsafe fn l_Lake_OutStream_ctorElim___boxed(
    mut v_motive_4387_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_4388_: *mut crate::leanh::LeanObject,
    mut v_t_4389_: *mut crate::leanh::LeanObject,
    mut v_h_4390_: *mut crate::leanh::LeanObject,
    mut v_k_4391_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4392_ = l_Lake_OutStream_ctorElim(
        v_motive_4387_,
        v_ctorIdx_4388_,
        v_t_4389_,
        v_h_4390_,
        v_k_4391_,
    );
    crate::leanh::lean_dec(v_ctorIdx_4388_);
    return v_res_4392_;
}
pub unsafe fn l_Lake_OutStream_stdout_elim___redArg(
    mut v_t_4393_: *mut crate::leanh::LeanObject,
    mut v_stdout_4394_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4395_ = l_Lake_OutStream_ctorElim___redArg(v_t_4393_, v_stdout_4394_);
    return v___x_4395_;
}
pub unsafe fn l_Lake_OutStream_stdout_elim(
    mut v_motive_4396_: *mut crate::leanh::LeanObject,
    mut v_t_4397_: *mut crate::leanh::LeanObject,
    mut v_h_4398_: *mut crate::leanh::LeanObject,
    mut v_stdout_4399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4400_ = l_Lake_OutStream_ctorElim___redArg(v_t_4397_, v_stdout_4399_);
    return v___x_4400_;
}
pub unsafe fn l_Lake_OutStream_stderr_elim___redArg(
    mut v_t_4401_: *mut crate::leanh::LeanObject,
    mut v_stderr_4402_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4403_ = l_Lake_OutStream_ctorElim___redArg(v_t_4401_, v_stderr_4402_);
    return v___x_4403_;
}
pub unsafe fn l_Lake_OutStream_stderr_elim(
    mut v_motive_4404_: *mut crate::leanh::LeanObject,
    mut v_t_4405_: *mut crate::leanh::LeanObject,
    mut v_h_4406_: *mut crate::leanh::LeanObject,
    mut v_stderr_4407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4408_ = l_Lake_OutStream_ctorElim___redArg(v_t_4405_, v_stderr_4407_);
    return v___x_4408_;
}
pub unsafe fn l_Lake_OutStream_stream_elim___redArg(
    mut v_t_4409_: *mut crate::leanh::LeanObject,
    mut v_stream_4410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4411_ = l_Lake_OutStream_ctorElim___redArg(v_t_4409_, v_stream_4410_);
    return v___x_4411_;
}
pub unsafe fn l_Lake_OutStream_stream_elim(
    mut v_motive_4412_: *mut crate::leanh::LeanObject,
    mut v_t_4413_: *mut crate::leanh::LeanObject,
    mut v_h_4414_: *mut crate::leanh::LeanObject,
    mut v_stream_4415_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4416_ = l_Lake_OutStream_ctorElim___redArg(v_t_4413_, v_stream_4415_);
    return v___x_4416_;
}
pub unsafe fn l_Lake_OutStream_get(
    mut v_x_4417_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_4417_) {
        0 => {
            let mut v___x_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4419_ = lean_get_stdout();
            return v___x_4419_;
        }
        1 => {
            let mut v___x_4420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4420_ = lean_get_stderr();
            return v___x_4420_;
        }
        _ => {
            let mut v_s_4421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_s_4421_ = crate::leanh::lean_ctor_get(v_x_4417_, 0);
            crate::leanh::lean_inc_ref(v_s_4421_);
            return v_s_4421_;
        }
    }
}
pub unsafe fn l_Lake_OutStream_get___boxed(
    mut v_x_4422_: *mut crate::leanh::LeanObject,
    mut v_a_4423_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4424_ = l_Lake_OutStream_get(v_x_4422_);
    crate::leanh::lean_dec(v_x_4422_);
    return v_res_4424_;
}
pub unsafe fn l_Lake_instCoeStreamOutStream___lam__0(
    mut v_s_4425_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4426_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4426_, 0, v_s_4425_);
    return v___x_4426_;
}
pub unsafe fn l_Lake_instCoeHandleOutStream___lam__0(
    mut v_h_4429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4430_ = lean_stream_of_handle(v_h_4429_);
    v___x_4431_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4431_, 0, v___x_4430_);
    return v___x_4431_;
}
pub unsafe fn l_Lake_LogLevel_ctorIdx(mut v_x_4434_: u8) -> *mut crate::leanh::LeanObject {
    match v_x_4434_ {
        0 => {
            let mut v___x_4435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4435_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_4435_;
        }
        1 => {
            let mut v___x_4436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4436_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_4436_;
        }
        2 => {
            let mut v___x_4437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4437_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_4437_;
        }
        _ => {
            let mut v___x_4438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4438_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_4438_;
        }
    }
}
pub unsafe fn l_Lake_LogLevel_ctorIdx___boxed(
    mut v_x_4439_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_4440_: u8 = 0;
    let mut v_res_4441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_4440_ = (crate::leanh::lean_unbox(v_x_4439_) as u8);
    v_res_4441_ = l_Lake_LogLevel_ctorIdx(v_x_boxed_4440_);
    return v_res_4441_;
}
pub unsafe fn l_Lake_LogLevel_toCtorIdx(mut v_x_4442_: u8) -> *mut crate::leanh::LeanObject {
    let mut v___x_4443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4443_ = l_Lake_LogLevel_ctorIdx(v_x_4442_);
    return v___x_4443_;
}
pub unsafe fn l_Lake_LogLevel_toCtorIdx___boxed(
    mut v_x_4444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4__boxed_4445_: u8 = 0;
    let mut v_res_4446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_4445_ = (crate::leanh::lean_unbox(v_x_4444_) as u8);
    v_res_4446_ = l_Lake_LogLevel_toCtorIdx(v_x_4__boxed_4445_);
    return v_res_4446_;
}
pub unsafe fn l_Lake_LogLevel_ctorElim___redArg(
    mut v_k_4447_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_4447_);
    return v_k_4447_;
}
pub unsafe fn l_Lake_LogLevel_ctorElim___redArg___boxed(
    mut v_k_4448_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4449_ = l_Lake_LogLevel_ctorElim___redArg(v_k_4448_);
    crate::leanh::lean_dec(v_k_4448_);
    return v_res_4449_;
}
pub unsafe fn l_Lake_LogLevel_ctorElim(
    mut v_motive_4450_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_4451_: *mut crate::leanh::LeanObject,
    mut v_t_4452_: u8,
    mut v_h_4453_: *mut crate::leanh::LeanObject,
    mut v_k_4454_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_4454_);
    return v_k_4454_;
}
pub unsafe fn l_Lake_LogLevel_ctorElim___boxed(
    mut v_motive_4455_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_4456_: *mut crate::leanh::LeanObject,
    mut v_t_4457_: *mut crate::leanh::LeanObject,
    mut v_h_4458_: *mut crate::leanh::LeanObject,
    mut v_k_4459_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_4460_: u8 = 0;
    let mut v_res_4461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_4460_ = (crate::leanh::lean_unbox(v_t_4457_) as u8);
    v_res_4461_ = l_Lake_LogLevel_ctorElim(
        v_motive_4455_,
        v_ctorIdx_4456_,
        v_t_boxed_4460_,
        v_h_4458_,
        v_k_4459_,
    );
    crate::leanh::lean_dec(v_k_4459_);
    crate::leanh::lean_dec(v_ctorIdx_4456_);
    return v_res_4461_;
}
pub unsafe fn l_Lake_LogLevel_trace_elim___redArg(
    mut v_trace_4462_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_trace_4462_);
    return v_trace_4462_;
}
pub unsafe fn l_Lake_LogLevel_trace_elim___redArg___boxed(
    mut v_trace_4463_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4464_ = l_Lake_LogLevel_trace_elim___redArg(v_trace_4463_);
    crate::leanh::lean_dec(v_trace_4463_);
    return v_res_4464_;
}
pub unsafe fn l_Lake_LogLevel_trace_elim(
    mut v_motive_4465_: *mut crate::leanh::LeanObject,
    mut v_t_4466_: u8,
    mut v_h_4467_: *mut crate::leanh::LeanObject,
    mut v_trace_4468_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_trace_4468_);
    return v_trace_4468_;
}
pub unsafe fn l_Lake_LogLevel_trace_elim___boxed(
    mut v_motive_4469_: *mut crate::leanh::LeanObject,
    mut v_t_4470_: *mut crate::leanh::LeanObject,
    mut v_h_4471_: *mut crate::leanh::LeanObject,
    mut v_trace_4472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_4473_: u8 = 0;
    let mut v_res_4474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_4473_ = (crate::leanh::lean_unbox(v_t_4470_) as u8);
    v_res_4474_ =
        l_Lake_LogLevel_trace_elim(v_motive_4469_, v_t_boxed_4473_, v_h_4471_, v_trace_4472_);
    crate::leanh::lean_dec(v_trace_4472_);
    return v_res_4474_;
}
pub unsafe fn l_Lake_LogLevel_info_elim___redArg(
    mut v_info_4475_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_info_4475_);
    return v_info_4475_;
}
pub unsafe fn l_Lake_LogLevel_info_elim___redArg___boxed(
    mut v_info_4476_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4477_ = l_Lake_LogLevel_info_elim___redArg(v_info_4476_);
    crate::leanh::lean_dec(v_info_4476_);
    return v_res_4477_;
}
pub unsafe fn l_Lake_LogLevel_info_elim(
    mut v_motive_4478_: *mut crate::leanh::LeanObject,
    mut v_t_4479_: u8,
    mut v_h_4480_: *mut crate::leanh::LeanObject,
    mut v_info_4481_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_info_4481_);
    return v_info_4481_;
}
pub unsafe fn l_Lake_LogLevel_info_elim___boxed(
    mut v_motive_4482_: *mut crate::leanh::LeanObject,
    mut v_t_4483_: *mut crate::leanh::LeanObject,
    mut v_h_4484_: *mut crate::leanh::LeanObject,
    mut v_info_4485_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_4486_: u8 = 0;
    let mut v_res_4487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_4486_ = (crate::leanh::lean_unbox(v_t_4483_) as u8);
    v_res_4487_ =
        l_Lake_LogLevel_info_elim(v_motive_4482_, v_t_boxed_4486_, v_h_4484_, v_info_4485_);
    crate::leanh::lean_dec(v_info_4485_);
    return v_res_4487_;
}
pub unsafe fn l_Lake_LogLevel_warning_elim___redArg(
    mut v_warning_4488_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_warning_4488_);
    return v_warning_4488_;
}
pub unsafe fn l_Lake_LogLevel_warning_elim___redArg___boxed(
    mut v_warning_4489_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4490_ = l_Lake_LogLevel_warning_elim___redArg(v_warning_4489_);
    crate::leanh::lean_dec(v_warning_4489_);
    return v_res_4490_;
}
pub unsafe fn l_Lake_LogLevel_warning_elim(
    mut v_motive_4491_: *mut crate::leanh::LeanObject,
    mut v_t_4492_: u8,
    mut v_h_4493_: *mut crate::leanh::LeanObject,
    mut v_warning_4494_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_warning_4494_);
    return v_warning_4494_;
}
pub unsafe fn l_Lake_LogLevel_warning_elim___boxed(
    mut v_motive_4495_: *mut crate::leanh::LeanObject,
    mut v_t_4496_: *mut crate::leanh::LeanObject,
    mut v_h_4497_: *mut crate::leanh::LeanObject,
    mut v_warning_4498_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_4499_: u8 = 0;
    let mut v_res_4500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_4499_ = (crate::leanh::lean_unbox(v_t_4496_) as u8);
    v_res_4500_ =
        l_Lake_LogLevel_warning_elim(v_motive_4495_, v_t_boxed_4499_, v_h_4497_, v_warning_4498_);
    crate::leanh::lean_dec(v_warning_4498_);
    return v_res_4500_;
}
pub unsafe fn l_Lake_LogLevel_error_elim___redArg(
    mut v_error_4501_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_error_4501_);
    return v_error_4501_;
}
pub unsafe fn l_Lake_LogLevel_error_elim___redArg___boxed(
    mut v_error_4502_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4503_ = l_Lake_LogLevel_error_elim___redArg(v_error_4502_);
    crate::leanh::lean_dec(v_error_4502_);
    return v_res_4503_;
}
pub unsafe fn l_Lake_LogLevel_error_elim(
    mut v_motive_4504_: *mut crate::leanh::LeanObject,
    mut v_t_4505_: u8,
    mut v_h_4506_: *mut crate::leanh::LeanObject,
    mut v_error_4507_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_error_4507_);
    return v_error_4507_;
}
pub unsafe fn l_Lake_LogLevel_error_elim___boxed(
    mut v_motive_4508_: *mut crate::leanh::LeanObject,
    mut v_t_4509_: *mut crate::leanh::LeanObject,
    mut v_h_4510_: *mut crate::leanh::LeanObject,
    mut v_error_4511_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_4512_: u8 = 0;
    let mut v_res_4513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_4512_ = (crate::leanh::lean_unbox(v_t_4509_) as u8);
    v_res_4513_ =
        l_Lake_LogLevel_error_elim(v_motive_4508_, v_t_boxed_4512_, v_h_4510_, v_error_4511_);
    crate::leanh::lean_dec(v_error_4511_);
    return v_res_4513_;
}
pub unsafe fn _init_l_Lake_instInhabitedLogLevel_default() -> u8 {
    let mut v___x_4514_: u8 = 0;
    v___x_4514_ = 0;
    return v___x_4514_;
}
pub unsafe fn _init_l_Lake_instInhabitedLogLevel() -> u8 {
    let mut v___x_4515_: u8 = 0;
    v___x_4515_ = 0;
    return v___x_4515_;
}
pub unsafe fn l_Lake_instReprLogLevel_repr(
    mut v_x_4528_: u8,
    mut v_prec_4529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4534_: u8 = 0;
    let mut v___x_4535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: u8 = 0;
    let mut v___x_4542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4548_: u8 = 0;
    let mut v___x_4549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: u8 = 0;
    let mut v___x_4556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4559_: u8 = 0;
    let mut v___x_4560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: u8 = 0;
    let mut v___x_4564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4567_: u8 = 0;
    let mut v___x_4568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4571_: u8 = 0;
    let mut v___x_4572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match v_x_4528_ {
                0 => {
                    v___x_4558_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_4559_ = lean_nat_dec_le(v___x_4558_, v_prec_4529_);
                    if v___x_4559_ == 0 {
                        v___x_4560_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprVerbosity_repr___closed__6),
                            core::ptr::addr_of_mut!(l_Lake_instReprVerbosity_repr___closed__6_once),
                            _init_l_Lake_instReprVerbosity_repr___closed__6,
                        );
                        v___y_4531_ = v___x_4560_;
                        state = 1;
                        continue;
                    } else {
                        v___x_4561_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprVerbosity_repr___closed__7),
                            core::ptr::addr_of_mut!(l_Lake_instReprVerbosity_repr___closed__7_once),
                            _init_l_Lake_instReprVerbosity_repr___closed__7,
                        );
                        v___y_4531_ = v___x_4561_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v___x_4562_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_4563_ = lean_nat_dec_le(v___x_4562_, v_prec_4529_);
                    if v___x_4563_ == 0 {
                        v___x_4564_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprVerbosity_repr___closed__6),
                            core::ptr::addr_of_mut!(l_Lake_instReprVerbosity_repr___closed__6_once),
                            _init_l_Lake_instReprVerbosity_repr___closed__6,
                        );
                        v___y_4538_ = v___x_4564_;
                        state = 2;
                        continue;
                    } else {
                        v___x_4565_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprVerbosity_repr___closed__7),
                            core::ptr::addr_of_mut!(l_Lake_instReprVerbosity_repr___closed__7_once),
                            _init_l_Lake_instReprVerbosity_repr___closed__7,
                        );
                        v___y_4538_ = v___x_4565_;
                        state = 2;
                        continue;
                    }
                }
                2 => {
                    v___x_4566_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_4567_ = lean_nat_dec_le(v___x_4566_, v_prec_4529_);
                    if v___x_4567_ == 0 {
                        v___x_4568_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprVerbosity_repr___closed__6),
                            core::ptr::addr_of_mut!(l_Lake_instReprVerbosity_repr___closed__6_once),
                            _init_l_Lake_instReprVerbosity_repr___closed__6,
                        );
                        v___y_4545_ = v___x_4568_;
                        state = 3;
                        continue;
                    } else {
                        v___x_4569_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprVerbosity_repr___closed__7),
                            core::ptr::addr_of_mut!(l_Lake_instReprVerbosity_repr___closed__7_once),
                            _init_l_Lake_instReprVerbosity_repr___closed__7,
                        );
                        v___y_4545_ = v___x_4569_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v___x_4570_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_4571_ = lean_nat_dec_le(v___x_4570_, v_prec_4529_);
                    if v___x_4571_ == 0 {
                        v___x_4572_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprVerbosity_repr___closed__6),
                            core::ptr::addr_of_mut!(l_Lake_instReprVerbosity_repr___closed__6_once),
                            _init_l_Lake_instReprVerbosity_repr___closed__6,
                        );
                        v___y_4552_ = v___x_4572_;
                        state = 4;
                        continue;
                    } else {
                        v___x_4573_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprVerbosity_repr___closed__7),
                            core::ptr::addr_of_mut!(l_Lake_instReprVerbosity_repr___closed__7_once),
                            _init_l_Lake_instReprVerbosity_repr___closed__7,
                        );
                        v___y_4552_ = v___x_4573_;
                        state = 4;
                        continue;
                    }
                }
            },
            1 => {
                v___x_4532_ = l_Lake_instReprLogLevel_repr___closed__1;
                crate::leanh::lean_inc(v___y_4531_);
                v___x_4533_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4533_, 0, v___y_4531_);
                crate::leanh::lean_ctor_set(v___x_4533_, 1, v___x_4532_);
                v___x_4534_ = 0;
                v___x_4535_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4535_, 0, v___x_4533_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4535_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4534_,
                );
                v___x_4536_ = l_Repr_addAppParen(v___x_4535_, v_prec_4529_);
                return v___x_4536_;
            }
            2 => {
                v___x_4539_ = l_Lake_instReprLogLevel_repr___closed__3;
                crate::leanh::lean_inc(v___y_4538_);
                v___x_4540_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4540_, 0, v___y_4538_);
                crate::leanh::lean_ctor_set(v___x_4540_, 1, v___x_4539_);
                v___x_4541_ = 0;
                v___x_4542_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4542_, 0, v___x_4540_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4542_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4541_,
                );
                v___x_4543_ = l_Repr_addAppParen(v___x_4542_, v_prec_4529_);
                return v___x_4543_;
            }
            3 => {
                v___x_4546_ = l_Lake_instReprLogLevel_repr___closed__5;
                crate::leanh::lean_inc(v___y_4545_);
                v___x_4547_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4547_, 0, v___y_4545_);
                crate::leanh::lean_ctor_set(v___x_4547_, 1, v___x_4546_);
                v___x_4548_ = 0;
                v___x_4549_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4549_, 0, v___x_4547_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4549_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4548_,
                );
                v___x_4550_ = l_Repr_addAppParen(v___x_4549_, v_prec_4529_);
                return v___x_4550_;
            }
            4 => {
                v___x_4553_ = l_Lake_instReprLogLevel_repr___closed__7;
                crate::leanh::lean_inc(v___y_4552_);
                v___x_4554_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4554_, 0, v___y_4552_);
                crate::leanh::lean_ctor_set(v___x_4554_, 1, v___x_4553_);
                v___x_4555_ = 0;
                v___x_4556_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4556_, 0, v___x_4554_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4556_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4555_,
                );
                v___x_4557_ = l_Repr_addAppParen(v___x_4556_, v_prec_4529_);
                return v___x_4557_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instReprLogLevel_repr___boxed(
    mut v_x_4574_: *mut crate::leanh::LeanObject,
    mut v_prec_4575_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_229__boxed_4576_: u8 = 0;
    let mut v_res_4577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_229__boxed_4576_ = (crate::leanh::lean_unbox(v_x_4574_) as u8);
    v_res_4577_ = l_Lake_instReprLogLevel_repr(v_x_229__boxed_4576_, v_prec_4575_);
    crate::leanh::lean_dec(v_prec_4575_);
    return v_res_4577_;
}
pub unsafe fn l_Lake_LogLevel_ofNat(mut v_n_4580_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_4581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4582_: u8 = 0;
    v___x_4581_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_4582_ = lean_nat_dec_le(v_n_4580_, v___x_4581_);
    if v___x_4582_ == 0 {
        let mut v___x_4583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4584_: u8 = 0;
        v___x_4583_ = crate::leanh::lean_unsigned_to_nat(2);
        v___x_4584_ = lean_nat_dec_le(v_n_4580_, v___x_4583_);
        if v___x_4584_ == 0 {
            let mut v___x_4585_: u8 = 0;
            v___x_4585_ = 3;
            return v___x_4585_;
        } else {
            let mut v___x_4586_: u8 = 0;
            v___x_4586_ = 2;
            return v___x_4586_;
        }
    } else {
        let mut v___x_4587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4588_: u8 = 0;
        v___x_4587_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_4588_ = lean_nat_dec_le(v_n_4580_, v___x_4587_);
        if v___x_4588_ == 0 {
            let mut v___x_4589_: u8 = 0;
            v___x_4589_ = 1;
            return v___x_4589_;
        } else {
            let mut v___x_4590_: u8 = 0;
            v___x_4590_ = 0;
            return v___x_4590_;
        }
    }
}
pub unsafe fn l_Lake_LogLevel_ofNat___boxed(
    mut v_n_4591_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4592_: u8 = 0;
    let mut v_r_4593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4592_ = l_Lake_LogLevel_ofNat(v_n_4591_);
    crate::leanh::lean_dec(v_n_4591_);
    v_r_4593_ = crate::leanh::lean_box((v_res_4592_) as usize);
    return v_r_4593_;
}
pub unsafe fn l_Lake_instDecidableEqLogLevel(mut v_x_4594_: u8, mut v_y_4595_: u8) -> u8 {
    let mut v___x_4596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4598_: u8 = 0;
    v___x_4596_ = l_Lake_LogLevel_ctorIdx(v_x_4594_);
    v___x_4597_ = l_Lake_LogLevel_ctorIdx(v_y_4595_);
    v___x_4598_ = lean_nat_dec_eq(v___x_4596_, v___x_4597_);
    crate::leanh::lean_dec(v___x_4597_);
    crate::leanh::lean_dec(v___x_4596_);
    return v___x_4598_;
}
pub unsafe fn l_Lake_instDecidableEqLogLevel___boxed(
    mut v_x_4599_: *mut crate::leanh::LeanObject,
    mut v_y_4600_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_13__boxed_4601_: u8 = 0;
    let mut v_y_14__boxed_4602_: u8 = 0;
    let mut v_res_4603_: u8 = 0;
    let mut v_r_4604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_13__boxed_4601_ = (crate::leanh::lean_unbox(v_x_4599_) as u8);
    v_y_14__boxed_4602_ = (crate::leanh::lean_unbox(v_y_4600_) as u8);
    v_res_4603_ = l_Lake_instDecidableEqLogLevel(v_x_13__boxed_4601_, v_y_14__boxed_4602_);
    v_r_4604_ = crate::leanh::lean_box((v_res_4603_) as usize);
    return v_r_4604_;
}
pub unsafe fn l_Lake_instOrdLogLevel_ord(mut v_x_4605_: u8, mut v_y_4606_: u8) -> u8 {
    let mut v___x_4607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4609_: u8 = 0;
    v___x_4607_ = l_Lake_LogLevel_ctorIdx(v_x_4605_);
    v___x_4608_ = l_Lake_LogLevel_ctorIdx(v_y_4606_);
    v___x_4609_ = lean_nat_dec_lt(v___x_4607_, v___x_4608_);
    if v___x_4609_ == 0 {
        let mut v___x_4610_: u8 = 0;
        v___x_4610_ = lean_nat_dec_eq(v___x_4607_, v___x_4608_);
        crate::leanh::lean_dec(v___x_4608_);
        crate::leanh::lean_dec(v___x_4607_);
        if v___x_4610_ == 0 {
            let mut v___x_4611_: u8 = 0;
            v___x_4611_ = 2;
            return v___x_4611_;
        } else {
            let mut v___x_4612_: u8 = 0;
            v___x_4612_ = 1;
            return v___x_4612_;
        }
    } else {
        let mut v___x_4613_: u8 = 0;
        crate::leanh::lean_dec(v___x_4608_);
        crate::leanh::lean_dec(v___x_4607_);
        v___x_4613_ = 0;
        return v___x_4613_;
    }
}
pub unsafe fn l_Lake_instOrdLogLevel_ord___boxed(
    mut v_x_4614_: *mut crate::leanh::LeanObject,
    mut v_y_4615_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_30__boxed_4616_: u8 = 0;
    let mut v_y_31__boxed_4617_: u8 = 0;
    let mut v_res_4618_: u8 = 0;
    let mut v_r_4619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_30__boxed_4616_ = (crate::leanh::lean_unbox(v_x_4614_) as u8);
    v_y_31__boxed_4617_ = (crate::leanh::lean_unbox(v_y_4615_) as u8);
    v_res_4618_ = l_Lake_instOrdLogLevel_ord(v_x_30__boxed_4616_, v_y_31__boxed_4617_);
    v_r_4619_ = crate::leanh::lean_box((v_res_4618_) as usize);
    return v_r_4619_;
}
pub unsafe fn l_Lake_instToJsonLogLevel_toJson(mut v_x_4634_: u8) -> *mut crate::leanh::LeanObject {
    match v_x_4634_ {
        0 => {
            let mut v___x_4635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4635_ = l_Lake_instToJsonLogLevel_toJson___closed__1;
            return v___x_4635_;
        }
        1 => {
            let mut v___x_4636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4636_ = l_Lake_instToJsonLogLevel_toJson___closed__3;
            return v___x_4636_;
        }
        2 => {
            let mut v___x_4637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4637_ = l_Lake_instToJsonLogLevel_toJson___closed__5;
            return v___x_4637_;
        }
        _ => {
            let mut v___x_4638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4638_ = l_Lake_instToJsonLogLevel_toJson___closed__7;
            return v___x_4638_;
        }
    }
}
pub unsafe fn l_Lake_instToJsonLogLevel_toJson___boxed(
    mut v_x_4639_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_88__boxed_4640_: u8 = 0;
    let mut v_res_4641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_88__boxed_4640_ = (crate::leanh::lean_unbox(v_x_4639_) as u8);
    v_res_4641_ = l_Lake_instToJsonLogLevel_toJson(v_x_88__boxed_4640_);
    return v_res_4641_;
}
pub unsafe fn l_Lake_instFromJsonLogLevel_fromJson(
    mut v_json_4662_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4663_ = l_Lean_Json_getTag_x3f(v_json_4662_);
    if crate::leanh::lean_obj_tag(v___x_4663_) == 0 {
        let mut v___x_4664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4664_ = l_Lake_instFromJsonLogLevel_fromJson___closed__1;
        return v___x_4664_;
    } else {
        let mut v_val_4665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4667_: u8 = 0;
        v_val_4665_ = crate::leanh::lean_ctor_get(v___x_4663_, 0);
        crate::leanh::lean_inc(v_val_4665_);
        crate::leanh::lean_dec_ref_known(v___x_4663_, 1);
        v___x_4666_ = l_Lake_instToJsonLogLevel_toJson___closed__6;
        v___x_4667_ = lean_string_dec_eq(v_val_4665_, v___x_4666_);
        if v___x_4667_ == 0 {
            let mut v___x_4668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4669_: u8 = 0;
            v___x_4668_ = l_Lake_instToJsonLogLevel_toJson___closed__0;
            v___x_4669_ = lean_string_dec_eq(v_val_4665_, v___x_4668_);
            if v___x_4669_ == 0 {
                let mut v___x_4670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4671_: u8 = 0;
                v___x_4670_ = l_Lake_instToJsonLogLevel_toJson___closed__2;
                v___x_4671_ = lean_string_dec_eq(v_val_4665_, v___x_4670_);
                if v___x_4671_ == 0 {
                    let mut v___x_4672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4673_: u8 = 0;
                    v___x_4672_ = l_Lake_instToJsonLogLevel_toJson___closed__4;
                    v___x_4673_ = lean_string_dec_eq(v_val_4665_, v___x_4672_);
                    crate::leanh::lean_dec(v_val_4665_);
                    if v___x_4673_ == 0 {
                        let mut v___x_4674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v___x_4674_ = l_Lake_instFromJsonLogLevel_fromJson___closed__3;
                        return v___x_4674_;
                    } else {
                        let mut v___x_4675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v___x_4675_ = l_Lake_instFromJsonLogLevel_fromJson___closed__4;
                        return v___x_4675_;
                    }
                } else {
                    let mut v___x_4676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_val_4665_);
                    v___x_4676_ = l_Lake_instFromJsonLogLevel_fromJson___closed__5;
                    return v___x_4676_;
                }
            } else {
                let mut v___x_4677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_val_4665_);
                v___x_4677_ = l_Lake_instFromJsonLogLevel_fromJson___closed__6;
                return v___x_4677_;
            }
        } else {
            let mut v___x_4678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_val_4665_);
            v___x_4678_ = l_Lake_instFromJsonLogLevel_fromJson___closed__7;
            return v___x_4678_;
        }
    }
}
pub unsafe fn _init_l_Lake_instLTLogLevel() -> *mut crate::leanh::LeanObject {
    let mut v___x_4681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4681_ = crate::leanh::lean_box(0);
    return v___x_4681_;
}
pub unsafe fn _init_l_Lake_instLELogLevel() -> *mut crate::leanh::LeanObject {
    let mut v___x_4682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4682_ = crate::leanh::lean_box(0);
    return v___x_4682_;
}
pub unsafe fn l_Lake_instMinLogLevel___lam__0(mut v_x_4683_: u8, mut v_y_4684_: u8) -> u8 {
    let mut v___x_4685_: u8 = 0;
    v___x_4685_ = l_Lake_instOrdLogLevel_ord(v_x_4683_, v_y_4684_);
    if v___x_4685_ == 2 {
        return v_y_4684_;
    } else {
        return v_x_4683_;
    }
}
pub unsafe fn l_Lake_instMinLogLevel___lam__0___boxed(
    mut v_x_4686_: *mut crate::leanh::LeanObject,
    mut v_y_4687_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_4688_: u8 = 0;
    let mut v_y_boxed_4689_: u8 = 0;
    let mut v_res_4690_: u8 = 0;
    let mut v_r_4691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_4688_ = (crate::leanh::lean_unbox(v_x_4686_) as u8);
    v_y_boxed_4689_ = (crate::leanh::lean_unbox(v_y_4687_) as u8);
    v_res_4690_ = l_Lake_instMinLogLevel___lam__0(v_x_boxed_4688_, v_y_boxed_4689_);
    v_r_4691_ = crate::leanh::lean_box((v_res_4690_) as usize);
    return v_r_4691_;
}
pub unsafe fn l_Lake_instMaxLogLevel___lam__0(mut v_x_4694_: u8, mut v_y_4695_: u8) -> u8 {
    let mut v___x_4696_: u8 = 0;
    v___x_4696_ = l_Lake_instOrdLogLevel_ord(v_x_4694_, v_y_4695_);
    if v___x_4696_ == 2 {
        return v_x_4694_;
    } else {
        return v_y_4695_;
    }
}
pub unsafe fn l_Lake_instMaxLogLevel___lam__0___boxed(
    mut v_x_4697_: *mut crate::leanh::LeanObject,
    mut v_y_4698_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_4699_: u8 = 0;
    let mut v_y_boxed_4700_: u8 = 0;
    let mut v_res_4701_: u8 = 0;
    let mut v_r_4702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_4699_ = (crate::leanh::lean_unbox(v_x_4697_) as u8);
    v_y_boxed_4700_ = (crate::leanh::lean_unbox(v_y_4698_) as u8);
    v_res_4701_ = l_Lake_instMaxLogLevel___lam__0(v_x_boxed_4699_, v_y_boxed_4700_);
    v_r_4702_ = crate::leanh::lean_box((v_res_4701_) as usize);
    return v_r_4702_;
}
pub unsafe fn l_Lake_LogLevel_icon(mut v_x_4705_: u8) -> u32 {
    match v_x_4705_ {
        2 => {
            let mut v___x_4706_: u32 = 0;
            v___x_4706_ = 9888;
            return v___x_4706_;
        }
        3 => {
            let mut v___x_4707_: u32 = 0;
            v___x_4707_ = 10006;
            return v___x_4707_;
        }
        _ => {
            let mut v___x_4708_: u32 = 0;
            v___x_4708_ = 8505;
            return v___x_4708_;
        }
    }
}
pub unsafe fn l_Lake_LogLevel_icon___boxed(
    mut v_x_4709_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_33__boxed_4710_: u8 = 0;
    let mut v_res_4711_: u32 = 0;
    let mut v_r_4712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_33__boxed_4710_ = (crate::leanh::lean_unbox(v_x_4709_) as u8);
    v_res_4711_ = l_Lake_LogLevel_icon(v_x_33__boxed_4710_);
    v_r_4712_ = crate::leanh::lean_box_uint32(v_res_4711_);
    return v_r_4712_;
}
pub unsafe fn l_Lake_LogLevel_ansiColor(mut v_x_4716_: u8) -> *mut crate::leanh::LeanObject {
    match v_x_4716_ {
        2 => {
            let mut v___x_4717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4717_ = l_Lake_LogLevel_ansiColor___closed__0;
            return v___x_4717_;
        }
        3 => {
            let mut v___x_4718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4718_ = l_Lake_LogLevel_ansiColor___closed__1;
            return v___x_4718_;
        }
        _ => {
            let mut v___x_4719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4719_ = l_Lake_LogLevel_ansiColor___closed__2;
            return v___x_4719_;
        }
    }
}
pub unsafe fn l_Lake_LogLevel_ansiColor___boxed(
    mut v_x_4720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_36__boxed_4721_: u8 = 0;
    let mut v_res_4722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_36__boxed_4721_ = (crate::leanh::lean_unbox(v_x_4720_) as u8);
    v_res_4722_ = l_Lake_LogLevel_ansiColor(v_x_36__boxed_4721_);
    return v_res_4722_;
}
pub unsafe fn l_String_mapAux___at___00Lake_LogLevel_ofString_x3f_spec__0(
    mut v_s_4723_: *mut crate::leanh::LeanObject,
    mut v_p_4724_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4726_: u32 = 0;
    let mut v___x_4727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4732_: u8 = 0;
    let mut v___x_4733_: u32 = 0;
    let mut v___x_4734_: u32 = 0;
    let mut v___x_4735_: u8 = 0;
    let mut v___x_4736_: u32 = 0;
    let mut v___x_4737_: u8 = 0;
    let mut v___x_4738_: u32 = 0;
    let mut v___x_4739_: u32 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4731_ = lean_string_utf8_byte_size(v_s_4723_);
                v___x_4732_ = lean_nat_dec_eq(v_p_4724_, v___x_4731_);
                if v___x_4732_ == 0 {
                    v___x_4733_ = lean_string_utf8_get_fast(v_s_4723_, v_p_4724_);
                    v___x_4734_ = 65;
                    v___x_4735_ = lean_uint32_dec_le(v___x_4734_, v___x_4733_);
                    if v___x_4735_ == 0 {
                        v___y_4726_ = v___x_4733_;
                        state = 1;
                        continue;
                    } else {
                        v___x_4736_ = 90;
                        v___x_4737_ = lean_uint32_dec_le(v___x_4733_, v___x_4736_);
                        if v___x_4737_ == 0 {
                            v___y_4726_ = v___x_4733_;
                            state = 1;
                            continue;
                        } else {
                            v___x_4738_ = 32;
                            v___x_4739_ = lean_uint32_add(v___x_4733_, v___x_4738_);
                            v___y_4726_ = v___x_4739_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_p_4724_);
                    return v_s_4723_;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_p_4724_);
                v___x_4727_ = lean_string_utf8_set(v_s_4723_, v_p_4724_, v___y_4726_);
                v___x_4728_ = l_Char_utf8Size(v___y_4726_);
                v___x_4729_ = lean_nat_add(v_p_4724_, v___x_4728_);
                crate::leanh::lean_dec(v___x_4728_);
                crate::leanh::lean_dec(v_p_4724_);
                v_s_4723_ = v___x_4727_;
                v_p_4724_ = v___x_4729_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LogLevel_ofString_x3f(
    mut v_s_4754_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4762_: u8 = 0;
    let mut v___x_4763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4764_: u8 = 0;
    let mut v___x_4765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4766_: u8 = 0;
    let mut v___x_4767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4768_: u8 = 0;
    let mut v___x_4769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4770_: u8 = 0;
    let mut v___x_4771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4772_: u8 = 0;
    let mut v___x_4773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4759_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4760_ = l_String_mapAux___at___00Lake_LogLevel_ofString_x3f_spec__0(
                    v_s_4754_,
                    v___x_4759_,
                );
                v___x_4761_ = l_Lake_instToJsonLogLevel_toJson___closed__0;
                v___x_4762_ = lean_string_dec_eq(v___x_4760_, v___x_4761_);
                if v___x_4762_ == 0 {
                    v___x_4763_ = l_Lake_instToJsonLogLevel_toJson___closed__2;
                    v___x_4764_ = lean_string_dec_eq(v___x_4760_, v___x_4763_);
                    if v___x_4764_ == 0 {
                        v___x_4765_ = l_Lake_LogLevel_ofString_x3f___closed__2;
                        v___x_4766_ = lean_string_dec_eq(v___x_4760_, v___x_4765_);
                        if v___x_4766_ == 0 {
                            v___x_4767_ = l_Lake_LogLevel_ofString_x3f___closed__3;
                            v___x_4768_ = lean_string_dec_eq(v___x_4760_, v___x_4767_);
                            if v___x_4768_ == 0 {
                                v___x_4769_ = l_Lake_instToJsonLogLevel_toJson___closed__4;
                                v___x_4770_ = lean_string_dec_eq(v___x_4760_, v___x_4769_);
                                if v___x_4770_ == 0 {
                                    v___x_4771_ = l_Lake_instToJsonLogLevel_toJson___closed__6;
                                    v___x_4772_ = lean_string_dec_eq(v___x_4760_, v___x_4771_);
                                    crate::leanh::lean_dec_ref(v___x_4760_);
                                    if v___x_4772_ == 0 {
                                        v___x_4773_ = crate::leanh::lean_box(0);
                                        return v___x_4773_;
                                    } else {
                                        v___x_4774_ = l_Lake_LogLevel_ofString_x3f___closed__4;
                                        return v___x_4774_;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_4760_);
                                    state = 2;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___x_4760_);
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_4760_);
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_4760_);
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_4760_);
                    v___x_4775_ = l_Lake_LogLevel_ofString_x3f___closed__5;
                    return v___x_4775_;
                }
            }
            1 => {
                v___x_4756_ = l_Lake_LogLevel_ofString_x3f___closed__0;
                return v___x_4756_;
            }
            2 => {
                v___x_4758_ = l_Lake_LogLevel_ofString_x3f___closed__1;
                return v___x_4758_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LogLevel_toString(mut v_x_4776_: u8) -> *mut crate::leanh::LeanObject {
    match v_x_4776_ {
        0 => {
            let mut v___x_4777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4777_ = l_Lake_instToJsonLogLevel_toJson___closed__0;
            return v___x_4777_;
        }
        1 => {
            let mut v___x_4778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4778_ = l_Lake_instToJsonLogLevel_toJson___closed__2;
            return v___x_4778_;
        }
        2 => {
            let mut v___x_4779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4779_ = l_Lake_instToJsonLogLevel_toJson___closed__4;
            return v___x_4779_;
        }
        _ => {
            let mut v___x_4780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4780_ = l_Lake_instToJsonLogLevel_toJson___closed__6;
            return v___x_4780_;
        }
    }
}
pub unsafe fn l_Lake_LogLevel_toString___boxed(
    mut v_x_4781_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_36__boxed_4782_: u8 = 0;
    let mut v_res_4783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_36__boxed_4782_ = (crate::leanh::lean_unbox(v_x_4781_) as u8);
    v_res_4783_ = l_Lake_LogLevel_toString(v_x_36__boxed_4782_);
    return v_res_4783_;
}
pub unsafe fn l_Lake_LogLevel_ofMessageSeverity(mut v_x_4786_: u8) -> u8 {
    match v_x_4786_ {
        0 => {
            let mut v___x_4787_: u8 = 0;
            v___x_4787_ = 1;
            return v___x_4787_;
        }
        1 => {
            let mut v___x_4788_: u8 = 0;
            v___x_4788_ = 2;
            return v___x_4788_;
        }
        _ => {
            let mut v___x_4789_: u8 = 0;
            v___x_4789_ = 3;
            return v___x_4789_;
        }
    }
}
pub unsafe fn l_Lake_LogLevel_ofMessageSeverity___boxed(
    mut v_x_4790_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_25__boxed_4791_: u8 = 0;
    let mut v_res_4792_: u8 = 0;
    let mut v_r_4793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_25__boxed_4791_ = (crate::leanh::lean_unbox(v_x_4790_) as u8);
    v_res_4792_ = l_Lake_LogLevel_ofMessageSeverity(v_x_25__boxed_4791_);
    v_r_4793_ = crate::leanh::lean_box((v_res_4792_) as usize);
    return v_r_4793_;
}
pub unsafe fn l_Lake_LogLevel_toMessageSeverity(mut v_x_4794_: u8) -> u8 {
    match v_x_4794_ {
        2 => {
            let mut v___x_4795_: u8 = 0;
            v___x_4795_ = 1;
            return v___x_4795_;
        }
        3 => {
            let mut v___x_4796_: u8 = 0;
            v___x_4796_ = 2;
            return v___x_4796_;
        }
        _ => {
            let mut v___x_4797_: u8 = 0;
            v___x_4797_ = 0;
            return v___x_4797_;
        }
    }
}
pub unsafe fn l_Lake_LogLevel_toMessageSeverity___boxed(
    mut v_x_4798_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_30__boxed_4799_: u8 = 0;
    let mut v_res_4800_: u8 = 0;
    let mut v_r_4801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_30__boxed_4799_ = (crate::leanh::lean_unbox(v_x_4798_) as u8);
    v_res_4800_ = l_Lake_LogLevel_toMessageSeverity(v_x_30__boxed_4799_);
    v_r_4801_ = crate::leanh::lean_box((v_res_4800_) as usize);
    return v_r_4801_;
}
pub unsafe fn l_Lake_Verbosity_minLogLv(mut v_x_4802_: u8) -> u8 {
    match v_x_4802_ {
        0 => {
            let mut v___x_4803_: u8 = 0;
            v___x_4803_ = 2;
            return v___x_4803_;
        }
        1 => {
            let mut v___x_4804_: u8 = 0;
            v___x_4804_ = 1;
            return v___x_4804_;
        }
        _ => {
            let mut v___x_4805_: u8 = 0;
            v___x_4805_ = 0;
            return v___x_4805_;
        }
    }
}
pub unsafe fn l_Lake_Verbosity_minLogLv___boxed(
    mut v_x_4806_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_25__boxed_4807_: u8 = 0;
    let mut v_res_4808_: u8 = 0;
    let mut v_r_4809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_25__boxed_4807_ = (crate::leanh::lean_unbox(v_x_4806_) as u8);
    v_res_4808_ = l_Lake_Verbosity_minLogLv(v_x_25__boxed_4807_);
    v_r_4809_ = crate::leanh::lean_box((v_res_4808_) as usize);
    return v_r_4809_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lake_instToJsonLogEntry_toJson_spec__0(
    mut v_a_4816_: *mut crate::leanh::LeanObject,
    mut v_a_4817_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_4816_) == 0 {
                    v___x_4818_ = lean_array_to_list(v_a_4817_);
                    return v___x_4818_;
                } else {
                    v_head_4819_ = crate::leanh::lean_ctor_get(v_a_4816_, 0);
                    crate::leanh::lean_inc(v_head_4819_);
                    v_tail_4820_ = crate::leanh::lean_ctor_get(v_a_4816_, 1);
                    crate::leanh::lean_inc(v_tail_4820_);
                    crate::leanh::lean_dec_ref_known(v_a_4816_, 2);
                    v___x_4821_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(
                        v_a_4817_,
                        v_head_4819_,
                    );
                    v_a_4816_ = v_tail_4820_;
                    v_a_4817_ = v___x_4821_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instToJsonLogEntry_toJson(
    mut v_x_4827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_level_4828_: u8 = 0;
    let mut v_message_4829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_level_4828_ = crate::leanh::lean_ctor_get_uint8(
        v_x_4827_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
    );
    v_message_4829_ = crate::leanh::lean_ctor_get(v_x_4827_, 0);
    v___x_4830_ = l_Lake_instToJsonLogEntry_toJson___closed__0;
    v___x_4831_ = l_Lake_instToJsonLogLevel_toJson(v_level_4828_);
    v___x_4832_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4832_, 0, v___x_4830_);
    crate::leanh::lean_ctor_set(v___x_4832_, 1, v___x_4831_);
    v___x_4833_ = crate::leanh::lean_box(0);
    v___x_4834_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4834_, 0, v___x_4832_);
    crate::leanh::lean_ctor_set(v___x_4834_, 1, v___x_4833_);
    v___x_4835_ = l_Lake_instToJsonLogEntry_toJson___closed__1;
    crate::leanh::lean_inc_ref(v_message_4829_);
    v___x_4836_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4836_, 0, v_message_4829_);
    v___x_4837_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4837_, 0, v___x_4835_);
    crate::leanh::lean_ctor_set(v___x_4837_, 1, v___x_4836_);
    v___x_4838_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4838_, 0, v___x_4837_);
    crate::leanh::lean_ctor_set(v___x_4838_, 1, v___x_4833_);
    v___x_4839_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4839_, 0, v___x_4838_);
    crate::leanh::lean_ctor_set(v___x_4839_, 1, v___x_4833_);
    v___x_4840_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4840_, 0, v___x_4834_);
    crate::leanh::lean_ctor_set(v___x_4840_, 1, v___x_4839_);
    v___x_4841_ = l_Lake_instToJsonLogEntry_toJson___closed__2;
    v___x_4842_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lake_instToJsonLogEntry_toJson_spec__0(v___x_4840_, v___x_4841_);
    v___x_4843_ = l_Lean_Json_mkObj(v___x_4842_);
    crate::leanh::lean_dec(v___x_4842_);
    return v___x_4843_;
}
pub unsafe fn l_Lake_instToJsonLogEntry_toJson___boxed(
    mut v_x_4844_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4845_ = l_Lake_instToJsonLogEntry_toJson(v_x_4844_);
    crate::leanh::lean_dec_ref(v_x_4844_);
    return v_res_4845_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lake_instFromJsonLogEntry_fromJson_spec__0(
    mut v_j_4848_: *mut crate::leanh::LeanObject,
    mut v_k_4849_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4850_ = l_Lean_Json_getObjValD(v_j_4848_, v_k_4849_);
    v___x_4851_ = l_Lake_instFromJsonLogLevel_fromJson(v___x_4850_);
    return v___x_4851_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lake_instFromJsonLogEntry_fromJson_spec__0___boxed(
    mut v_j_4852_: *mut crate::leanh::LeanObject,
    mut v_k_4853_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4854_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_instFromJsonLogEntry_fromJson_spec__0(
        v_j_4852_, v_k_4853_,
    );
    crate::leanh::lean_dec_ref(v_k_4853_);
    return v_res_4854_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lake_instFromJsonLogEntry_fromJson_spec__1(
    mut v_j_4855_: *mut crate::leanh::LeanObject,
    mut v_k_4856_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4857_ = l_Lean_Json_getObjValD(v_j_4855_, v_k_4856_);
    v___x_4858_ = l_Lean_Json_getStr_x3f(v___x_4857_);
    return v___x_4858_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lake_instFromJsonLogEntry_fromJson_spec__1___boxed(
    mut v_j_4859_: *mut crate::leanh::LeanObject,
    mut v_k_4860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4861_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_instFromJsonLogEntry_fromJson_spec__1(
        v_j_4859_, v_k_4860_,
    );
    crate::leanh::lean_dec_ref(v_k_4860_);
    return v_res_4861_;
}
pub unsafe fn _init_l_Lake_instFromJsonLogEntry_fromJson___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4867_: u8 = 0;
    let mut v___x_4868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4867_ = 1;
    v___x_4868_ = l_Lake_instFromJsonLogEntry_fromJson___closed__2;
    v___x_4869_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4868_, v___x_4867_);
    return v___x_4869_;
}
pub unsafe fn _init_l_Lake_instFromJsonLogEntry_fromJson___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4871_ = l_Lake_instFromJsonLogEntry_fromJson___closed__4;
    v___x_4872_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instFromJsonLogEntry_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lake_instFromJsonLogEntry_fromJson___closed__3_once),
        _init_l_Lake_instFromJsonLogEntry_fromJson___closed__3,
    );
    v___x_4873_ = lean_string_append(v___x_4872_, v___x_4871_);
    return v___x_4873_;
}
pub unsafe fn _init_l_Lake_instFromJsonLogEntry_fromJson___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4876_: u8 = 0;
    let mut v___x_4877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4876_ = 1;
    v___x_4877_ = l_Lake_instFromJsonLogEntry_fromJson___closed__6;
    v___x_4878_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4877_, v___x_4876_);
    return v___x_4878_;
}
pub unsafe fn _init_l_Lake_instFromJsonLogEntry_fromJson___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4879_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instFromJsonLogEntry_fromJson___closed__7),
        core::ptr::addr_of_mut!(l_Lake_instFromJsonLogEntry_fromJson___closed__7_once),
        _init_l_Lake_instFromJsonLogEntry_fromJson___closed__7,
    );
    v___x_4880_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instFromJsonLogEntry_fromJson___closed__5),
        core::ptr::addr_of_mut!(l_Lake_instFromJsonLogEntry_fromJson___closed__5_once),
        _init_l_Lake_instFromJsonLogEntry_fromJson___closed__5,
    );
    v___x_4881_ = lean_string_append(v___x_4880_, v___x_4879_);
    return v___x_4881_;
}
pub unsafe fn _init_l_Lake_instFromJsonLogEntry_fromJson___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4883_ = l_Lake_instFromJsonLogEntry_fromJson___closed__9;
    v___x_4884_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instFromJsonLogEntry_fromJson___closed__8),
        core::ptr::addr_of_mut!(l_Lake_instFromJsonLogEntry_fromJson___closed__8_once),
        _init_l_Lake_instFromJsonLogEntry_fromJson___closed__8,
    );
    v___x_4885_ = lean_string_append(v___x_4884_, v___x_4883_);
    return v___x_4885_;
}
pub unsafe fn _init_l_Lake_instFromJsonLogEntry_fromJson___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4888_: u8 = 0;
    let mut v___x_4889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4888_ = 1;
    v___x_4889_ = l_Lake_instFromJsonLogEntry_fromJson___closed__11;
    v___x_4890_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4889_, v___x_4888_);
    return v___x_4890_;
}
pub unsafe fn _init_l_Lake_instFromJsonLogEntry_fromJson___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4891_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instFromJsonLogEntry_fromJson___closed__12),
        core::ptr::addr_of_mut!(l_Lake_instFromJsonLogEntry_fromJson___closed__12_once),
        _init_l_Lake_instFromJsonLogEntry_fromJson___closed__12,
    );
    v___x_4892_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instFromJsonLogEntry_fromJson___closed__5),
        core::ptr::addr_of_mut!(l_Lake_instFromJsonLogEntry_fromJson___closed__5_once),
        _init_l_Lake_instFromJsonLogEntry_fromJson___closed__5,
    );
    v___x_4893_ = lean_string_append(v___x_4892_, v___x_4891_);
    return v___x_4893_;
}
pub unsafe fn _init_l_Lake_instFromJsonLogEntry_fromJson___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4894_ = l_Lake_instFromJsonLogEntry_fromJson___closed__9;
    v___x_4895_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instFromJsonLogEntry_fromJson___closed__13),
        core::ptr::addr_of_mut!(l_Lake_instFromJsonLogEntry_fromJson___closed__13_once),
        _init_l_Lake_instFromJsonLogEntry_fromJson___closed__13,
    );
    v___x_4896_ = lean_string_append(v___x_4895_, v___x_4894_);
    return v___x_4896_;
}
pub unsafe fn l_Lake_instFromJsonLogEntry_fromJson(
    mut v_json_4897_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4903_: u8 = 0;
    let mut v___x_4904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4909_: u8 = 0;
    let mut v_a_4910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4913_: u8 = 0;
    let mut v___x_4915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4917_: u8 = 0;
    let mut v_a_4918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4924_: u8 = 0;
    let mut v___x_4925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4930_: u8 = 0;
    let mut v_a_4931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4934_: u8 = 0;
    let mut v___x_4936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4938_: u8 = 0;
    let mut v_a_4939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4942_: u8 = 0;
    let mut v___x_4943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4944_: u8 = 0;
    let mut v___x_4946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4948_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4898_ = l_Lake_instToJsonLogEntry_toJson___closed__0;
                crate::leanh::lean_inc(v_json_4897_);
                v___x_4899_ =
                    l_Lean_Json_getObjValAs_x3f___at___00Lake_instFromJsonLogEntry_fromJson_spec__0(
                        v_json_4897_,
                        v___x_4898_,
                    );
                if crate::leanh::lean_obj_tag(v___x_4899_) == 0 {
                    crate::leanh::lean_dec(v_json_4897_);
                    v_a_4900_ = crate::leanh::lean_ctor_get(v___x_4899_, 0);
                    v_isSharedCheck_4909_ = (!crate::leanh::lean_is_exclusive(v___x_4899_)) as u8;
                    if v_isSharedCheck_4909_ == 0 {
                        v___x_4902_ = v___x_4899_;
                        v_isShared_4903_ = v_isSharedCheck_4909_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4900_);
                        crate::leanh::lean_dec(v___x_4899_);
                        v___x_4902_ = crate::leanh::lean_box(0);
                        v_isShared_4903_ = v_isSharedCheck_4909_;
                        state = 1;
                        continue;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v___x_4899_) == 0 {
                        crate::leanh::lean_dec(v_json_4897_);
                        v_a_4910_ = crate::leanh::lean_ctor_get(v___x_4899_, 0);
                        v_isSharedCheck_4917_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4899_)) as u8;
                        if v_isSharedCheck_4917_ == 0 {
                            v___x_4912_ = v___x_4899_;
                            v_isShared_4913_ = v_isSharedCheck_4917_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4910_);
                            crate::leanh::lean_dec(v___x_4899_);
                            v___x_4912_ = crate::leanh::lean_box(0);
                            v_isShared_4913_ = v_isSharedCheck_4917_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_4918_ = crate::leanh::lean_ctor_get(v___x_4899_, 0);
                        crate::leanh::lean_inc(v_a_4918_);
                        crate::leanh::lean_dec_ref_known(v___x_4899_, 1);
                        v___x_4919_ = l_Lake_instToJsonLogEntry_toJson___closed__1;
                        v___x_4920_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_instFromJsonLogEntry_fromJson_spec__1(v_json_4897_, v___x_4919_);
                        if crate::leanh::lean_obj_tag(v___x_4920_) == 0 {
                            crate::leanh::lean_dec(v_a_4918_);
                            v_a_4921_ = crate::leanh::lean_ctor_get(v___x_4920_, 0);
                            v_isSharedCheck_4930_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4920_)) as u8;
                            if v_isSharedCheck_4930_ == 0 {
                                v___x_4923_ = v___x_4920_;
                                v_isShared_4924_ = v_isSharedCheck_4930_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4921_);
                                crate::leanh::lean_dec(v___x_4920_);
                                v___x_4923_ = crate::leanh::lean_box(0);
                                v_isShared_4924_ = v_isSharedCheck_4930_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if crate::leanh::lean_obj_tag(v___x_4920_) == 0 {
                                crate::leanh::lean_dec(v_a_4918_);
                                v_a_4931_ = crate::leanh::lean_ctor_get(v___x_4920_, 0);
                                v_isSharedCheck_4938_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4920_)) as u8;
                                if v_isSharedCheck_4938_ == 0 {
                                    v___x_4933_ = v___x_4920_;
                                    v_isShared_4934_ = v_isSharedCheck_4938_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4931_);
                                    crate::leanh::lean_dec(v___x_4920_);
                                    v___x_4933_ = crate::leanh::lean_box(0);
                                    v_isShared_4934_ = v_isSharedCheck_4938_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_4939_ = crate::leanh::lean_ctor_get(v___x_4920_, 0);
                                v_isSharedCheck_4948_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4920_)) as u8;
                                if v_isSharedCheck_4948_ == 0 {
                                    v___x_4941_ = v___x_4920_;
                                    v_isShared_4942_ = v_isSharedCheck_4948_;
                                    state = 9;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4939_);
                                    crate::leanh::lean_dec(v___x_4920_);
                                    v___x_4941_ = crate::leanh::lean_box(0);
                                    v_isShared_4942_ = v_isSharedCheck_4948_;
                                    state = 9;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_4904_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_instFromJsonLogEntry_fromJson___closed__10),
                    core::ptr::addr_of_mut!(l_Lake_instFromJsonLogEntry_fromJson___closed__10_once),
                    _init_l_Lake_instFromJsonLogEntry_fromJson___closed__10,
                );
                v___x_4905_ = lean_string_append(v___x_4904_, v_a_4900_);
                crate::leanh::lean_dec(v_a_4900_);
                if v_isShared_4903_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4902_, 0, v___x_4905_);
                    v___x_4907_ = v___x_4902_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4908_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4908_, 0, v___x_4905_);
                    v___x_4907_ = v_reuseFailAlloc_4908_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4907_;
            }
            3 => {
                if v_isShared_4913_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4912_, 0);
                    v___x_4915_ = v___x_4912_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4916_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4916_, 0, v_a_4910_);
                    v___x_4915_ = v_reuseFailAlloc_4916_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4915_;
            }
            5 => {
                v___x_4925_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_instFromJsonLogEntry_fromJson___closed__14),
                    core::ptr::addr_of_mut!(l_Lake_instFromJsonLogEntry_fromJson___closed__14_once),
                    _init_l_Lake_instFromJsonLogEntry_fromJson___closed__14,
                );
                v___x_4926_ = lean_string_append(v___x_4925_, v_a_4921_);
                crate::leanh::lean_dec(v_a_4921_);
                if v_isShared_4924_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4923_, 0, v___x_4926_);
                    v___x_4928_ = v___x_4923_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4929_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4929_, 0, v___x_4926_);
                    v___x_4928_ = v_reuseFailAlloc_4929_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4928_;
            }
            7 => {
                if v_isShared_4934_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4933_, 0);
                    v___x_4936_ = v___x_4933_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4937_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4937_, 0, v_a_4931_);
                    v___x_4936_ = v_reuseFailAlloc_4937_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4936_;
            }
            9 => {
                v___x_4943_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4943_, 0, v_a_4939_);
                v___x_4944_ = (crate::leanh::lean_unbox(v_a_4918_) as u8);
                crate::leanh::lean_dec(v_a_4918_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4943_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4944_,
                );
                if v_isShared_4942_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4941_, 0, v___x_4943_);
                    v___x_4946_ = v___x_4941_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4947_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4947_, 0, v___x_4943_);
                    v___x_4946_ = v_reuseFailAlloc_4947_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4946_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LogEntry_toString(
    mut v_self_4953_: *mut crate::leanh::LeanObject,
    mut v_useAnsi_4954_: u8,
) -> *mut crate::leanh::LeanObject {
    if v_useAnsi_4954_ == 0 {
        let mut v_level_4955_: u8 = 0;
        let mut v_message_4956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_level_4955_ = crate::leanh::lean_ctor_get_uint8(
            v_self_4953_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        );
        v_message_4956_ = crate::leanh::lean_ctor_get(v_self_4953_, 0);
        v___x_4957_ = l_Lake_LogLevel_toString(v_level_4955_);
        v___x_4958_ = l_Lake_instFromJsonLogEntry_fromJson___closed__9;
        v___x_4959_ = lean_string_append(v___x_4957_, v___x_4958_);
        v___x_4960_ = lean_string_append(v___x_4959_, v_message_4956_);
        return v___x_4960_;
    } else {
        let mut v_level_4961_: u8 = 0;
        let mut v_message_4962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_pre_4967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_level_4961_ = crate::leanh::lean_ctor_get_uint8(
            v_self_4953_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        );
        v_message_4962_ = crate::leanh::lean_ctor_get(v_self_4953_, 0);
        v___x_4963_ = l_Lake_LogLevel_ansiColor(v_level_4961_);
        v___x_4964_ = l_Lake_LogLevel_toString(v_level_4961_);
        v___x_4965_ = l_Lake_LogEntry_toString___closed__0;
        v___x_4966_ = lean_string_append(v___x_4964_, v___x_4965_);
        v_pre_4967_ = l_Lake_Ansi_chalk(v___x_4963_, v___x_4966_);
        crate::leanh::lean_dec_ref(v___x_4966_);
        crate::leanh::lean_dec_ref(v___x_4963_);
        v___x_4968_ = l_Lake_LogEntry_toString___closed__1;
        v___x_4969_ = lean_string_append(v_pre_4967_, v___x_4968_);
        v___x_4970_ = lean_string_append(v___x_4969_, v_message_4962_);
        return v___x_4970_;
    }
}
pub unsafe fn l_Lake_LogEntry_toString___boxed(
    mut v_self_4971_: *mut crate::leanh::LeanObject,
    mut v_useAnsi_4972_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_useAnsi_boxed_4973_: u8 = 0;
    let mut v_res_4974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_useAnsi_boxed_4973_ = (crate::leanh::lean_unbox(v_useAnsi_4972_) as u8);
    v_res_4974_ = l_Lake_LogEntry_toString(v_self_4971_, v_useAnsi_boxed_4973_);
    crate::leanh::lean_dec_ref(v_self_4971_);
    return v_res_4974_;
}
pub unsafe fn l_Lake_instToStringLogEntry___lam__0(
    mut v_self_4975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4976_: u8 = 0;
    let mut v___x_4977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4976_ = 0;
    v___x_4977_ = l_Lake_LogEntry_toString(v_self_4975_, v___x_4976_);
    return v___x_4977_;
}
pub unsafe fn l_Lake_instToStringLogEntry___lam__0___boxed(
    mut v_self_4978_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4979_ = l_Lake_instToStringLogEntry___lam__0(v_self_4978_);
    crate::leanh::lean_dec_ref(v_self_4978_);
    return v_res_4979_;
}
pub unsafe fn l_Lake_LogEntry_trace(
    mut v_message_4982_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4983_: u8 = 0;
    let mut v___x_4984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4983_ = 0;
    v___x_4984_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_4984_, 0, v_message_4982_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_4984_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_4983_,
    );
    return v___x_4984_;
}
pub unsafe fn l_Lake_LogEntry_info(
    mut v_message_4985_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4986_: u8 = 0;
    let mut v___x_4987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4986_ = 1;
    v___x_4987_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_4987_, 0, v_message_4985_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_4987_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_4986_,
    );
    return v___x_4987_;
}
pub unsafe fn l_Lake_LogEntry_warning(
    mut v_message_4988_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4989_: u8 = 0;
    let mut v___x_4990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4989_ = 2;
    v___x_4990_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_4990_, 0, v_message_4988_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_4990_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_4989_,
    );
    return v___x_4990_;
}
pub unsafe fn l_Lake_LogEntry_error(
    mut v_message_4991_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4992_: u8 = 0;
    let mut v___x_4993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4992_ = 3;
    v___x_4993_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_4993_, 0, v_message_4991_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_4993_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_4992_,
    );
    return v___x_4993_;
}
pub unsafe fn l_Lake_LogEntry_ofSerialMessage(
    mut v_msg_4995_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBaseMessage_4996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_4997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_severity_4999_: u8 = 0;
    let mut v_caption_5000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_5001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5004_: u8 = 0;
    let mut v___x_5005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_5012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_5013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5015_: u8 = 0;
    let mut v___x_5016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5019_: u8 = 0;
    let mut v___x_5020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5029_: u8 = 0;
    let mut v_unused_5030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5035_: u8 = 0;
    let mut v___x_5036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_5040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_5041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_5042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5045_: u8 = 0;
    let mut v_unused_5046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toBaseMessage_4996_ = crate::leanh::lean_ctor_get(v_msg_4995_, 0);
                crate::leanh::lean_inc_ref(v_toBaseMessage_4996_);
                crate::leanh::lean_dec_ref(v_msg_4995_);
                v_fileName_4997_ = crate::leanh::lean_ctor_get(v_toBaseMessage_4996_, 0);
                crate::leanh::lean_inc_ref(v_fileName_4997_);
                v_pos_4998_ = crate::leanh::lean_ctor_get(v_toBaseMessage_4996_, 1);
                crate::leanh::lean_inc_ref(v_pos_4998_);
                v_severity_4999_ = crate::leanh::lean_ctor_get_uint8(
                    v_toBaseMessage_4996_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                );
                v_caption_5000_ = crate::leanh::lean_ctor_get(v_toBaseMessage_4996_, 3);
                crate::leanh::lean_inc_ref(v_caption_5000_);
                v_data_5001_ = crate::leanh::lean_ctor_get(v_toBaseMessage_4996_, 4);
                crate::leanh::lean_inc(v_data_5001_);
                crate::leanh::lean_dec_ref(v_toBaseMessage_4996_);
                v___x_5008_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5009_ = lean_string_utf8_byte_size(v_caption_5000_);
                v___x_5010_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5010_, 0, v_caption_5000_);
                crate::leanh::lean_ctor_set(v___x_5010_, 1, v___x_5008_);
                crate::leanh::lean_ctor_set(v___x_5010_, 2, v___x_5009_);
                v___x_5011_ = l_String_Slice_trimAscii(v___x_5010_);
                v_startInclusive_5012_ = crate::leanh::lean_ctor_get(v___x_5011_, 1);
                crate::leanh::lean_inc(v_startInclusive_5012_);
                v_endExclusive_5013_ = crate::leanh::lean_ctor_get(v___x_5011_, 2);
                crate::leanh::lean_inc(v_endExclusive_5013_);
                v___x_5014_ = lean_nat_sub(v_endExclusive_5013_, v_startInclusive_5012_);
                crate::leanh::lean_dec(v_startInclusive_5012_);
                crate::leanh::lean_dec(v_endExclusive_5013_);
                v___x_5015_ = lean_nat_dec_eq(v___x_5014_, v___x_5008_);
                crate::leanh::lean_dec(v___x_5014_);
                if v___x_5015_ == 0 {
                    v___x_5016_ = l_String_Slice_toString(v___x_5011_);
                    v_isSharedCheck_5029_ = (!crate::leanh::lean_is_exclusive(v___x_5011_)) as u8;
                    if v_isSharedCheck_5029_ == 0 {
                        v_unused_5030_ = crate::leanh::lean_ctor_get(v___x_5011_, 2);
                        crate::leanh::lean_dec(v_unused_5030_);
                        v_unused_5031_ = crate::leanh::lean_ctor_get(v___x_5011_, 1);
                        crate::leanh::lean_dec(v_unused_5031_);
                        v_unused_5032_ = crate::leanh::lean_ctor_get(v___x_5011_, 0);
                        crate::leanh::lean_dec(v_unused_5032_);
                        v___x_5018_ = v___x_5011_;
                        v_isShared_5019_ = v_isSharedCheck_5029_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_5011_);
                        v___x_5018_ = crate::leanh::lean_box(0);
                        v_isShared_5019_ = v_isSharedCheck_5029_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_isSharedCheck_5045_ = (!crate::leanh::lean_is_exclusive(v___x_5011_)) as u8;
                    if v_isSharedCheck_5045_ == 0 {
                        v_unused_5046_ = crate::leanh::lean_ctor_get(v___x_5011_, 2);
                        crate::leanh::lean_dec(v_unused_5046_);
                        v_unused_5047_ = crate::leanh::lean_ctor_get(v___x_5011_, 1);
                        crate::leanh::lean_dec(v_unused_5047_);
                        v_unused_5048_ = crate::leanh::lean_ctor_get(v___x_5011_, 0);
                        crate::leanh::lean_dec(v_unused_5048_);
                        v___x_5034_ = v___x_5011_;
                        v_isShared_5035_ = v_isSharedCheck_5045_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_5011_);
                        v___x_5034_ = crate::leanh::lean_box(0);
                        v_isShared_5035_ = v_isSharedCheck_5045_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5004_ = l_Lake_LogLevel_ofMessageSeverity(v_severity_4999_);
                v___x_5005_ = crate::leanh::lean_box(0);
                v___x_5006_ = l_Lean_mkErrorStringWithPos(
                    v_fileName_4997_,
                    v_pos_4998_,
                    v___y_5003_,
                    v___x_5005_,
                    v___x_5005_,
                    v___x_5005_,
                );
                crate::leanh::lean_dec_ref(v___y_5003_);
                v___x_5007_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_5007_, 0, v___x_5006_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5007_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_5004_,
                );
                return v___x_5007_;
            }
            2 => {
                v___x_5020_ = l_Lake_LogEntry_ofSerialMessage___closed__0;
                v___x_5021_ = lean_string_append(v___x_5016_, v___x_5020_);
                v___x_5022_ = lean_string_utf8_byte_size(v_data_5001_);
                if v_isShared_5019_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5018_, 2, v___x_5022_);
                    crate::leanh::lean_ctor_set(v___x_5018_, 1, v___x_5008_);
                    crate::leanh::lean_ctor_set(v___x_5018_, 0, v_data_5001_);
                    v___x_5024_ = v___x_5018_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5028_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5028_, 0, v_data_5001_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5028_, 1, v___x_5008_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5028_, 2, v___x_5022_);
                    v___x_5024_ = v_reuseFailAlloc_5028_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5025_ = l_String_Slice_trimAscii(v___x_5024_);
                v___x_5026_ = l_String_Slice_toString(v___x_5025_);
                crate::leanh::lean_dec_ref(v___x_5025_);
                v___x_5027_ = lean_string_append(v___x_5021_, v___x_5026_);
                crate::leanh::lean_dec_ref(v___x_5026_);
                v___y_5003_ = v___x_5027_;
                state = 1;
                continue;
            }
            4 => {
                v___x_5036_ = lean_string_utf8_byte_size(v_data_5001_);
                if v_isShared_5035_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5034_, 2, v___x_5036_);
                    crate::leanh::lean_ctor_set(v___x_5034_, 1, v___x_5008_);
                    crate::leanh::lean_ctor_set(v___x_5034_, 0, v_data_5001_);
                    v___x_5038_ = v___x_5034_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5044_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5044_, 0, v_data_5001_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5044_, 1, v___x_5008_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5044_, 2, v___x_5036_);
                    v___x_5038_ = v_reuseFailAlloc_5044_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5039_ = l_String_Slice_trimAscii(v___x_5038_);
                v_str_5040_ = crate::leanh::lean_ctor_get(v___x_5039_, 0);
                crate::leanh::lean_inc_ref(v_str_5040_);
                v_startInclusive_5041_ = crate::leanh::lean_ctor_get(v___x_5039_, 1);
                crate::leanh::lean_inc(v_startInclusive_5041_);
                v_endExclusive_5042_ = crate::leanh::lean_ctor_get(v___x_5039_, 2);
                crate::leanh::lean_inc(v_endExclusive_5042_);
                crate::leanh::lean_dec_ref(v___x_5039_);
                v___x_5043_ = lean_string_utf8_extract(
                    v_str_5040_,
                    v_startInclusive_5041_,
                    v_endExclusive_5042_,
                );
                crate::leanh::lean_dec(v_endExclusive_5042_);
                crate::leanh::lean_dec(v_startInclusive_5041_);
                crate::leanh::lean_dec_ref(v_str_5040_);
                v___y_5003_ = v___x_5043_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LogEntry_ofMessage(
    mut v_msg_5049_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_5051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_5052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_severity_5053_: u8 = 0;
    let mut v_caption_5054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_5055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5059_: u8 = 0;
    let mut v___x_5060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_5067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_5068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5070_: u8 = 0;
    let mut v___x_5071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5074_: u8 = 0;
    let mut v___x_5075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5084_: u8 = 0;
    let mut v_unused_5085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5090_: u8 = 0;
    let mut v___x_5091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_5095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_5096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_5097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5100_: u8 = 0;
    let mut v_unused_5101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_5051_ = crate::leanh::lean_ctor_get(v_msg_5049_, 0);
                crate::leanh::lean_inc_ref(v_fileName_5051_);
                v_pos_5052_ = crate::leanh::lean_ctor_get(v_msg_5049_, 1);
                crate::leanh::lean_inc_ref(v_pos_5052_);
                v_severity_5053_ = crate::leanh::lean_ctor_get_uint8(
                    v_msg_5049_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                );
                v_caption_5054_ = crate::leanh::lean_ctor_get(v_msg_5049_, 3);
                crate::leanh::lean_inc_ref(v_caption_5054_);
                v_data_5055_ = crate::leanh::lean_ctor_get(v_msg_5049_, 4);
                crate::leanh::lean_inc(v_data_5055_);
                crate::leanh::lean_dec_ref(v_msg_5049_);
                v___x_5056_ = l_Lean_MessageData_toString(v_data_5055_);
                v___x_5063_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5064_ = lean_string_utf8_byte_size(v_caption_5054_);
                v___x_5065_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5065_, 0, v_caption_5054_);
                crate::leanh::lean_ctor_set(v___x_5065_, 1, v___x_5063_);
                crate::leanh::lean_ctor_set(v___x_5065_, 2, v___x_5064_);
                v___x_5066_ = l_String_Slice_trimAscii(v___x_5065_);
                v_startInclusive_5067_ = crate::leanh::lean_ctor_get(v___x_5066_, 1);
                crate::leanh::lean_inc(v_startInclusive_5067_);
                v_endExclusive_5068_ = crate::leanh::lean_ctor_get(v___x_5066_, 2);
                crate::leanh::lean_inc(v_endExclusive_5068_);
                v___x_5069_ = lean_nat_sub(v_endExclusive_5068_, v_startInclusive_5067_);
                crate::leanh::lean_dec(v_startInclusive_5067_);
                crate::leanh::lean_dec(v_endExclusive_5068_);
                v___x_5070_ = lean_nat_dec_eq(v___x_5069_, v___x_5063_);
                crate::leanh::lean_dec(v___x_5069_);
                if v___x_5070_ == 0 {
                    v___x_5071_ = l_String_Slice_toString(v___x_5066_);
                    v_isSharedCheck_5084_ = (!crate::leanh::lean_is_exclusive(v___x_5066_)) as u8;
                    if v_isSharedCheck_5084_ == 0 {
                        v_unused_5085_ = crate::leanh::lean_ctor_get(v___x_5066_, 2);
                        crate::leanh::lean_dec(v_unused_5085_);
                        v_unused_5086_ = crate::leanh::lean_ctor_get(v___x_5066_, 1);
                        crate::leanh::lean_dec(v_unused_5086_);
                        v_unused_5087_ = crate::leanh::lean_ctor_get(v___x_5066_, 0);
                        crate::leanh::lean_dec(v_unused_5087_);
                        v___x_5073_ = v___x_5066_;
                        v_isShared_5074_ = v_isSharedCheck_5084_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_5066_);
                        v___x_5073_ = crate::leanh::lean_box(0);
                        v_isShared_5074_ = v_isSharedCheck_5084_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_isSharedCheck_5100_ = (!crate::leanh::lean_is_exclusive(v___x_5066_)) as u8;
                    if v_isSharedCheck_5100_ == 0 {
                        v_unused_5101_ = crate::leanh::lean_ctor_get(v___x_5066_, 2);
                        crate::leanh::lean_dec(v_unused_5101_);
                        v_unused_5102_ = crate::leanh::lean_ctor_get(v___x_5066_, 1);
                        crate::leanh::lean_dec(v_unused_5102_);
                        v_unused_5103_ = crate::leanh::lean_ctor_get(v___x_5066_, 0);
                        crate::leanh::lean_dec(v_unused_5103_);
                        v___x_5089_ = v___x_5066_;
                        v_isShared_5090_ = v_isSharedCheck_5100_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_5066_);
                        v___x_5089_ = crate::leanh::lean_box(0);
                        v_isShared_5090_ = v_isSharedCheck_5100_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5059_ = l_Lake_LogLevel_ofMessageSeverity(v_severity_5053_);
                v___x_5060_ = crate::leanh::lean_box(0);
                v___x_5061_ = l_Lean_mkErrorStringWithPos(
                    v_fileName_5051_,
                    v_pos_5052_,
                    v___y_5058_,
                    v___x_5060_,
                    v___x_5060_,
                    v___x_5060_,
                );
                crate::leanh::lean_dec_ref(v___y_5058_);
                v___x_5062_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_5062_, 0, v___x_5061_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5062_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_5059_,
                );
                return v___x_5062_;
            }
            2 => {
                v___x_5075_ = l_Lake_LogEntry_ofSerialMessage___closed__0;
                v___x_5076_ = lean_string_append(v___x_5071_, v___x_5075_);
                v___x_5077_ = lean_string_utf8_byte_size(v___x_5056_);
                if v_isShared_5074_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5073_, 2, v___x_5077_);
                    crate::leanh::lean_ctor_set(v___x_5073_, 1, v___x_5063_);
                    crate::leanh::lean_ctor_set(v___x_5073_, 0, v___x_5056_);
                    v___x_5079_ = v___x_5073_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5083_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5083_, 0, v___x_5056_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5083_, 1, v___x_5063_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5083_, 2, v___x_5077_);
                    v___x_5079_ = v_reuseFailAlloc_5083_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5080_ = l_String_Slice_trimAscii(v___x_5079_);
                v___x_5081_ = l_String_Slice_toString(v___x_5080_);
                crate::leanh::lean_dec_ref(v___x_5080_);
                v___x_5082_ = lean_string_append(v___x_5076_, v___x_5081_);
                crate::leanh::lean_dec_ref(v___x_5081_);
                v___y_5058_ = v___x_5082_;
                state = 1;
                continue;
            }
            4 => {
                v___x_5091_ = lean_string_utf8_byte_size(v___x_5056_);
                if v_isShared_5090_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5089_, 2, v___x_5091_);
                    crate::leanh::lean_ctor_set(v___x_5089_, 1, v___x_5063_);
                    crate::leanh::lean_ctor_set(v___x_5089_, 0, v___x_5056_);
                    v___x_5093_ = v___x_5089_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5099_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5099_, 0, v___x_5056_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5099_, 1, v___x_5063_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5099_, 2, v___x_5091_);
                    v___x_5093_ = v_reuseFailAlloc_5099_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5094_ = l_String_Slice_trimAscii(v___x_5093_);
                v_str_5095_ = crate::leanh::lean_ctor_get(v___x_5094_, 0);
                crate::leanh::lean_inc_ref(v_str_5095_);
                v_startInclusive_5096_ = crate::leanh::lean_ctor_get(v___x_5094_, 1);
                crate::leanh::lean_inc(v_startInclusive_5096_);
                v_endExclusive_5097_ = crate::leanh::lean_ctor_get(v___x_5094_, 2);
                crate::leanh::lean_inc(v_endExclusive_5097_);
                crate::leanh::lean_dec_ref(v___x_5094_);
                v___x_5098_ = lean_string_utf8_extract(
                    v_str_5095_,
                    v_startInclusive_5096_,
                    v_endExclusive_5097_,
                );
                crate::leanh::lean_dec(v_endExclusive_5097_);
                crate::leanh::lean_dec(v_startInclusive_5096_);
                crate::leanh::lean_dec_ref(v_str_5095_);
                v___y_5058_ = v___x_5098_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LogEntry_ofMessage___boxed(
    mut v_msg_5104_: *mut crate::leanh::LeanObject,
    mut v_a_5105_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5106_ = l_Lake_LogEntry_ofMessage(v_msg_5104_);
    return v_res_5106_;
}
pub unsafe fn l_Lake_logVerbose___redArg(
    mut v_inst_5107_: *mut crate::leanh::LeanObject,
    mut v_message_5108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5109_: u8 = 0;
    let mut v___x_5110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5109_ = 0;
    v___x_5110_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_5110_, 0, v_message_5108_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_5110_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_5109_,
    );
    v___x_5111_ = crate::leanh::lean_apply_1(v_inst_5107_, v___x_5110_);
    return v___x_5111_;
}
pub unsafe fn l_Lake_logVerbose(
    mut v_m_5112_: *mut crate::leanh::LeanObject,
    mut v_inst_5113_: *mut crate::leanh::LeanObject,
    mut v_inst_5114_: *mut crate::leanh::LeanObject,
    mut v_message_5115_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5116_: u8 = 0;
    let mut v___x_5117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5116_ = 0;
    v___x_5117_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_5117_, 0, v_message_5115_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_5117_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_5116_,
    );
    v___x_5118_ = crate::leanh::lean_apply_1(v_inst_5114_, v___x_5117_);
    return v___x_5118_;
}
pub unsafe fn l_Lake_logVerbose___boxed(
    mut v_m_5119_: *mut crate::leanh::LeanObject,
    mut v_inst_5120_: *mut crate::leanh::LeanObject,
    mut v_inst_5121_: *mut crate::leanh::LeanObject,
    mut v_message_5122_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5123_ = l_Lake_logVerbose(v_m_5119_, v_inst_5120_, v_inst_5121_, v_message_5122_);
    crate::leanh::lean_dec_ref(v_inst_5120_);
    return v_res_5123_;
}
pub unsafe fn l_Lake_logInfo___redArg(
    mut v_inst_5124_: *mut crate::leanh::LeanObject,
    mut v_message_5125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5126_: u8 = 0;
    let mut v___x_5127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5126_ = 1;
    v___x_5127_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_5127_, 0, v_message_5125_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_5127_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_5126_,
    );
    v___x_5128_ = crate::leanh::lean_apply_1(v_inst_5124_, v___x_5127_);
    return v___x_5128_;
}
pub unsafe fn l_Lake_logInfo(
    mut v_m_5129_: *mut crate::leanh::LeanObject,
    mut v_inst_5130_: *mut crate::leanh::LeanObject,
    mut v_inst_5131_: *mut crate::leanh::LeanObject,
    mut v_message_5132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5133_: u8 = 0;
    let mut v___x_5134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5133_ = 1;
    v___x_5134_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_5134_, 0, v_message_5132_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_5134_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_5133_,
    );
    v___x_5135_ = crate::leanh::lean_apply_1(v_inst_5131_, v___x_5134_);
    return v___x_5135_;
}
pub unsafe fn l_Lake_logInfo___boxed(
    mut v_m_5136_: *mut crate::leanh::LeanObject,
    mut v_inst_5137_: *mut crate::leanh::LeanObject,
    mut v_inst_5138_: *mut crate::leanh::LeanObject,
    mut v_message_5139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5140_ = l_Lake_logInfo(v_m_5136_, v_inst_5137_, v_inst_5138_, v_message_5139_);
    crate::leanh::lean_dec_ref(v_inst_5137_);
    return v_res_5140_;
}
pub unsafe fn l_Lake_logWarning___redArg(
    mut v_inst_5141_: *mut crate::leanh::LeanObject,
    mut v_message_5142_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5143_: u8 = 0;
    let mut v___x_5144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5143_ = 2;
    v___x_5144_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_5144_, 0, v_message_5142_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_5144_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_5143_,
    );
    v___x_5145_ = crate::leanh::lean_apply_1(v_inst_5141_, v___x_5144_);
    return v___x_5145_;
}
pub unsafe fn l_Lake_logWarning(
    mut v_m_5146_: *mut crate::leanh::LeanObject,
    mut v_inst_5147_: *mut crate::leanh::LeanObject,
    mut v_message_5148_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5149_: u8 = 0;
    let mut v___x_5150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5149_ = 2;
    v___x_5150_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_5150_, 0, v_message_5148_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_5150_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_5149_,
    );
    v___x_5151_ = crate::leanh::lean_apply_1(v_inst_5147_, v___x_5150_);
    return v___x_5151_;
}
pub unsafe fn l_Lake_logError___redArg(
    mut v_inst_5152_: *mut crate::leanh::LeanObject,
    mut v_message_5153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5154_: u8 = 0;
    let mut v___x_5155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5154_ = 3;
    v___x_5155_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_5155_, 0, v_message_5153_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_5155_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_5154_,
    );
    v___x_5156_ = crate::leanh::lean_apply_1(v_inst_5152_, v___x_5155_);
    return v___x_5156_;
}
pub unsafe fn l_Lake_logError(
    mut v_m_5157_: *mut crate::leanh::LeanObject,
    mut v_inst_5158_: *mut crate::leanh::LeanObject,
    mut v_message_5159_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5160_: u8 = 0;
    let mut v___x_5161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5160_ = 3;
    v___x_5161_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_5161_, 0, v_message_5159_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_5161_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_5160_,
    );
    v___x_5162_ = crate::leanh::lean_apply_1(v_inst_5158_, v___x_5161_);
    return v___x_5162_;
}
pub unsafe fn l_Lake_logSerialMessage___redArg(
    mut v_msg_5163_: *mut crate::leanh::LeanObject,
    mut v_inst_5164_: *mut crate::leanh::LeanObject,
    mut v_inst_5165_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBaseMessage_5166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSilent_5167_: u8 = 0;
    v_toBaseMessage_5166_ = crate::leanh::lean_ctor_get(v_msg_5163_, 0);
    v_isSilent_5167_ = crate::leanh::lean_ctor_get_uint8(
        v_toBaseMessage_5166_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 2) as u32,
    );
    if v_isSilent_5167_ == 0 {
        let mut v___x_5168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_inst_5164_);
        v___x_5168_ = l_Lake_LogEntry_ofSerialMessage(v_msg_5163_);
        v___x_5169_ = crate::leanh::lean_apply_1(v_inst_5165_, v___x_5168_);
        return v___x_5169_;
    } else {
        let mut v_toApplicative_5170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_5171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_inst_5165_);
        crate::leanh::lean_dec_ref(v_msg_5163_);
        v_toApplicative_5170_ = crate::leanh::lean_ctor_get(v_inst_5164_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_5170_);
        crate::leanh::lean_dec_ref(v_inst_5164_);
        v_toPure_5171_ = crate::leanh::lean_ctor_get(v_toApplicative_5170_, 1);
        crate::leanh::lean_inc(v_toPure_5171_);
        crate::leanh::lean_dec_ref(v_toApplicative_5170_);
        v___x_5172_ = crate::leanh::lean_box(0);
        v___x_5173_ =
            crate::leanh::lean_apply_2(v_toPure_5171_, crate::leanh::lean_box(0), v___x_5172_);
        return v___x_5173_;
    }
}
pub unsafe fn l_Lake_logSerialMessage(
    mut v_m_5174_: *mut crate::leanh::LeanObject,
    mut v_msg_5175_: *mut crate::leanh::LeanObject,
    mut v_inst_5176_: *mut crate::leanh::LeanObject,
    mut v_inst_5177_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBaseMessage_5178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSilent_5179_: u8 = 0;
    v_toBaseMessage_5178_ = crate::leanh::lean_ctor_get(v_msg_5175_, 0);
    v_isSilent_5179_ = crate::leanh::lean_ctor_get_uint8(
        v_toBaseMessage_5178_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 2) as u32,
    );
    if v_isSilent_5179_ == 0 {
        let mut v___x_5180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_inst_5176_);
        v___x_5180_ = l_Lake_LogEntry_ofSerialMessage(v_msg_5175_);
        v___x_5181_ = crate::leanh::lean_apply_1(v_inst_5177_, v___x_5180_);
        return v___x_5181_;
    } else {
        let mut v_toApplicative_5182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_5183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_inst_5177_);
        crate::leanh::lean_dec_ref(v_msg_5175_);
        v_toApplicative_5182_ = crate::leanh::lean_ctor_get(v_inst_5176_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_5182_);
        crate::leanh::lean_dec_ref(v_inst_5176_);
        v_toPure_5183_ = crate::leanh::lean_ctor_get(v_toApplicative_5182_, 1);
        crate::leanh::lean_inc(v_toPure_5183_);
        crate::leanh::lean_dec_ref(v_toApplicative_5182_);
        v___x_5184_ = crate::leanh::lean_box(0);
        v___x_5185_ =
            crate::leanh::lean_apply_2(v_toPure_5183_, crate::leanh::lean_box(0), v___x_5184_);
        return v___x_5185_;
    }
}
pub unsafe fn l_Lake_logMessage___redArg___lam__0(
    mut v_inst_5186_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5187_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5188_ = crate::leanh::lean_apply_1(v_inst_5186_, v_____do__lift_5187_);
    return v___x_5188_;
}
pub unsafe fn l_Lake_logMessage___redArg(
    mut v_msg_5189_: *mut crate::leanh::LeanObject,
    mut v_inst_5190_: *mut crate::leanh::LeanObject,
    mut v_inst_5191_: *mut crate::leanh::LeanObject,
    mut v_inst_5192_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isSilent_5193_: u8 = 0;
    v_isSilent_5193_ = crate::leanh::lean_ctor_get_uint8(
        v_msg_5189_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 2) as u32,
    );
    if v_isSilent_5193_ == 0 {
        let mut v_toBind_5194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_5195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toBind_5194_ = crate::leanh::lean_ctor_get(v_inst_5190_, 1);
        crate::leanh::lean_inc(v_toBind_5194_);
        crate::leanh::lean_dec_ref(v_inst_5190_);
        v___f_5195_ = crate::leanh::lean_alloc_closure(
            l_Lake_logMessage___redArg___lam__0 as *mut core::ffi::c_void,
            2,
            1,
        );
        crate::leanh::lean_closure_set(v___f_5195_, 0, v_inst_5191_);
        v___x_5196_ = crate::leanh::lean_alloc_closure(
            l_Lake_LogEntry_ofMessage___boxed as *mut core::ffi::c_void,
            2,
            1,
        );
        crate::leanh::lean_closure_set(v___x_5196_, 0, v_msg_5189_);
        v___x_5197_ =
            crate::leanh::lean_apply_2(v_inst_5192_, crate::leanh::lean_box(0), v___x_5196_);
        v___x_5198_ = crate::leanh::lean_apply_4(
            v_toBind_5194_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_5197_,
            v___f_5195_,
        );
        return v___x_5198_;
    } else {
        let mut v_toApplicative_5199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_5200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_inst_5192_);
        crate::leanh::lean_dec(v_inst_5191_);
        crate::leanh::lean_dec_ref(v_msg_5189_);
        v_toApplicative_5199_ = crate::leanh::lean_ctor_get(v_inst_5190_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_5199_);
        crate::leanh::lean_dec_ref(v_inst_5190_);
        v_toPure_5200_ = crate::leanh::lean_ctor_get(v_toApplicative_5199_, 1);
        crate::leanh::lean_inc(v_toPure_5200_);
        crate::leanh::lean_dec_ref(v_toApplicative_5199_);
        v___x_5201_ = crate::leanh::lean_box(0);
        v___x_5202_ =
            crate::leanh::lean_apply_2(v_toPure_5200_, crate::leanh::lean_box(0), v___x_5201_);
        return v___x_5202_;
    }
}
pub unsafe fn l_Lake_logMessage(
    mut v_m_5203_: *mut crate::leanh::LeanObject,
    mut v_msg_5204_: *mut crate::leanh::LeanObject,
    mut v_inst_5205_: *mut crate::leanh::LeanObject,
    mut v_inst_5206_: *mut crate::leanh::LeanObject,
    mut v_inst_5207_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isSilent_5208_: u8 = 0;
    v_isSilent_5208_ = crate::leanh::lean_ctor_get_uint8(
        v_msg_5204_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 2) as u32,
    );
    if v_isSilent_5208_ == 0 {
        let mut v_toBind_5209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_5210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toBind_5209_ = crate::leanh::lean_ctor_get(v_inst_5205_, 1);
        crate::leanh::lean_inc(v_toBind_5209_);
        crate::leanh::lean_dec_ref(v_inst_5205_);
        v___f_5210_ = crate::leanh::lean_alloc_closure(
            l_Lake_logMessage___redArg___lam__0 as *mut core::ffi::c_void,
            2,
            1,
        );
        crate::leanh::lean_closure_set(v___f_5210_, 0, v_inst_5206_);
        v___x_5211_ = crate::leanh::lean_alloc_closure(
            l_Lake_LogEntry_ofMessage___boxed as *mut core::ffi::c_void,
            2,
            1,
        );
        crate::leanh::lean_closure_set(v___x_5211_, 0, v_msg_5204_);
        v___x_5212_ =
            crate::leanh::lean_apply_2(v_inst_5207_, crate::leanh::lean_box(0), v___x_5211_);
        v___x_5213_ = crate::leanh::lean_apply_4(
            v_toBind_5209_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_5212_,
            v___f_5210_,
        );
        return v___x_5213_;
    } else {
        let mut v_toApplicative_5214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_5215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_inst_5207_);
        crate::leanh::lean_dec(v_inst_5206_);
        crate::leanh::lean_dec_ref(v_msg_5204_);
        v_toApplicative_5214_ = crate::leanh::lean_ctor_get(v_inst_5205_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_5214_);
        crate::leanh::lean_dec_ref(v_inst_5205_);
        v_toPure_5215_ = crate::leanh::lean_ctor_get(v_toApplicative_5214_, 1);
        crate::leanh::lean_inc(v_toPure_5215_);
        crate::leanh::lean_dec_ref(v_toApplicative_5214_);
        v___x_5216_ = crate::leanh::lean_box(0);
        v___x_5217_ =
            crate::leanh::lean_apply_2(v_toPure_5215_, crate::leanh::lean_box(0), v___x_5216_);
        return v___x_5217_;
    }
}
pub unsafe fn l_Lake_logToStream(
    mut v_e_5218_: *mut crate::leanh::LeanObject,
    mut v_out_5219_: *mut crate::leanh::LeanObject,
    mut v_minLv_5220_: u8,
    mut v_useAnsi_5221_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_level_5223_: u8 = 0;
    let mut v___x_5224_: u8 = 0;
    v_level_5223_ = crate::leanh::lean_ctor_get_uint8(
        v_e_5218_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
    );
    v___x_5224_ = l_Lake_instOrdLogLevel_ord(v_minLv_5220_, v_level_5223_);
    if v___x_5224_ == 2 {
        let mut v___x_5225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_out_5219_);
        v___x_5225_ = crate::leanh::lean_box(0);
        return v___x_5225_;
    } else {
        let mut v___x_5226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5226_ = l_Lake_LogEntry_toString(v_e_5218_, v_useAnsi_5221_);
        v___x_5227_ = l_IO_FS_Stream_putStrLn(v_out_5219_, v___x_5226_);
        if crate::leanh::lean_obj_tag(v___x_5227_) == 0 {
            let mut v_a_5228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_5228_ = crate::leanh::lean_ctor_get(v___x_5227_, 0);
            crate::leanh::lean_inc(v_a_5228_);
            crate::leanh::lean_dec_ref_known(v___x_5227_, 1);
            return v_a_5228_;
        } else {
            let mut v___x_5229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref_known(v___x_5227_, 1);
            v___x_5229_ = crate::leanh::lean_box(0);
            return v___x_5229_;
        }
    }
}
pub unsafe fn l_Lake_logToStream___boxed(
    mut v_e_5230_: *mut crate::leanh::LeanObject,
    mut v_out_5231_: *mut crate::leanh::LeanObject,
    mut v_minLv_5232_: *mut crate::leanh::LeanObject,
    mut v_useAnsi_5233_: *mut crate::leanh::LeanObject,
    mut v_a_5234_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_minLv_boxed_5235_: u8 = 0;
    let mut v_useAnsi_boxed_5236_: u8 = 0;
    let mut v_res_5237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_minLv_boxed_5235_ = (crate::leanh::lean_unbox(v_minLv_5232_) as u8);
    v_useAnsi_boxed_5236_ = (crate::leanh::lean_unbox(v_useAnsi_5233_) as u8);
    v_res_5237_ = l_Lake_logToStream(
        v_e_5230_,
        v_out_5231_,
        v_minLv_boxed_5235_,
        v_useAnsi_boxed_5236_,
    );
    crate::leanh::lean_dec_ref(v_e_5230_);
    return v_res_5237_;
}
pub unsafe fn l_Lake_MonadLog_nop___redArg___lam__0(
    mut v_inst_5238_: *mut crate::leanh::LeanObject,
    mut v_x_5239_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5240_ = crate::leanh::lean_box(0);
    v___x_5241_ = crate::leanh::lean_apply_2(v_inst_5238_, crate::leanh::lean_box(0), v___x_5240_);
    return v___x_5241_;
}
pub unsafe fn l_Lake_MonadLog_nop___redArg___lam__0___boxed(
    mut v_inst_5242_: *mut crate::leanh::LeanObject,
    mut v_x_5243_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5244_ = l_Lake_MonadLog_nop___redArg___lam__0(v_inst_5242_, v_x_5243_);
    crate::leanh::lean_dec_ref(v_x_5243_);
    return v_res_5244_;
}
pub unsafe fn l_Lake_MonadLog_nop___redArg(
    mut v_inst_5245_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5246_ = crate::leanh::lean_alloc_closure(
        l_Lake_MonadLog_nop___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5246_, 0, v_inst_5245_);
    return v___f_5246_;
}
pub unsafe fn l_Lake_MonadLog_nop(
    mut v_m_5247_: *mut crate::leanh::LeanObject,
    mut v_inst_5248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5249_ = crate::leanh::lean_alloc_closure(
        l_Lake_MonadLog_nop___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5249_, 0, v_inst_5248_);
    return v___f_5249_;
}
pub unsafe fn l_Lake_MonadLog_instInhabitedOfPure___redArg(
    mut v_inst_5250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5251_ = crate::leanh::lean_alloc_closure(
        l_Lake_MonadLog_nop___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5251_, 0, v_inst_5250_);
    return v___f_5251_;
}
pub unsafe fn l_Lake_MonadLog_instInhabitedOfPure(
    mut v_m_5252_: *mut crate::leanh::LeanObject,
    mut v_inst_5253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5254_ = crate::leanh::lean_alloc_closure(
        l_Lake_MonadLog_nop___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5254_, 0, v_inst_5253_);
    return v___f_5254_;
}
pub unsafe fn l_Lake_MonadLog_lift___redArg___lam__0(
    mut v_self_5255_: *mut crate::leanh::LeanObject,
    mut v_inst_5256_: *mut crate::leanh::LeanObject,
    mut v_e_5257_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5258_ = crate::leanh::lean_apply_1(v_self_5255_, v_e_5257_);
    v___x_5259_ = crate::leanh::lean_apply_2(v_inst_5256_, crate::leanh::lean_box(0), v___x_5258_);
    return v___x_5259_;
}
pub unsafe fn l_Lake_MonadLog_lift___redArg(
    mut v_inst_5260_: *mut crate::leanh::LeanObject,
    mut v_self_5261_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5262_ = crate::leanh::lean_alloc_closure(
        l_Lake_MonadLog_lift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_5262_, 0, v_self_5261_);
    crate::leanh::lean_closure_set(v___f_5262_, 1, v_inst_5260_);
    return v___f_5262_;
}
pub unsafe fn l_Lake_MonadLog_lift(
    mut v_m_5263_: *mut crate::leanh::LeanObject,
    mut v_n_5264_: *mut crate::leanh::LeanObject,
    mut v_inst_5265_: *mut crate::leanh::LeanObject,
    mut v_self_5266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5267_ = crate::leanh::lean_alloc_closure(
        l_Lake_MonadLog_lift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_5267_, 0, v_self_5266_);
    crate::leanh::lean_closure_set(v___f_5267_, 1, v_inst_5265_);
    return v___f_5267_;
}
pub unsafe fn l_Lake_MonadLog_instOfMonadLift___redArg___lam__0(
    mut v_methods_5268_: *mut crate::leanh::LeanObject,
    mut v_inst_5269_: *mut crate::leanh::LeanObject,
    mut v_e_5270_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5271_ = crate::leanh::lean_apply_1(v_methods_5268_, v_e_5270_);
    v___x_5272_ = crate::leanh::lean_apply_2(v_inst_5269_, crate::leanh::lean_box(0), v___x_5271_);
    return v___x_5272_;
}
pub unsafe fn l_Lake_MonadLog_instOfMonadLift___redArg(
    mut v_inst_5273_: *mut crate::leanh::LeanObject,
    mut v_methods_5274_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5275_ = crate::leanh::lean_alloc_closure(
        l_Lake_MonadLog_instOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_5275_, 0, v_methods_5274_);
    crate::leanh::lean_closure_set(v___f_5275_, 1, v_inst_5273_);
    return v___f_5275_;
}
pub unsafe fn l_Lake_MonadLog_instOfMonadLift(
    mut v_m_5276_: *mut crate::leanh::LeanObject,
    mut v_n_5277_: *mut crate::leanh::LeanObject,
    mut v_inst_5278_: *mut crate::leanh::LeanObject,
    mut v_methods_5279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5280_ = crate::leanh::lean_alloc_closure(
        l_Lake_MonadLog_instOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_5280_, 0, v_methods_5279_);
    crate::leanh::lean_closure_set(v___f_5280_, 1, v_inst_5278_);
    return v___f_5280_;
}
pub unsafe fn l_Lake_MonadLog_stream___redArg___lam__0(
    mut v_out_5281_: *mut crate::leanh::LeanObject,
    mut v_minLv_5282_: u8,
    mut v_useAnsi_5283_: u8,
    mut v_inst_5284_: *mut crate::leanh::LeanObject,
    mut v_e_5285_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5286_ = crate::leanh::lean_box((v_minLv_5282_) as usize);
    v___x_5287_ = crate::leanh::lean_box((v_useAnsi_5283_) as usize);
    v___x_5288_ = crate::leanh::lean_alloc_closure(
        l_Lake_logToStream___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___x_5288_, 0, v_e_5285_);
    crate::leanh::lean_closure_set(v___x_5288_, 1, v_out_5281_);
    crate::leanh::lean_closure_set(v___x_5288_, 2, v___x_5286_);
    crate::leanh::lean_closure_set(v___x_5288_, 3, v___x_5287_);
    v___x_5289_ = crate::leanh::lean_apply_2(v_inst_5284_, crate::leanh::lean_box(0), v___x_5288_);
    return v___x_5289_;
}
pub unsafe fn l_Lake_MonadLog_stream___redArg___lam__0___boxed(
    mut v_out_5290_: *mut crate::leanh::LeanObject,
    mut v_minLv_5291_: *mut crate::leanh::LeanObject,
    mut v_useAnsi_5292_: *mut crate::leanh::LeanObject,
    mut v_inst_5293_: *mut crate::leanh::LeanObject,
    mut v_e_5294_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_minLv_boxed_5295_: u8 = 0;
    let mut v_useAnsi_boxed_5296_: u8 = 0;
    let mut v_res_5297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_minLv_boxed_5295_ = (crate::leanh::lean_unbox(v_minLv_5291_) as u8);
    v_useAnsi_boxed_5296_ = (crate::leanh::lean_unbox(v_useAnsi_5292_) as u8);
    v_res_5297_ = l_Lake_MonadLog_stream___redArg___lam__0(
        v_out_5290_,
        v_minLv_boxed_5295_,
        v_useAnsi_boxed_5296_,
        v_inst_5293_,
        v_e_5294_,
    );
    return v_res_5297_;
}
pub unsafe fn l_Lake_MonadLog_stream___redArg(
    mut v_inst_5298_: *mut crate::leanh::LeanObject,
    mut v_out_5299_: *mut crate::leanh::LeanObject,
    mut v_minLv_5300_: u8,
    mut v_useAnsi_5301_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5302_ = crate::leanh::lean_box((v_minLv_5300_) as usize);
    v___x_5303_ = crate::leanh::lean_box((v_useAnsi_5301_) as usize);
    v___f_5304_ = crate::leanh::lean_alloc_closure(
        l_Lake_MonadLog_stream___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_5304_, 0, v_out_5299_);
    crate::leanh::lean_closure_set(v___f_5304_, 1, v___x_5302_);
    crate::leanh::lean_closure_set(v___f_5304_, 2, v___x_5303_);
    crate::leanh::lean_closure_set(v___f_5304_, 3, v_inst_5298_);
    return v___f_5304_;
}
pub unsafe fn l_Lake_MonadLog_stream___redArg___boxed(
    mut v_inst_5305_: *mut crate::leanh::LeanObject,
    mut v_out_5306_: *mut crate::leanh::LeanObject,
    mut v_minLv_5307_: *mut crate::leanh::LeanObject,
    mut v_useAnsi_5308_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_minLv_boxed_5309_: u8 = 0;
    let mut v_useAnsi_boxed_5310_: u8 = 0;
    let mut v_res_5311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_minLv_boxed_5309_ = (crate::leanh::lean_unbox(v_minLv_5307_) as u8);
    v_useAnsi_boxed_5310_ = (crate::leanh::lean_unbox(v_useAnsi_5308_) as u8);
    v_res_5311_ = l_Lake_MonadLog_stream___redArg(
        v_inst_5305_,
        v_out_5306_,
        v_minLv_boxed_5309_,
        v_useAnsi_boxed_5310_,
    );
    return v_res_5311_;
}
pub unsafe fn l_Lake_MonadLog_stream(
    mut v_m_5312_: *mut crate::leanh::LeanObject,
    mut v_inst_5313_: *mut crate::leanh::LeanObject,
    mut v_out_5314_: *mut crate::leanh::LeanObject,
    mut v_minLv_5315_: u8,
    mut v_useAnsi_5316_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5317_ = crate::leanh::lean_box((v_minLv_5315_) as usize);
    v___x_5318_ = crate::leanh::lean_box((v_useAnsi_5316_) as usize);
    v___f_5319_ = crate::leanh::lean_alloc_closure(
        l_Lake_MonadLog_stream___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_5319_, 0, v_out_5314_);
    crate::leanh::lean_closure_set(v___f_5319_, 1, v___x_5317_);
    crate::leanh::lean_closure_set(v___f_5319_, 2, v___x_5318_);
    crate::leanh::lean_closure_set(v___f_5319_, 3, v_inst_5313_);
    return v___f_5319_;
}
pub unsafe fn l_Lake_MonadLog_stream___boxed(
    mut v_m_5320_: *mut crate::leanh::LeanObject,
    mut v_inst_5321_: *mut crate::leanh::LeanObject,
    mut v_out_5322_: *mut crate::leanh::LeanObject,
    mut v_minLv_5323_: *mut crate::leanh::LeanObject,
    mut v_useAnsi_5324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_minLv_boxed_5325_: u8 = 0;
    let mut v_useAnsi_boxed_5326_: u8 = 0;
    let mut v_res_5327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_minLv_boxed_5325_ = (crate::leanh::lean_unbox(v_minLv_5323_) as u8);
    v_useAnsi_boxed_5326_ = (crate::leanh::lean_unbox(v_useAnsi_5324_) as u8);
    v_res_5327_ = l_Lake_MonadLog_stream(
        v_m_5320_,
        v_inst_5321_,
        v_out_5322_,
        v_minLv_boxed_5325_,
        v_useAnsi_boxed_5326_,
    );
    return v_res_5327_;
}
pub unsafe fn l_Lake_MonadLog_error___redArg___lam__0(
    mut v_failure_5328_: *mut crate::leanh::LeanObject,
    mut v_x_5329_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5330_ = crate::leanh::lean_apply_1(v_failure_5328_, crate::leanh::lean_box(0));
    return v___x_5330_;
}
pub unsafe fn l_Lake_MonadLog_error___redArg(
    mut v_inst_5331_: *mut crate::leanh::LeanObject,
    mut v_inst_5332_: *mut crate::leanh::LeanObject,
    mut v_msg_5333_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_5334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_failure_5335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_5336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5338_: u8 = 0;
    let mut v___x_5339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_5334_ = crate::leanh::lean_ctor_get(v_inst_5331_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_5334_);
    v_failure_5335_ = crate::leanh::lean_ctor_get(v_inst_5331_, 1);
    crate::leanh::lean_inc(v_failure_5335_);
    crate::leanh::lean_dec_ref(v_inst_5331_);
    v_toSeqRight_5336_ = crate::leanh::lean_ctor_get(v_toApplicative_5334_, 4);
    crate::leanh::lean_inc(v_toSeqRight_5336_);
    crate::leanh::lean_dec_ref(v_toApplicative_5334_);
    v___f_5337_ = crate::leanh::lean_alloc_closure(
        l_Lake_MonadLog_error___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5337_, 0, v_failure_5335_);
    v___x_5338_ = 3;
    v___x_5339_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_5339_, 0, v_msg_5333_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_5339_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_5338_,
    );
    v___x_5340_ = crate::leanh::lean_apply_1(v_inst_5332_, v___x_5339_);
    v___x_5341_ = crate::leanh::lean_apply_4(
        v_toSeqRight_5336_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5340_,
        v___f_5337_,
    );
    return v___x_5341_;
}
pub unsafe fn l_Lake_MonadLog_error(
    mut v_m_5342_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_5343_: *mut crate::leanh::LeanObject,
    mut v_inst_5344_: *mut crate::leanh::LeanObject,
    mut v_inst_5345_: *mut crate::leanh::LeanObject,
    mut v_msg_5346_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_5347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_failure_5348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_5349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5351_: u8 = 0;
    let mut v___x_5352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_5347_ = crate::leanh::lean_ctor_get(v_inst_5344_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_5347_);
    v_failure_5348_ = crate::leanh::lean_ctor_get(v_inst_5344_, 1);
    crate::leanh::lean_inc(v_failure_5348_);
    crate::leanh::lean_dec_ref(v_inst_5344_);
    v_toSeqRight_5349_ = crate::leanh::lean_ctor_get(v_toApplicative_5347_, 4);
    crate::leanh::lean_inc(v_toSeqRight_5349_);
    crate::leanh::lean_dec_ref(v_toApplicative_5347_);
    v___f_5350_ = crate::leanh::lean_alloc_closure(
        l_Lake_MonadLog_error___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5350_, 0, v_failure_5348_);
    v___x_5351_ = 3;
    v___x_5352_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_5352_, 0, v_msg_5346_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_5352_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_5351_,
    );
    v___x_5353_ = crate::leanh::lean_apply_1(v_inst_5345_, v___x_5352_);
    v___x_5354_ = crate::leanh::lean_apply_4(
        v_toSeqRight_5349_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5353_,
        v___f_5350_,
    );
    return v___x_5354_;
}
pub unsafe fn l_Lake_OutStream_logEntry(
    mut v_self_5355_: *mut crate::leanh::LeanObject,
    mut v_e_5356_: *mut crate::leanh::LeanObject,
    mut v_minLv_5357_: u8,
    mut v_ansiMode_5358_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5361_: u8 = 0;
    let mut v___x_5362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5360_ = l_Lake_OutStream_get(v_self_5355_);
    crate::leanh::lean_inc_ref(v___x_5360_);
    v___x_5361_ = l_Lake_AnsiMode_isEnabled(v___x_5360_, v_ansiMode_5358_);
    v___x_5362_ = l_Lake_logToStream(v_e_5356_, v___x_5360_, v_minLv_5357_, v___x_5361_);
    return v___x_5362_;
}
pub unsafe fn l_Lake_OutStream_logEntry___boxed(
    mut v_self_5363_: *mut crate::leanh::LeanObject,
    mut v_e_5364_: *mut crate::leanh::LeanObject,
    mut v_minLv_5365_: *mut crate::leanh::LeanObject,
    mut v_ansiMode_5366_: *mut crate::leanh::LeanObject,
    mut v_a_5367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_minLv_boxed_5368_: u8 = 0;
    let mut v_ansiMode_boxed_5369_: u8 = 0;
    let mut v_res_5370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_minLv_boxed_5368_ = (crate::leanh::lean_unbox(v_minLv_5365_) as u8);
    v_ansiMode_boxed_5369_ = (crate::leanh::lean_unbox(v_ansiMode_5366_) as u8);
    v_res_5370_ = l_Lake_OutStream_logEntry(
        v_self_5363_,
        v_e_5364_,
        v_minLv_boxed_5368_,
        v_ansiMode_boxed_5369_,
    );
    crate::leanh::lean_dec_ref(v_e_5364_);
    crate::leanh::lean_dec(v_self_5363_);
    return v_res_5370_;
}
pub unsafe fn l_Lake_OutStream_logger___redArg___lam__0(
    mut v_out_5371_: *mut crate::leanh::LeanObject,
    mut v_minLv_5372_: u8,
    mut v_ansiMode_5373_: u8,
    mut v_inst_5374_: *mut crate::leanh::LeanObject,
    mut v_e_5375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5376_ = crate::leanh::lean_box((v_minLv_5372_) as usize);
    v___x_5377_ = crate::leanh::lean_box((v_ansiMode_5373_) as usize);
    v___x_5378_ = crate::leanh::lean_alloc_closure(
        l_Lake_OutStream_logEntry___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___x_5378_, 0, v_out_5371_);
    crate::leanh::lean_closure_set(v___x_5378_, 1, v_e_5375_);
    crate::leanh::lean_closure_set(v___x_5378_, 2, v___x_5376_);
    crate::leanh::lean_closure_set(v___x_5378_, 3, v___x_5377_);
    v___x_5379_ = crate::leanh::lean_apply_2(v_inst_5374_, crate::leanh::lean_box(0), v___x_5378_);
    return v___x_5379_;
}
pub unsafe fn l_Lake_OutStream_logger___redArg___lam__0___boxed(
    mut v_out_5380_: *mut crate::leanh::LeanObject,
    mut v_minLv_5381_: *mut crate::leanh::LeanObject,
    mut v_ansiMode_5382_: *mut crate::leanh::LeanObject,
    mut v_inst_5383_: *mut crate::leanh::LeanObject,
    mut v_e_5384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_minLv_boxed_5385_: u8 = 0;
    let mut v_ansiMode_boxed_5386_: u8 = 0;
    let mut v_res_5387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_minLv_boxed_5385_ = (crate::leanh::lean_unbox(v_minLv_5381_) as u8);
    v_ansiMode_boxed_5386_ = (crate::leanh::lean_unbox(v_ansiMode_5382_) as u8);
    v_res_5387_ = l_Lake_OutStream_logger___redArg___lam__0(
        v_out_5380_,
        v_minLv_boxed_5385_,
        v_ansiMode_boxed_5386_,
        v_inst_5383_,
        v_e_5384_,
    );
    return v_res_5387_;
}
pub unsafe fn l_Lake_OutStream_logger___redArg(
    mut v_inst_5388_: *mut crate::leanh::LeanObject,
    mut v_out_5389_: *mut crate::leanh::LeanObject,
    mut v_minLv_5390_: u8,
    mut v_ansiMode_5391_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5392_ = crate::leanh::lean_box((v_minLv_5390_) as usize);
    v___x_5393_ = crate::leanh::lean_box((v_ansiMode_5391_) as usize);
    v___f_5394_ = crate::leanh::lean_alloc_closure(
        l_Lake_OutStream_logger___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_5394_, 0, v_out_5389_);
    crate::leanh::lean_closure_set(v___f_5394_, 1, v___x_5392_);
    crate::leanh::lean_closure_set(v___f_5394_, 2, v___x_5393_);
    crate::leanh::lean_closure_set(v___f_5394_, 3, v_inst_5388_);
    return v___f_5394_;
}
pub unsafe fn l_Lake_OutStream_logger___redArg___boxed(
    mut v_inst_5395_: *mut crate::leanh::LeanObject,
    mut v_out_5396_: *mut crate::leanh::LeanObject,
    mut v_minLv_5397_: *mut crate::leanh::LeanObject,
    mut v_ansiMode_5398_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_minLv_boxed_5399_: u8 = 0;
    let mut v_ansiMode_boxed_5400_: u8 = 0;
    let mut v_res_5401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_minLv_boxed_5399_ = (crate::leanh::lean_unbox(v_minLv_5397_) as u8);
    v_ansiMode_boxed_5400_ = (crate::leanh::lean_unbox(v_ansiMode_5398_) as u8);
    v_res_5401_ = l_Lake_OutStream_logger___redArg(
        v_inst_5395_,
        v_out_5396_,
        v_minLv_boxed_5399_,
        v_ansiMode_boxed_5400_,
    );
    return v_res_5401_;
}
pub unsafe fn l_Lake_OutStream_logger(
    mut v_m_5402_: *mut crate::leanh::LeanObject,
    mut v_inst_5403_: *mut crate::leanh::LeanObject,
    mut v_out_5404_: *mut crate::leanh::LeanObject,
    mut v_minLv_5405_: u8,
    mut v_ansiMode_5406_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5407_ = crate::leanh::lean_box((v_minLv_5405_) as usize);
    v___x_5408_ = crate::leanh::lean_box((v_ansiMode_5406_) as usize);
    v___f_5409_ = crate::leanh::lean_alloc_closure(
        l_Lake_OutStream_logger___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_5409_, 0, v_out_5404_);
    crate::leanh::lean_closure_set(v___f_5409_, 1, v___x_5407_);
    crate::leanh::lean_closure_set(v___f_5409_, 2, v___x_5408_);
    crate::leanh::lean_closure_set(v___f_5409_, 3, v_inst_5403_);
    return v___f_5409_;
}
pub unsafe fn l_Lake_OutStream_logger___boxed(
    mut v_m_5410_: *mut crate::leanh::LeanObject,
    mut v_inst_5411_: *mut crate::leanh::LeanObject,
    mut v_out_5412_: *mut crate::leanh::LeanObject,
    mut v_minLv_5413_: *mut crate::leanh::LeanObject,
    mut v_ansiMode_5414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_minLv_boxed_5415_: u8 = 0;
    let mut v_ansiMode_boxed_5416_: u8 = 0;
    let mut v_res_5417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_minLv_boxed_5415_ = (crate::leanh::lean_unbox(v_minLv_5413_) as u8);
    v_ansiMode_boxed_5416_ = (crate::leanh::lean_unbox(v_ansiMode_5414_) as u8);
    v_res_5417_ = l_Lake_OutStream_logger(
        v_m_5410_,
        v_inst_5411_,
        v_out_5412_,
        v_minLv_boxed_5415_,
        v_ansiMode_boxed_5416_,
    );
    return v_res_5417_;
}
pub unsafe fn l_Lake_MonadLog_stdout___redArg___lam__0(
    mut v___x_5418_: *mut crate::leanh::LeanObject,
    mut v_minLv_5419_: u8,
    mut v_ansiMode_5420_: u8,
    mut v_inst_5421_: *mut crate::leanh::LeanObject,
    mut v_e_5422_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5423_ = crate::leanh::lean_box((v_minLv_5419_) as usize);
    v___x_5424_ = crate::leanh::lean_box((v_ansiMode_5420_) as usize);
    v___x_5425_ = crate::leanh::lean_alloc_closure(
        l_Lake_OutStream_logEntry___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___x_5425_, 0, v___x_5418_);
    crate::leanh::lean_closure_set(v___x_5425_, 1, v_e_5422_);
    crate::leanh::lean_closure_set(v___x_5425_, 2, v___x_5423_);
    crate::leanh::lean_closure_set(v___x_5425_, 3, v___x_5424_);
    v___x_5426_ = crate::leanh::lean_apply_2(v_inst_5421_, crate::leanh::lean_box(0), v___x_5425_);
    return v___x_5426_;
}
pub unsafe fn l_Lake_MonadLog_stdout___redArg___lam__0___boxed(
    mut v___x_5427_: *mut crate::leanh::LeanObject,
    mut v_minLv_5428_: *mut crate::leanh::LeanObject,
    mut v_ansiMode_5429_: *mut crate::leanh::LeanObject,
    mut v_inst_5430_: *mut crate::leanh::LeanObject,
    mut v_e_5431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_minLv_boxed_5432_: u8 = 0;
    let mut v_ansiMode_boxed_5433_: u8 = 0;
    let mut v_res_5434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_minLv_boxed_5432_ = (crate::leanh::lean_unbox(v_minLv_5428_) as u8);
    v_ansiMode_boxed_5433_ = (crate::leanh::lean_unbox(v_ansiMode_5429_) as u8);
    v_res_5434_ = l_Lake_MonadLog_stdout___redArg___lam__0(
        v___x_5427_,
        v_minLv_boxed_5432_,
        v_ansiMode_boxed_5433_,
        v_inst_5430_,
        v_e_5431_,
    );
    return v_res_5434_;
}
pub unsafe fn l_Lake_MonadLog_stdout___redArg(
    mut v_inst_5435_: *mut crate::leanh::LeanObject,
    mut v_minLv_5436_: u8,
    mut v_ansiMode_5437_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5438_ = crate::leanh::lean_box(0);
    v___x_5439_ = crate::leanh::lean_box((v_minLv_5436_) as usize);
    v___x_5440_ = crate::leanh::lean_box((v_ansiMode_5437_) as usize);
    v___f_5441_ = crate::leanh::lean_alloc_closure(
        l_Lake_MonadLog_stdout___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_5441_, 0, v___x_5438_);
    crate::leanh::lean_closure_set(v___f_5441_, 1, v___x_5439_);
    crate::leanh::lean_closure_set(v___f_5441_, 2, v___x_5440_);
    crate::leanh::lean_closure_set(v___f_5441_, 3, v_inst_5435_);
    return v___f_5441_;
}
pub unsafe fn l_Lake_MonadLog_stdout___redArg___boxed(
    mut v_inst_5442_: *mut crate::leanh::LeanObject,
    mut v_minLv_5443_: *mut crate::leanh::LeanObject,
    mut v_ansiMode_5444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_minLv_boxed_5445_: u8 = 0;
    let mut v_ansiMode_boxed_5446_: u8 = 0;
    let mut v_res_5447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_minLv_boxed_5445_ = (crate::leanh::lean_unbox(v_minLv_5443_) as u8);
    v_ansiMode_boxed_5446_ = (crate::leanh::lean_unbox(v_ansiMode_5444_) as u8);
    v_res_5447_ =
        l_Lake_MonadLog_stdout___redArg(v_inst_5442_, v_minLv_boxed_5445_, v_ansiMode_boxed_5446_);
    return v_res_5447_;
}
pub unsafe fn l_Lake_MonadLog_stdout(
    mut v_m_5448_: *mut crate::leanh::LeanObject,
    mut v_inst_5449_: *mut crate::leanh::LeanObject,
    mut v_minLv_5450_: u8,
    mut v_ansiMode_5451_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5452_ = crate::leanh::lean_box(0);
    v___x_5453_ = crate::leanh::lean_box((v_minLv_5450_) as usize);
    v___x_5454_ = crate::leanh::lean_box((v_ansiMode_5451_) as usize);
    v___f_5455_ = crate::leanh::lean_alloc_closure(
        l_Lake_MonadLog_stdout___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_5455_, 0, v___x_5452_);
    crate::leanh::lean_closure_set(v___f_5455_, 1, v___x_5453_);
    crate::leanh::lean_closure_set(v___f_5455_, 2, v___x_5454_);
    crate::leanh::lean_closure_set(v___f_5455_, 3, v_inst_5449_);
    return v___f_5455_;
}
pub unsafe fn l_Lake_MonadLog_stdout___boxed(
    mut v_m_5456_: *mut crate::leanh::LeanObject,
    mut v_inst_5457_: *mut crate::leanh::LeanObject,
    mut v_minLv_5458_: *mut crate::leanh::LeanObject,
    mut v_ansiMode_5459_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_minLv_boxed_5460_: u8 = 0;
    let mut v_ansiMode_boxed_5461_: u8 = 0;
    let mut v_res_5462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_minLv_boxed_5460_ = (crate::leanh::lean_unbox(v_minLv_5458_) as u8);
    v_ansiMode_boxed_5461_ = (crate::leanh::lean_unbox(v_ansiMode_5459_) as u8);
    v_res_5462_ = l_Lake_MonadLog_stdout(
        v_m_5456_,
        v_inst_5457_,
        v_minLv_boxed_5460_,
        v_ansiMode_boxed_5461_,
    );
    return v_res_5462_;
}
pub unsafe fn l_Lake_MonadLog_stderr___redArg(
    mut v_inst_5463_: *mut crate::leanh::LeanObject,
    mut v_minLv_5464_: u8,
    mut v_ansiMode_5465_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5466_ = crate::leanh::lean_box(1);
    v___x_5467_ = crate::leanh::lean_box((v_minLv_5464_) as usize);
    v___x_5468_ = crate::leanh::lean_box((v_ansiMode_5465_) as usize);
    v___f_5469_ = crate::leanh::lean_alloc_closure(
        l_Lake_MonadLog_stdout___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_5469_, 0, v___x_5466_);
    crate::leanh::lean_closure_set(v___f_5469_, 1, v___x_5467_);
    crate::leanh::lean_closure_set(v___f_5469_, 2, v___x_5468_);
    crate::leanh::lean_closure_set(v___f_5469_, 3, v_inst_5463_);
    return v___f_5469_;
}
pub unsafe fn l_Lake_MonadLog_stderr___redArg___boxed(
    mut v_inst_5470_: *mut crate::leanh::LeanObject,
    mut v_minLv_5471_: *mut crate::leanh::LeanObject,
    mut v_ansiMode_5472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_minLv_boxed_5473_: u8 = 0;
    let mut v_ansiMode_boxed_5474_: u8 = 0;
    let mut v_res_5475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_minLv_boxed_5473_ = (crate::leanh::lean_unbox(v_minLv_5471_) as u8);
    v_ansiMode_boxed_5474_ = (crate::leanh::lean_unbox(v_ansiMode_5472_) as u8);
    v_res_5475_ =
        l_Lake_MonadLog_stderr___redArg(v_inst_5470_, v_minLv_boxed_5473_, v_ansiMode_boxed_5474_);
    return v_res_5475_;
}
pub unsafe fn l_Lake_MonadLog_stderr(
    mut v_m_5476_: *mut crate::leanh::LeanObject,
    mut v_inst_5477_: *mut crate::leanh::LeanObject,
    mut v_minLv_5478_: u8,
    mut v_ansiMode_5479_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5480_ = crate::leanh::lean_box(1);
    v___x_5481_ = crate::leanh::lean_box((v_minLv_5478_) as usize);
    v___x_5482_ = crate::leanh::lean_box((v_ansiMode_5479_) as usize);
    v___f_5483_ = crate::leanh::lean_alloc_closure(
        l_Lake_MonadLog_stdout___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_5483_, 0, v___x_5480_);
    crate::leanh::lean_closure_set(v___f_5483_, 1, v___x_5481_);
    crate::leanh::lean_closure_set(v___f_5483_, 2, v___x_5482_);
    crate::leanh::lean_closure_set(v___f_5483_, 3, v_inst_5477_);
    return v___f_5483_;
}
pub unsafe fn l_Lake_MonadLog_stderr___boxed(
    mut v_m_5484_: *mut crate::leanh::LeanObject,
    mut v_inst_5485_: *mut crate::leanh::LeanObject,
    mut v_minLv_5486_: *mut crate::leanh::LeanObject,
    mut v_ansiMode_5487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_minLv_boxed_5488_: u8 = 0;
    let mut v_ansiMode_boxed_5489_: u8 = 0;
    let mut v_res_5490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_minLv_boxed_5488_ = (crate::leanh::lean_unbox(v_minLv_5486_) as u8);
    v_ansiMode_boxed_5489_ = (crate::leanh::lean_unbox(v_ansiMode_5487_) as u8);
    v_res_5490_ = l_Lake_MonadLog_stderr(
        v_m_5484_,
        v_inst_5485_,
        v_minLv_boxed_5488_,
        v_ansiMode_boxed_5489_,
    );
    return v_res_5490_;
}
pub unsafe fn l_Lake_OutStream_getLogger___redArg___lam__0(
    mut v_val_5491_: *mut crate::leanh::LeanObject,
    mut v_minLv_5492_: u8,
    mut v_val_5493_: u8,
    mut v_inst_5494_: *mut crate::leanh::LeanObject,
    mut v_e_5495_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5496_ = crate::leanh::lean_box((v_minLv_5492_) as usize);
    v___x_5497_ = crate::leanh::lean_box((v_val_5493_) as usize);
    v___x_5498_ = crate::leanh::lean_alloc_closure(
        l_Lake_logToStream___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___x_5498_, 0, v_e_5495_);
    crate::leanh::lean_closure_set(v___x_5498_, 1, v_val_5491_);
    crate::leanh::lean_closure_set(v___x_5498_, 2, v___x_5496_);
    crate::leanh::lean_closure_set(v___x_5498_, 3, v___x_5497_);
    v___x_5499_ = crate::leanh::lean_apply_2(v_inst_5494_, crate::leanh::lean_box(0), v___x_5498_);
    return v___x_5499_;
}
pub unsafe fn l_Lake_OutStream_getLogger___redArg___lam__0___boxed(
    mut v_val_5500_: *mut crate::leanh::LeanObject,
    mut v_minLv_5501_: *mut crate::leanh::LeanObject,
    mut v_val_5502_: *mut crate::leanh::LeanObject,
    mut v_inst_5503_: *mut crate::leanh::LeanObject,
    mut v_e_5504_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_minLv_boxed_5505_: u8 = 0;
    let mut v_val_105__boxed_5506_: u8 = 0;
    let mut v_res_5507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_minLv_boxed_5505_ = (crate::leanh::lean_unbox(v_minLv_5501_) as u8);
    v_val_105__boxed_5506_ = (crate::leanh::lean_unbox(v_val_5502_) as u8);
    v_res_5507_ = l_Lake_OutStream_getLogger___redArg___lam__0(
        v_val_5500_,
        v_minLv_boxed_5505_,
        v_val_105__boxed_5506_,
        v_inst_5503_,
        v_e_5504_,
    );
    return v_res_5507_;
}
pub unsafe fn l_Lake_OutStream_getLogger___redArg(
    mut v_inst_5508_: *mut crate::leanh::LeanObject,
    mut v_out_5509_: *mut crate::leanh::LeanObject,
    mut v_minLv_5510_: u8,
    mut v_ansiMode_5511_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5514_: u8 = 0;
    let mut v___x_5515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5513_ = l_Lake_OutStream_get(v_out_5509_);
    crate::leanh::lean_inc_ref(v___x_5513_);
    v___x_5514_ = l_Lake_AnsiMode_isEnabled(v___x_5513_, v_ansiMode_5511_);
    v___x_5515_ = crate::leanh::lean_box((v_minLv_5510_) as usize);
    v___x_5516_ = crate::leanh::lean_box((v___x_5514_) as usize);
    v___f_5517_ = crate::leanh::lean_alloc_closure(
        l_Lake_OutStream_getLogger___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_5517_, 0, v___x_5513_);
    crate::leanh::lean_closure_set(v___f_5517_, 1, v___x_5515_);
    crate::leanh::lean_closure_set(v___f_5517_, 2, v___x_5516_);
    crate::leanh::lean_closure_set(v___f_5517_, 3, v_inst_5508_);
    return v___f_5517_;
}
pub unsafe fn l_Lake_OutStream_getLogger___redArg___boxed(
    mut v_inst_5518_: *mut crate::leanh::LeanObject,
    mut v_out_5519_: *mut crate::leanh::LeanObject,
    mut v_minLv_5520_: *mut crate::leanh::LeanObject,
    mut v_ansiMode_5521_: *mut crate::leanh::LeanObject,
    mut v_a_5522_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_minLv_boxed_5523_: u8 = 0;
    let mut v_ansiMode_boxed_5524_: u8 = 0;
    let mut v_res_5525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_minLv_boxed_5523_ = (crate::leanh::lean_unbox(v_minLv_5520_) as u8);
    v_ansiMode_boxed_5524_ = (crate::leanh::lean_unbox(v_ansiMode_5521_) as u8);
    v_res_5525_ = l_Lake_OutStream_getLogger___redArg(
        v_inst_5518_,
        v_out_5519_,
        v_minLv_boxed_5523_,
        v_ansiMode_boxed_5524_,
    );
    crate::leanh::lean_dec(v_out_5519_);
    return v_res_5525_;
}
pub unsafe fn l_Lake_OutStream_getLogger(
    mut v_m_5526_: *mut crate::leanh::LeanObject,
    mut v_inst_5527_: *mut crate::leanh::LeanObject,
    mut v_out_5528_: *mut crate::leanh::LeanObject,
    mut v_minLv_5529_: u8,
    mut v_ansiMode_5530_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5533_: u8 = 0;
    let mut v___x_5534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5532_ = l_Lake_OutStream_get(v_out_5528_);
    crate::leanh::lean_inc_ref(v___x_5532_);
    v___x_5533_ = l_Lake_AnsiMode_isEnabled(v___x_5532_, v_ansiMode_5530_);
    v___x_5534_ = crate::leanh::lean_box((v_minLv_5529_) as usize);
    v___x_5535_ = crate::leanh::lean_box((v___x_5533_) as usize);
    v___f_5536_ = crate::leanh::lean_alloc_closure(
        l_Lake_OutStream_getLogger___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_5536_, 0, v___x_5532_);
    crate::leanh::lean_closure_set(v___f_5536_, 1, v___x_5534_);
    crate::leanh::lean_closure_set(v___f_5536_, 2, v___x_5535_);
    crate::leanh::lean_closure_set(v___f_5536_, 3, v_inst_5527_);
    return v___f_5536_;
}
pub unsafe fn l_Lake_OutStream_getLogger___boxed(
    mut v_m_5537_: *mut crate::leanh::LeanObject,
    mut v_inst_5538_: *mut crate::leanh::LeanObject,
    mut v_out_5539_: *mut crate::leanh::LeanObject,
    mut v_minLv_5540_: *mut crate::leanh::LeanObject,
    mut v_ansiMode_5541_: *mut crate::leanh::LeanObject,
    mut v_a_5542_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_minLv_boxed_5543_: u8 = 0;
    let mut v_ansiMode_boxed_5544_: u8 = 0;
    let mut v_res_5545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_minLv_boxed_5543_ = (crate::leanh::lean_unbox(v_minLv_5540_) as u8);
    v_ansiMode_boxed_5544_ = (crate::leanh::lean_unbox(v_ansiMode_5541_) as u8);
    v_res_5545_ = l_Lake_OutStream_getLogger(
        v_m_5537_,
        v_inst_5538_,
        v_out_5539_,
        v_minLv_boxed_5543_,
        v_ansiMode_boxed_5544_,
    );
    crate::leanh::lean_dec(v_out_5539_);
    return v_res_5545_;
}
pub unsafe fn l_Lake_MonadLogT_instInhabitedOfPure___redArg___lam__0(
    mut v_inst_5546_: *mut crate::leanh::LeanObject,
    mut v_inst_5547_: *mut crate::leanh::LeanObject,
    mut v_x_5548_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5549_ = crate::leanh::lean_apply_2(v_inst_5546_, crate::leanh::lean_box(0), v_inst_5547_);
    return v___x_5549_;
}
pub unsafe fn l_Lake_MonadLogT_instInhabitedOfPure___redArg___lam__0___boxed(
    mut v_inst_5550_: *mut crate::leanh::LeanObject,
    mut v_inst_5551_: *mut crate::leanh::LeanObject,
    mut v_x_5552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5553_ = l_Lake_MonadLogT_instInhabitedOfPure___redArg___lam__0(
        v_inst_5550_,
        v_inst_5551_,
        v_x_5552_,
    );
    crate::leanh::lean_dec(v_x_5552_);
    return v_res_5553_;
}
pub unsafe fn l_Lake_MonadLogT_instInhabitedOfPure___redArg(
    mut v_inst_5554_: *mut crate::leanh::LeanObject,
    mut v_inst_5555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5556_ = crate::leanh::lean_alloc_closure(
        l_Lake_MonadLogT_instInhabitedOfPure___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_5556_, 0, v_inst_5554_);
    crate::leanh::lean_closure_set(v___f_5556_, 1, v_inst_5555_);
    return v___f_5556_;
}
pub unsafe fn l_Lake_MonadLogT_instInhabitedOfPure(
    mut v_n_5557_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_5558_: *mut crate::leanh::LeanObject,
    mut v_m_5559_: *mut crate::leanh::LeanObject,
    mut v_inst_5560_: *mut crate::leanh::LeanObject,
    mut v_inst_5561_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5562_ = crate::leanh::lean_alloc_closure(
        l_Lake_MonadLogT_instInhabitedOfPure___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_5562_, 0, v_inst_5560_);
    crate::leanh::lean_closure_set(v___f_5562_, 1, v_inst_5561_);
    return v___f_5562_;
}
pub unsafe fn l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg___lam__0(
    mut v_e_5563_: *mut crate::leanh::LeanObject,
    mut v_inst_5564_: *mut crate::leanh::LeanObject,
    mut v_a_5565_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5566_ = crate::leanh::lean_apply_1(v_a_5565_, v_e_5563_);
    v___x_5567_ = crate::leanh::lean_apply_2(v_inst_5564_, crate::leanh::lean_box(0), v___x_5566_);
    return v___x_5567_;
}
pub unsafe fn l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg___lam__1(
    mut v_inst_5568_: *mut crate::leanh::LeanObject,
    mut v_inst_5569_: *mut crate::leanh::LeanObject,
    mut v_e_5570_: *mut crate::leanh::LeanObject,
    mut v___y_5571_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_5572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_5573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_5574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_5572_ = crate::leanh::lean_ctor_get(v_inst_5568_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_5572_);
    v_toBind_5573_ = crate::leanh::lean_ctor_get(v_inst_5568_, 1);
    crate::leanh::lean_inc(v_toBind_5573_);
    crate::leanh::lean_dec_ref(v_inst_5568_);
    v_toPure_5574_ = crate::leanh::lean_ctor_get(v_toApplicative_5572_, 1);
    crate::leanh::lean_inc(v_toPure_5574_);
    crate::leanh::lean_dec_ref(v_toApplicative_5572_);
    v___f_5575_ = crate::leanh::lean_alloc_closure(
        l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_5575_, 0, v_e_5570_);
    crate::leanh::lean_closure_set(v___f_5575_, 1, v_inst_5569_);
    crate::leanh::lean_inc(v___y_5571_);
    v___x_5576_ =
        crate::leanh::lean_apply_2(v_toPure_5574_, crate::leanh::lean_box(0), v___y_5571_);
    v___x_5577_ = crate::leanh::lean_apply_4(
        v_toBind_5573_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5576_,
        v___f_5575_,
    );
    return v___x_5577_;
}
pub unsafe fn l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg___lam__1___boxed(
    mut v_inst_5578_: *mut crate::leanh::LeanObject,
    mut v_inst_5579_: *mut crate::leanh::LeanObject,
    mut v_e_5580_: *mut crate::leanh::LeanObject,
    mut v___y_5581_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5582_ = l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg___lam__1(
        v_inst_5578_,
        v_inst_5579_,
        v_e_5580_,
        v___y_5581_,
    );
    crate::leanh::lean_dec(v___y_5581_);
    return v_res_5582_;
}
pub unsafe fn l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg(
    mut v_inst_5583_: *mut crate::leanh::LeanObject,
    mut v_inst_5584_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5585_ = crate::leanh::lean_alloc_closure(
        l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_5585_, 0, v_inst_5583_);
    crate::leanh::lean_closure_set(v___f_5585_, 1, v_inst_5584_);
    return v___f_5585_;
}
pub unsafe fn l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT(
    mut v_n_5586_: *mut crate::leanh::LeanObject,
    mut v_m_5587_: *mut crate::leanh::LeanObject,
    mut v_inst_5588_: *mut crate::leanh::LeanObject,
    mut v_inst_5589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5590_ = crate::leanh::lean_alloc_closure(
        l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_5590_, 0, v_inst_5588_);
    crate::leanh::lean_closure_set(v___f_5590_, 1, v_inst_5589_);
    return v___f_5590_;
}
pub unsafe fn l_Lake_MonadLogT_adaptMethods___redArg(
    mut v_f_5591_: *mut crate::leanh::LeanObject,
    mut v_self_5592_: *mut crate::leanh::LeanObject,
    mut v_a_5593_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_5593_);
    v___x_5594_ = crate::leanh::lean_apply_1(v_f_5591_, v_a_5593_);
    v___x_5595_ = crate::leanh::lean_apply_1(v_self_5592_, v___x_5594_);
    return v___x_5595_;
}
pub unsafe fn l_Lake_MonadLogT_adaptMethods___redArg___boxed(
    mut v_f_5596_: *mut crate::leanh::LeanObject,
    mut v_self_5597_: *mut crate::leanh::LeanObject,
    mut v_a_5598_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5599_ = l_Lake_MonadLogT_adaptMethods___redArg(v_f_5596_, v_self_5597_, v_a_5598_);
    crate::leanh::lean_dec(v_a_5598_);
    return v_res_5599_;
}
pub unsafe fn l_Lake_MonadLogT_adaptMethods(
    mut v_n_5600_: *mut crate::leanh::LeanObject,
    mut v_m_5601_: *mut crate::leanh::LeanObject,
    mut v_m_x27_5602_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_5603_: *mut crate::leanh::LeanObject,
    mut v_inst_5604_: *mut crate::leanh::LeanObject,
    mut v_f_5605_: *mut crate::leanh::LeanObject,
    mut v_self_5606_: *mut crate::leanh::LeanObject,
    mut v_a_5607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_5607_);
    v___x_5608_ = crate::leanh::lean_apply_1(v_f_5605_, v_a_5607_);
    v___x_5609_ = crate::leanh::lean_apply_1(v_self_5606_, v___x_5608_);
    return v___x_5609_;
}
pub unsafe fn l_Lake_MonadLogT_adaptMethods___boxed(
    mut v_n_5610_: *mut crate::leanh::LeanObject,
    mut v_m_5611_: *mut crate::leanh::LeanObject,
    mut v_m_x27_5612_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_5613_: *mut crate::leanh::LeanObject,
    mut v_inst_5614_: *mut crate::leanh::LeanObject,
    mut v_f_5615_: *mut crate::leanh::LeanObject,
    mut v_self_5616_: *mut crate::leanh::LeanObject,
    mut v_a_5617_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5618_ = l_Lake_MonadLogT_adaptMethods(
        v_n_5610_,
        v_m_5611_,
        v_m_x27_5612_,
        v_00_u03b1_5613_,
        v_inst_5614_,
        v_f_5615_,
        v_self_5616_,
        v_a_5617_,
    );
    crate::leanh::lean_dec(v_a_5617_);
    crate::leanh::lean_dec_ref(v_inst_5614_);
    return v_res_5618_;
}
pub unsafe fn l_Lake_MonadLogT_ignoreLog___redArg(
    mut v_inst_5619_: *mut crate::leanh::LeanObject,
    mut v_self_5620_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5621_ = crate::leanh::lean_alloc_closure(
        l_Lake_MonadLog_nop___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5621_, 0, v_inst_5619_);
    v___x_5622_ = crate::leanh::lean_apply_1(v_self_5620_, v___f_5621_);
    return v___x_5622_;
}
pub unsafe fn l_Lake_MonadLogT_ignoreLog(
    mut v_m_5623_: *mut crate::leanh::LeanObject,
    mut v_n_5624_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_5625_: *mut crate::leanh::LeanObject,
    mut v_inst_5626_: *mut crate::leanh::LeanObject,
    mut v_self_5627_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5628_ = crate::leanh::lean_alloc_closure(
        l_Lake_MonadLog_nop___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5628_, 0, v_inst_5626_);
    v___x_5629_ = crate::leanh::lean_apply_1(v_self_5627_, v___f_5628_);
    return v___x_5629_;
}
pub unsafe fn l_Lake_instToJsonLog___lam__0(
    mut v___x_5634_: *mut crate::leanh::LeanObject,
    mut v_x_5635_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5636_ = l_Array_toJson___redArg(v___x_5634_, v_x_5635_);
    return v___x_5636_;
}
pub unsafe fn l_Lake_instFromJsonLog___lam__0(
    mut v___x_5640_: *mut crate::leanh::LeanObject,
    mut v_x_5641_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5646_: u8 = 0;
    let mut v___x_5648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5650_: u8 = 0;
    let mut v_a_5651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5654_: u8 = 0;
    let mut v___x_5656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5658_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5642_ = l_Array_fromJson_x3f___redArg(v___x_5640_, v_x_5641_);
                if crate::leanh::lean_obj_tag(v___x_5642_) == 0 {
                    v_a_5643_ = crate::leanh::lean_ctor_get(v___x_5642_, 0);
                    v_isSharedCheck_5650_ = (!crate::leanh::lean_is_exclusive(v___x_5642_)) as u8;
                    if v_isSharedCheck_5650_ == 0 {
                        v___x_5645_ = v___x_5642_;
                        v_isShared_5646_ = v_isSharedCheck_5650_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5643_);
                        crate::leanh::lean_dec(v___x_5642_);
                        v___x_5645_ = crate::leanh::lean_box(0);
                        v_isShared_5646_ = v_isSharedCheck_5650_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5651_ = crate::leanh::lean_ctor_get(v___x_5642_, 0);
                    v_isSharedCheck_5658_ = (!crate::leanh::lean_is_exclusive(v___x_5642_)) as u8;
                    if v_isSharedCheck_5658_ == 0 {
                        v___x_5653_ = v___x_5642_;
                        v_isShared_5654_ = v_isSharedCheck_5658_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5651_);
                        crate::leanh::lean_dec(v___x_5642_);
                        v___x_5653_ = crate::leanh::lean_box(0);
                        v_isShared_5654_ = v_isSharedCheck_5658_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5646_ == 0 {
                    v___x_5648_ = v___x_5645_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5649_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5649_, 0, v_a_5643_);
                    v___x_5648_ = v_reuseFailAlloc_5649_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5648_;
            }
            3 => {
                if v_isShared_5654_ == 0 {
                    v___x_5656_ = v___x_5653_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5657_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5657_, 0, v_a_5651_);
                    v___x_5656_ = v_reuseFailAlloc_5657_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5656_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lake_Log_instInhabitedPos_default() -> *mut crate::leanh::LeanObject {
    let mut v___x_5662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5662_ = crate::leanh::lean_unsigned_to_nat(0);
    return v___x_5662_;
}
pub unsafe fn _init_l_Lake_Log_instInhabitedPos() -> *mut crate::leanh::LeanObject {
    let mut v___x_5663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5663_ = crate::leanh::lean_unsigned_to_nat(0);
    return v___x_5663_;
}
pub unsafe fn l_Lake_Log_instDecidableEqPos_decEq(
    mut v_x_5664_: *mut crate::leanh::LeanObject,
    mut v_x_5665_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5666_: u8 = 0;
    v___x_5666_ = lean_nat_dec_eq(v_x_5664_, v_x_5665_);
    return v___x_5666_;
}
pub unsafe fn l_Lake_Log_instDecidableEqPos_decEq___boxed(
    mut v_x_5667_: *mut crate::leanh::LeanObject,
    mut v_x_5668_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5669_: u8 = 0;
    let mut v_r_5670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5669_ = l_Lake_Log_instDecidableEqPos_decEq(v_x_5667_, v_x_5668_);
    crate::leanh::lean_dec(v_x_5668_);
    crate::leanh::lean_dec(v_x_5667_);
    v_r_5670_ = crate::leanh::lean_box((v_res_5669_) as usize);
    return v_r_5670_;
}
pub unsafe fn l_Lake_Log_instDecidableEqPos(
    mut v_x_5671_: *mut crate::leanh::LeanObject,
    mut v_x_5672_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5673_: u8 = 0;
    v___x_5673_ = lean_nat_dec_eq(v_x_5671_, v_x_5672_);
    return v___x_5673_;
}
pub unsafe fn l_Lake_Log_instDecidableEqPos___boxed(
    mut v_x_5674_: *mut crate::leanh::LeanObject,
    mut v_x_5675_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5676_: u8 = 0;
    let mut v_r_5677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5676_ = l_Lake_Log_instDecidableEqPos(v_x_5674_, v_x_5675_);
    crate::leanh::lean_dec(v_x_5675_);
    crate::leanh::lean_dec(v_x_5674_);
    v_r_5677_ = crate::leanh::lean_box((v_res_5676_) as usize);
    return v_r_5677_;
}
pub unsafe fn _init_l_Lake_instOfNatPos() -> *mut crate::leanh::LeanObject {
    let mut v___x_5678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5678_ = crate::leanh::lean_unsigned_to_nat(0);
    return v___x_5678_;
}
pub unsafe fn l_Lake_instOrdPos___lam__0(
    mut v_x1_5679_: *mut crate::leanh::LeanObject,
    mut v_x2_5680_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5681_: u8 = 0;
    v___x_5681_ = lean_nat_dec_lt(v_x1_5679_, v_x2_5680_);
    if v___x_5681_ == 0 {
        let mut v___x_5682_: u8 = 0;
        v___x_5682_ = lean_nat_dec_eq(v_x1_5679_, v_x2_5680_);
        if v___x_5682_ == 0 {
            let mut v___x_5683_: u8 = 0;
            v___x_5683_ = 2;
            return v___x_5683_;
        } else {
            let mut v___x_5684_: u8 = 0;
            v___x_5684_ = 1;
            return v___x_5684_;
        }
    } else {
        let mut v___x_5685_: u8 = 0;
        v___x_5685_ = 0;
        return v___x_5685_;
    }
}
pub unsafe fn l_Lake_instOrdPos___lam__0___boxed(
    mut v_x1_5686_: *mut crate::leanh::LeanObject,
    mut v_x2_5687_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5688_: u8 = 0;
    let mut v_r_5689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5688_ = l_Lake_instOrdPos___lam__0(v_x1_5686_, v_x2_5687_);
    crate::leanh::lean_dec(v_x2_5687_);
    crate::leanh::lean_dec(v_x1_5686_);
    v_r_5689_ = crate::leanh::lean_box((v_res_5688_) as usize);
    return v_r_5689_;
}
pub unsafe fn _init_l_Lake_instLTPos() -> *mut crate::leanh::LeanObject {
    let mut v___x_5692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5692_ = crate::leanh::lean_box(0);
    return v___x_5692_;
}
pub unsafe fn l_Lake_instDecidableRelPosLt(
    mut v_a_5693_: *mut crate::leanh::LeanObject,
    mut v_b_5694_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5695_: u8 = 0;
    v___x_5695_ = lean_nat_dec_lt(v_a_5693_, v_b_5694_);
    return v___x_5695_;
}
pub unsafe fn l_Lake_instDecidableRelPosLt___boxed(
    mut v_a_5696_: *mut crate::leanh::LeanObject,
    mut v_b_5697_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5698_: u8 = 0;
    let mut v_r_5699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5698_ = l_Lake_instDecidableRelPosLt(v_a_5696_, v_b_5697_);
    crate::leanh::lean_dec(v_b_5697_);
    crate::leanh::lean_dec(v_a_5696_);
    v_r_5699_ = crate::leanh::lean_box((v_res_5698_) as usize);
    return v_r_5699_;
}
pub unsafe fn _init_l_Lake_instLEPos() -> *mut crate::leanh::LeanObject {
    let mut v___x_5700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5700_ = crate::leanh::lean_box(0);
    return v___x_5700_;
}
pub unsafe fn l_Lake_instDecidableRelPosLe(
    mut v_a_5701_: *mut crate::leanh::LeanObject,
    mut v_b_5702_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5703_: u8 = 0;
    v___x_5703_ = lean_nat_dec_le(v_a_5701_, v_b_5702_);
    return v___x_5703_;
}
pub unsafe fn l_Lake_instDecidableRelPosLe___boxed(
    mut v_a_5704_: *mut crate::leanh::LeanObject,
    mut v_b_5705_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5706_: u8 = 0;
    let mut v_r_5707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5706_ = l_Lake_instDecidableRelPosLe(v_a_5704_, v_b_5705_);
    crate::leanh::lean_dec(v_b_5705_);
    crate::leanh::lean_dec(v_a_5704_);
    v_r_5707_ = crate::leanh::lean_box((v_res_5706_) as usize);
    return v_r_5707_;
}
pub unsafe fn l_Lake_instMinPos___lam__0(
    mut v_x_5708_: *mut crate::leanh::LeanObject,
    mut v_y_5709_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5710_: u8 = 0;
    v___x_5710_ = lean_nat_dec_le(v_x_5708_, v_y_5709_);
    if v___x_5710_ == 0 {
        crate::leanh::lean_inc(v_y_5709_);
        return v_y_5709_;
    } else {
        crate::leanh::lean_inc(v_x_5708_);
        return v_x_5708_;
    }
}
pub unsafe fn l_Lake_instMinPos___lam__0___boxed(
    mut v_x_5711_: *mut crate::leanh::LeanObject,
    mut v_y_5712_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5713_ = l_Lake_instMinPos___lam__0(v_x_5711_, v_y_5712_);
    crate::leanh::lean_dec(v_y_5712_);
    crate::leanh::lean_dec(v_x_5711_);
    return v_res_5713_;
}
pub unsafe fn l_Lake_instMaxPos___lam__0(
    mut v_x_5716_: *mut crate::leanh::LeanObject,
    mut v_y_5717_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5718_: u8 = 0;
    v___x_5718_ = lean_nat_dec_le(v_x_5716_, v_y_5717_);
    if v___x_5718_ == 0 {
        crate::leanh::lean_inc(v_x_5716_);
        return v_x_5716_;
    } else {
        crate::leanh::lean_inc(v_y_5717_);
        return v_y_5717_;
    }
}
pub unsafe fn l_Lake_instMaxPos___lam__0___boxed(
    mut v_x_5719_: *mut crate::leanh::LeanObject,
    mut v_y_5720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5721_ = l_Lake_instMaxPos___lam__0(v_x_5719_, v_y_5720_);
    crate::leanh::lean_dec(v_y_5720_);
    crate::leanh::lean_dec(v_x_5719_);
    return v_res_5721_;
}
pub unsafe fn l_Lake_Log_size(
    mut v_log_5728_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5729_ = lean_array_get_size(v_log_5728_);
    return v___x_5729_;
}
pub unsafe fn l_Lake_Log_size___boxed(
    mut v_log_5730_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5731_ = l_Lake_Log_size(v_log_5730_);
    crate::leanh::lean_dec_ref(v_log_5730_);
    return v_res_5731_;
}
pub unsafe fn l_Lake_Log_isEmpty(mut v_log_5732_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_5733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5735_: u8 = 0;
    v___x_5733_ = lean_array_get_size(v_log_5732_);
    v___x_5734_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5735_ = lean_nat_dec_eq(v___x_5733_, v___x_5734_);
    return v___x_5735_;
}
pub unsafe fn l_Lake_Log_isEmpty___boxed(
    mut v_log_5736_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5737_: u8 = 0;
    let mut v_r_5738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5737_ = l_Lake_Log_isEmpty(v_log_5736_);
    crate::leanh::lean_dec_ref(v_log_5736_);
    v_r_5738_ = crate::leanh::lean_box((v_res_5737_) as usize);
    return v_r_5738_;
}
pub unsafe fn l_Lake_Log_hasEntries(mut v_log_5739_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_5740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5742_: u8 = 0;
    v___x_5740_ = lean_array_get_size(v_log_5739_);
    v___x_5741_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5742_ = lean_nat_dec_eq(v___x_5740_, v___x_5741_);
    if v___x_5742_ == 0 {
        let mut v___x_5743_: u8 = 0;
        v___x_5743_ = 1;
        return v___x_5743_;
    } else {
        let mut v___x_5744_: u8 = 0;
        v___x_5744_ = 0;
        return v___x_5744_;
    }
}
pub unsafe fn l_Lake_Log_hasEntries___boxed(
    mut v_log_5745_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5746_: u8 = 0;
    let mut v_r_5747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5746_ = l_Lake_Log_hasEntries(v_log_5745_);
    crate::leanh::lean_dec_ref(v_log_5745_);
    v_r_5747_ = crate::leanh::lean_box((v_res_5746_) as usize);
    return v_r_5747_;
}
pub unsafe fn l_Lake_Log_endPos(
    mut v_log_5748_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5749_ = lean_array_get_size(v_log_5748_);
    return v___x_5749_;
}
pub unsafe fn l_Lake_Log_endPos___boxed(
    mut v_log_5750_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5751_ = l_Lake_Log_endPos(v_log_5750_);
    crate::leanh::lean_dec_ref(v_log_5750_);
    return v_res_5751_;
}
pub unsafe fn l_Lake_Log_push(
    mut v_log_5752_: *mut crate::leanh::LeanObject,
    mut v_e_5753_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5754_ = lean_array_push(v_log_5752_, v_e_5753_);
    return v___x_5754_;
}
pub unsafe fn l_Lake_Log_append(
    mut v_log_5755_: *mut crate::leanh::LeanObject,
    mut v_o_5756_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5757_ = l_Array_append___redArg(v_log_5755_, v_o_5756_);
    return v___x_5757_;
}
pub unsafe fn l_Lake_Log_append___boxed(
    mut v_log_5758_: *mut crate::leanh::LeanObject,
    mut v_o_5759_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5760_ = l_Lake_Log_append(v_log_5758_, v_o_5759_);
    crate::leanh::lean_dec_ref(v_o_5759_);
    return v_res_5760_;
}
pub unsafe fn l_Lake_Log_extract(
    mut v_log_5763_: *mut crate::leanh::LeanObject,
    mut v_start_5764_: *mut crate::leanh::LeanObject,
    mut v_stop_5765_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5766_ = l_Array_extract___redArg(v_log_5763_, v_start_5764_, v_stop_5765_);
    return v___x_5766_;
}
pub unsafe fn l_Lake_Log_extract___boxed(
    mut v_log_5767_: *mut crate::leanh::LeanObject,
    mut v_start_5768_: *mut crate::leanh::LeanObject,
    mut v_stop_5769_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5770_ = l_Lake_Log_extract(v_log_5767_, v_start_5768_, v_stop_5769_);
    crate::leanh::lean_dec_ref(v_log_5767_);
    return v_res_5770_;
}
pub unsafe fn l_Lake_Log_dropFrom(
    mut v_log_5771_: *mut crate::leanh::LeanObject,
    mut v_pos_5772_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5773_ = l_Array_shrink___redArg(v_log_5771_, v_pos_5772_);
    return v___x_5773_;
}
pub unsafe fn l_Lake_Log_dropFrom___boxed(
    mut v_log_5774_: *mut crate::leanh::LeanObject,
    mut v_pos_5775_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5776_ = l_Lake_Log_dropFrom(v_log_5774_, v_pos_5775_);
    crate::leanh::lean_dec(v_pos_5775_);
    return v_res_5776_;
}
pub unsafe fn l_Lake_Log_takeFrom(
    mut v_log_5777_: *mut crate::leanh::LeanObject,
    mut v_pos_5778_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5779_ = lean_array_get_size(v_log_5777_);
    v___x_5780_ = l_Array_extract___redArg(v_log_5777_, v_pos_5778_, v___x_5779_);
    return v___x_5780_;
}
pub unsafe fn l_Lake_Log_takeFrom___boxed(
    mut v_log_5781_: *mut crate::leanh::LeanObject,
    mut v_pos_5782_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5783_ = l_Lake_Log_takeFrom(v_log_5781_, v_pos_5782_);
    crate::leanh::lean_dec_ref(v_log_5781_);
    return v_res_5783_;
}
pub unsafe fn l_Lake_Log_split(
    mut v_log_5784_: *mut crate::leanh::LeanObject,
    mut v_pos_5785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_log_5784_);
    v___x_5786_ = l_Array_shrink___redArg(v_log_5784_, v_pos_5785_);
    v___x_5787_ = lean_array_get_size(v_log_5784_);
    v___x_5788_ = l_Array_extract___redArg(v_log_5784_, v_pos_5785_, v___x_5787_);
    crate::leanh::lean_dec_ref(v_log_5784_);
    v___x_5789_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5789_, 0, v___x_5786_);
    crate::leanh::lean_ctor_set(v___x_5789_, 1, v___x_5788_);
    return v___x_5789_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_toString_spec__0(
    mut v_as_5791_: *mut crate::leanh::LeanObject,
    mut v_i_5792_: usize,
    mut v_stop_5793_: usize,
    mut v_b_5794_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5795_: u8 = 0;
    let mut v___x_5796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5801_: usize = 0;
    let mut v___x_5802_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5795_ = lean_usize_dec_eq(v_i_5792_, v_stop_5793_);
                if v___x_5795_ == 0 {
                    v___x_5796_ = lean_array_uget_borrowed(v_as_5791_, v_i_5792_);
                    v___x_5797_ = l_Lake_LogEntry_toString(v___x_5796_, v___x_5795_);
                    v___x_5798_ = lean_string_append(v_b_5794_, v___x_5797_);
                    crate::leanh::lean_dec_ref(v___x_5797_);
                    v___x_5799_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_toString_spec__0___closed__0;
                    v___x_5800_ = lean_string_append(v___x_5798_, v___x_5799_);
                    v___x_5801_ = 1usize;
                    v___x_5802_ = lean_usize_add(v_i_5792_, v___x_5801_);
                    v_i_5792_ = v___x_5802_;
                    v_b_5794_ = v___x_5800_;
                    state = 0;
                    continue;
                } else {
                    return v_b_5794_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_toString_spec__0___boxed(
    mut v_as_5804_: *mut crate::leanh::LeanObject,
    mut v_i_5805_: *mut crate::leanh::LeanObject,
    mut v_stop_5806_: *mut crate::leanh::LeanObject,
    mut v_b_5807_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_5808_: usize = 0;
    let mut v_stop_boxed_5809_: usize = 0;
    let mut v_res_5810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5808_ = crate::leanh::lean_unbox_usize(v_i_5805_);
    crate::leanh::lean_dec(v_i_5805_);
    v_stop_boxed_5809_ = crate::leanh::lean_unbox_usize(v_stop_5806_);
    crate::leanh::lean_dec(v_stop_5806_);
    v_res_5810_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_toString_spec__0(v_as_5804_, v_i_boxed_5808_, v_stop_boxed_5809_, v_b_5807_);
    crate::leanh::lean_dec_ref(v_as_5804_);
    return v_res_5810_;
}
pub unsafe fn l_Lake_Log_toString(
    mut v_log_5811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5815_: u8 = 0;
    v___x_5812_ = l_Lake_instInhabitedLogEntry_default___closed__0;
    v___x_5813_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5814_ = lean_array_get_size(v_log_5811_);
    v___x_5815_ = lean_nat_dec_lt(v___x_5813_, v___x_5814_);
    if v___x_5815_ == 0 {
        return v___x_5812_;
    } else {
        let mut v___x_5816_: u8 = 0;
        v___x_5816_ = lean_nat_dec_le(v___x_5814_, v___x_5814_);
        if v___x_5816_ == 0 {
            if v___x_5815_ == 0 {
                return v___x_5812_;
            } else {
                let mut v___x_5817_: usize = 0;
                let mut v___x_5818_: usize = 0;
                let mut v___x_5819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_5817_ = 0usize;
                v___x_5818_ = lean_usize_of_nat(v___x_5814_);
                v___x_5819_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_toString_spec__0(v_log_5811_, v___x_5817_, v___x_5818_, v___x_5812_);
                return v___x_5819_;
            }
        } else {
            let mut v___x_5820_: usize = 0;
            let mut v___x_5821_: usize = 0;
            let mut v___x_5822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_5820_ = 0usize;
            v___x_5821_ = lean_usize_of_nat(v___x_5814_);
            v___x_5822_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_toString_spec__0(v_log_5811_, v___x_5820_, v___x_5821_, v___x_5812_);
            return v___x_5822_;
        }
    }
}
pub unsafe fn l_Lake_Log_toString___boxed(
    mut v_log_5823_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5824_ = l_Lake_Log_toString(v_log_5823_);
    crate::leanh::lean_dec_ref(v_log_5823_);
    return v_res_5824_;
}
pub unsafe fn l_Lake_Log_replay___redArg___lam__0(
    mut v_logger_5827_: *mut crate::leanh::LeanObject,
    mut v_x_5828_: *mut crate::leanh::LeanObject,
    mut v___y_5829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5830_ = crate::leanh::lean_apply_1(v_logger_5827_, v___y_5829_);
    return v___x_5830_;
}
pub unsafe fn l_Lake_Log_replay___redArg(
    mut v_inst_5831_: *mut crate::leanh::LeanObject,
    mut v_logger_5832_: *mut crate::leanh::LeanObject,
    mut v_log_5833_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5837_: u8 = 0;
    v___x_5834_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5835_ = lean_array_get_size(v_log_5833_);
    v___x_5836_ = crate::leanh::lean_box(0);
    v___x_5837_ = lean_nat_dec_lt(v___x_5834_, v___x_5835_);
    if v___x_5837_ == 0 {
        let mut v_toApplicative_5838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_5839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_log_5833_);
        crate::leanh::lean_dec(v_logger_5832_);
        v_toApplicative_5838_ = crate::leanh::lean_ctor_get(v_inst_5831_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_5838_);
        crate::leanh::lean_dec_ref(v_inst_5831_);
        v_toPure_5839_ = crate::leanh::lean_ctor_get(v_toApplicative_5838_, 1);
        crate::leanh::lean_inc(v_toPure_5839_);
        crate::leanh::lean_dec_ref(v_toApplicative_5838_);
        v___x_5840_ =
            crate::leanh::lean_apply_2(v_toPure_5839_, crate::leanh::lean_box(0), v___x_5836_);
        return v___x_5840_;
    } else {
        let mut v___f_5841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5842_: u8 = 0;
        v___f_5841_ = crate::leanh::lean_alloc_closure(
            l_Lake_Log_replay___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        crate::leanh::lean_closure_set(v___f_5841_, 0, v_logger_5832_);
        v___x_5842_ = lean_nat_dec_le(v___x_5835_, v___x_5835_);
        if v___x_5842_ == 0 {
            if v___x_5837_ == 0 {
                let mut v_toApplicative_5843_: *mut crate::leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_5844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v___f_5841_);
                crate::leanh::lean_dec_ref(v_log_5833_);
                v_toApplicative_5843_ = crate::leanh::lean_ctor_get(v_inst_5831_, 0);
                crate::leanh::lean_inc_ref(v_toApplicative_5843_);
                crate::leanh::lean_dec_ref(v_inst_5831_);
                v_toPure_5844_ = crate::leanh::lean_ctor_get(v_toApplicative_5843_, 1);
                crate::leanh::lean_inc(v_toPure_5844_);
                crate::leanh::lean_dec_ref(v_toApplicative_5843_);
                v___x_5845_ = crate::leanh::lean_apply_2(
                    v_toPure_5844_,
                    crate::leanh::lean_box(0),
                    v___x_5836_,
                );
                return v___x_5845_;
            } else {
                let mut v___x_5846_: usize = 0;
                let mut v___x_5847_: usize = 0;
                let mut v___x_5848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_5846_ = 0usize;
                v___x_5847_ = lean_usize_of_nat(v___x_5835_);
                v___x_5848_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v_inst_5831_,
                    v___f_5841_,
                    v_log_5833_,
                    v___x_5846_,
                    v___x_5847_,
                    v___x_5836_,
                );
                return v___x_5848_;
            }
        } else {
            let mut v___x_5849_: usize = 0;
            let mut v___x_5850_: usize = 0;
            let mut v___x_5851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_5849_ = 0usize;
            v___x_5850_ = lean_usize_of_nat(v___x_5835_);
            v___x_5851_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v_inst_5831_,
                v___f_5841_,
                v_log_5833_,
                v___x_5849_,
                v___x_5850_,
                v___x_5836_,
            );
            return v___x_5851_;
        }
    }
}
pub unsafe fn l_Lake_Log_replay(
    mut v_m_5852_: *mut crate::leanh::LeanObject,
    mut v_inst_5853_: *mut crate::leanh::LeanObject,
    mut v_logger_5854_: *mut crate::leanh::LeanObject,
    mut v_log_5855_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5859_: u8 = 0;
    v___x_5856_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5857_ = lean_array_get_size(v_log_5855_);
    v___x_5858_ = crate::leanh::lean_box(0);
    v___x_5859_ = lean_nat_dec_lt(v___x_5856_, v___x_5857_);
    if v___x_5859_ == 0 {
        let mut v_toApplicative_5860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_5861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_log_5855_);
        crate::leanh::lean_dec(v_logger_5854_);
        v_toApplicative_5860_ = crate::leanh::lean_ctor_get(v_inst_5853_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_5860_);
        crate::leanh::lean_dec_ref(v_inst_5853_);
        v_toPure_5861_ = crate::leanh::lean_ctor_get(v_toApplicative_5860_, 1);
        crate::leanh::lean_inc(v_toPure_5861_);
        crate::leanh::lean_dec_ref(v_toApplicative_5860_);
        v___x_5862_ =
            crate::leanh::lean_apply_2(v_toPure_5861_, crate::leanh::lean_box(0), v___x_5858_);
        return v___x_5862_;
    } else {
        let mut v___f_5863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5864_: u8 = 0;
        v___f_5863_ = crate::leanh::lean_alloc_closure(
            l_Lake_Log_replay___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        crate::leanh::lean_closure_set(v___f_5863_, 0, v_logger_5854_);
        v___x_5864_ = lean_nat_dec_le(v___x_5857_, v___x_5857_);
        if v___x_5864_ == 0 {
            if v___x_5859_ == 0 {
                let mut v_toApplicative_5865_: *mut crate::leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_5866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v___f_5863_);
                crate::leanh::lean_dec_ref(v_log_5855_);
                v_toApplicative_5865_ = crate::leanh::lean_ctor_get(v_inst_5853_, 0);
                crate::leanh::lean_inc_ref(v_toApplicative_5865_);
                crate::leanh::lean_dec_ref(v_inst_5853_);
                v_toPure_5866_ = crate::leanh::lean_ctor_get(v_toApplicative_5865_, 1);
                crate::leanh::lean_inc(v_toPure_5866_);
                crate::leanh::lean_dec_ref(v_toApplicative_5865_);
                v___x_5867_ = crate::leanh::lean_apply_2(
                    v_toPure_5866_,
                    crate::leanh::lean_box(0),
                    v___x_5858_,
                );
                return v___x_5867_;
            } else {
                let mut v___x_5868_: usize = 0;
                let mut v___x_5869_: usize = 0;
                let mut v___x_5870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_5868_ = 0usize;
                v___x_5869_ = lean_usize_of_nat(v___x_5857_);
                v___x_5870_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v_inst_5853_,
                    v___f_5863_,
                    v_log_5855_,
                    v___x_5868_,
                    v___x_5869_,
                    v___x_5858_,
                );
                return v___x_5870_;
            }
        } else {
            let mut v___x_5871_: usize = 0;
            let mut v___x_5872_: usize = 0;
            let mut v___x_5873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_5871_ = 0usize;
            v___x_5872_ = lean_usize_of_nat(v___x_5857_);
            v___x_5873_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v_inst_5853_,
                v___f_5863_,
                v_log_5855_,
                v___x_5871_,
                v___x_5872_,
                v___x_5858_,
            );
            return v___x_5873_;
        }
    }
}
pub unsafe fn l_Lake_Log_filter___lam__0(
    mut v_f_5874_: *mut crate::leanh::LeanObject,
    mut v_x1_5875_: *mut crate::leanh::LeanObject,
    mut v_x2_5876_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5878_: u8 = 0;
    crate::leanh::lean_inc_ref(v_x2_5876_);
    v___x_5877_ = crate::leanh::lean_apply_1(v_f_5874_, v_x2_5876_);
    v___x_5878_ = (crate::leanh::lean_unbox(v___x_5877_) as u8);
    if v___x_5878_ == 0 {
        crate::leanh::lean_dec_ref(v_x2_5876_);
        return v_x1_5875_;
    } else {
        let mut v___x_5879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5879_ = lean_array_push(v_x1_5875_, v_x2_5876_);
        return v___x_5879_;
    }
}
pub unsafe fn l_Lake_Log_filter(
    mut v_f_5899_: *mut crate::leanh::LeanObject,
    mut v_log_5900_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5905_: u8 = 0;
    v___x_5901_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5902_ = lean_array_get_size(v_log_5900_);
    v___x_5903_ = l_Lake_Log_empty___closed__0;
    v___x_5904_ = l_Lake_Log_filter___closed__9;
    v___x_5905_ = lean_nat_dec_lt(v___x_5901_, v___x_5902_);
    if v___x_5905_ == 0 {
        crate::leanh::lean_dec_ref(v_log_5900_);
        crate::leanh::lean_dec_ref(v_f_5899_);
        return v___x_5903_;
    } else {
        let mut v___f_5906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5907_: u8 = 0;
        v___f_5906_ = crate::leanh::lean_alloc_closure(
            l_Lake_Log_filter___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        crate::leanh::lean_closure_set(v___f_5906_, 0, v_f_5899_);
        v___x_5907_ = lean_nat_dec_le(v___x_5902_, v___x_5902_);
        if v___x_5907_ == 0 {
            if v___x_5905_ == 0 {
                crate::leanh::lean_dec_ref(v___f_5906_);
                crate::leanh::lean_dec_ref(v_log_5900_);
                return v___x_5903_;
            } else {
                let mut v___x_5908_: usize = 0;
                let mut v___x_5909_: usize = 0;
                let mut v___x_5910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_5908_ = 0usize;
                v___x_5909_ = lean_usize_of_nat(v___x_5902_);
                v___x_5910_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_5904_,
                    v___f_5906_,
                    v_log_5900_,
                    v___x_5908_,
                    v___x_5909_,
                    v___x_5903_,
                );
                return v___x_5910_;
            }
        } else {
            let mut v___x_5911_: usize = 0;
            let mut v___x_5912_: usize = 0;
            let mut v___x_5913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_5911_ = 0usize;
            v___x_5912_ = lean_usize_of_nat(v___x_5902_);
            v___x_5913_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_5904_,
                v___f_5906_,
                v_log_5900_,
                v___x_5911_,
                v___x_5912_,
                v___x_5903_,
            );
            return v___x_5913_;
        }
    }
}
pub unsafe fn l_Lake_Log_any___lam__0(
    mut v_f_5914_: *mut crate::leanh::LeanObject,
    mut v_x_5915_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5917_: u8 = 0;
    v___x_5916_ = crate::leanh::lean_apply_1(v_f_5914_, v_x_5915_);
    v___x_5917_ = (crate::leanh::lean_unbox(v___x_5916_) as u8);
    return v___x_5917_;
}
pub unsafe fn l_Lake_Log_any___lam__0___boxed(
    mut v_f_5918_: *mut crate::leanh::LeanObject,
    mut v_x_5919_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5920_: u8 = 0;
    let mut v_r_5921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5920_ = l_Lake_Log_any___lam__0(v_f_5918_, v_x_5919_);
    v_r_5921_ = crate::leanh::lean_box((v_res_5920_) as usize);
    return v_r_5921_;
}
pub unsafe fn l_Lake_Log_any(
    mut v_f_5922_: *mut crate::leanh::LeanObject,
    mut v_log_5923_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5927_: u8 = 0;
    v___x_5924_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5925_ = lean_array_get_size(v_log_5923_);
    v___x_5926_ = l_Lake_Log_filter___closed__9;
    v___x_5927_ = lean_nat_dec_lt(v___x_5924_, v___x_5925_);
    if v___x_5927_ == 0 {
        crate::leanh::lean_dec_ref(v_log_5923_);
        crate::leanh::lean_dec_ref(v_f_5922_);
        return v___x_5927_;
    } else {
        if v___x_5927_ == 0 {
            crate::leanh::lean_dec_ref(v_log_5923_);
            crate::leanh::lean_dec_ref(v_f_5922_);
            return v___x_5927_;
        } else {
            let mut v___f_5928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5929_: usize = 0;
            let mut v___x_5930_: usize = 0;
            let mut v___x_5931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5932_: u8 = 0;
            v___f_5928_ = crate::leanh::lean_alloc_closure(
                l_Lake_Log_any___lam__0___boxed as *mut core::ffi::c_void,
                2,
                1,
            );
            crate::leanh::lean_closure_set(v___f_5928_, 0, v_f_5922_);
            v___x_5929_ = 0usize;
            v___x_5930_ = lean_usize_of_nat(v___x_5925_);
            v___x_5931_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_5926_,
                v___f_5928_,
                v_log_5923_,
                v___x_5929_,
                v___x_5930_,
            );
            v___x_5932_ = (crate::leanh::lean_unbox(v___x_5931_) as u8);
            crate::leanh::lean_dec(v___x_5931_);
            return v___x_5932_;
        }
    }
}
pub unsafe fn l_Lake_Log_any___boxed(
    mut v_f_5933_: *mut crate::leanh::LeanObject,
    mut v_log_5934_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5935_: u8 = 0;
    let mut v_r_5936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5935_ = l_Lake_Log_any(v_f_5933_, v_log_5934_);
    v_r_5936_ = crate::leanh::lean_box((v_res_5935_) as usize);
    return v_r_5936_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_maxLv_spec__0(
    mut v_as_5937_: *mut crate::leanh::LeanObject,
    mut v_i_5938_: usize,
    mut v_stop_5939_: usize,
    mut v_b_5940_: u8,
) -> u8 {
    let mut v___y_5942_: u8 = 0;
    let mut v___x_5943_: usize = 0;
    let mut v___x_5944_: usize = 0;
    let mut v___x_5946_: u8 = 0;
    let mut v___x_5947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_level_5948_: u8 = 0;
    let mut v___x_5949_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5946_ = lean_usize_dec_eq(v_i_5938_, v_stop_5939_);
                if v___x_5946_ == 0 {
                    v___x_5947_ = lean_array_uget_borrowed(v_as_5937_, v_i_5938_);
                    v_level_5948_ = crate::leanh::lean_ctor_get_uint8(
                        v___x_5947_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    v___x_5949_ = l_Lake_instOrdLogLevel_ord(v_b_5940_, v_level_5948_);
                    if v___x_5949_ == 2 {
                        if v___x_5946_ == 0 {
                            v___y_5942_ = v_b_5940_;
                            state = 1;
                            continue;
                        } else {
                            v___y_5942_ = v_level_5948_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___y_5942_ = v_level_5948_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_5940_;
                }
            }
            1 => {
                v___x_5943_ = 1usize;
                v___x_5944_ = lean_usize_add(v_i_5938_, v___x_5943_);
                v_i_5938_ = v___x_5944_;
                v_b_5940_ = v___y_5942_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_maxLv_spec__0___boxed(
    mut v_as_5950_: *mut crate::leanh::LeanObject,
    mut v_i_5951_: *mut crate::leanh::LeanObject,
    mut v_stop_5952_: *mut crate::leanh::LeanObject,
    mut v_b_5953_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_5954_: usize = 0;
    let mut v_stop_boxed_5955_: usize = 0;
    let mut v_b_boxed_5956_: u8 = 0;
    let mut v_res_5957_: u8 = 0;
    let mut v_r_5958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5954_ = crate::leanh::lean_unbox_usize(v_i_5951_);
    crate::leanh::lean_dec(v_i_5951_);
    v_stop_boxed_5955_ = crate::leanh::lean_unbox_usize(v_stop_5952_);
    crate::leanh::lean_dec(v_stop_5952_);
    v_b_boxed_5956_ = (crate::leanh::lean_unbox(v_b_5953_) as u8);
    v_res_5957_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_maxLv_spec__0(v_as_5950_, v_i_boxed_5954_, v_stop_boxed_5955_, v_b_boxed_5956_);
    crate::leanh::lean_dec_ref(v_as_5950_);
    v_r_5958_ = crate::leanh::lean_box((v_res_5957_) as usize);
    return v_r_5958_;
}
pub unsafe fn l_Lake_Log_maxLv(mut v_log_5959_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_5960_: u8 = 0;
    let mut v___x_5961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5963_: u8 = 0;
    v___x_5960_ = 0;
    v___x_5961_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5962_ = lean_array_get_size(v_log_5959_);
    v___x_5963_ = lean_nat_dec_lt(v___x_5961_, v___x_5962_);
    if v___x_5963_ == 0 {
        return v___x_5960_;
    } else {
        let mut v___x_5964_: u8 = 0;
        v___x_5964_ = lean_nat_dec_le(v___x_5962_, v___x_5962_);
        if v___x_5964_ == 0 {
            if v___x_5963_ == 0 {
                return v___x_5960_;
            } else {
                let mut v___x_5965_: usize = 0;
                let mut v___x_5966_: usize = 0;
                let mut v___x_5967_: u8 = 0;
                v___x_5965_ = 0usize;
                v___x_5966_ = lean_usize_of_nat(v___x_5962_);
                v___x_5967_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_maxLv_spec__0(v_log_5959_, v___x_5965_, v___x_5966_, v___x_5960_);
                return v___x_5967_;
            }
        } else {
            let mut v___x_5968_: usize = 0;
            let mut v___x_5969_: usize = 0;
            let mut v___x_5970_: u8 = 0;
            v___x_5968_ = 0usize;
            v___x_5969_ = lean_usize_of_nat(v___x_5962_);
            v___x_5970_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_maxLv_spec__0(v_log_5959_, v___x_5968_, v___x_5969_, v___x_5960_);
            return v___x_5970_;
        }
    }
}
pub unsafe fn l_Lake_Log_maxLv___boxed(
    mut v_log_5971_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5972_: u8 = 0;
    let mut v_r_5973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5972_ = l_Lake_Log_maxLv(v_log_5971_);
    crate::leanh::lean_dec_ref(v_log_5971_);
    v_r_5973_ = crate::leanh::lean_box((v_res_5972_) as usize);
    return v_r_5973_;
}
pub unsafe fn l_Lake_pushLogEntry___redArg___lam__0(
    mut v_e_5974_: *mut crate::leanh::LeanObject,
    mut v_s_5975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5976_ = crate::leanh::lean_box(0);
    v___x_5977_ = lean_array_push(v_s_5975_, v_e_5974_);
    v___x_5978_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5978_, 0, v___x_5976_);
    crate::leanh::lean_ctor_set(v___x_5978_, 1, v___x_5977_);
    return v___x_5978_;
}
pub unsafe fn l_Lake_pushLogEntry___redArg(
    mut v_inst_5979_: *mut crate::leanh::LeanObject,
    mut v_e_5980_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_modifyGet_5981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_modifyGet_5981_ = crate::leanh::lean_ctor_get(v_inst_5979_, 2);
    crate::leanh::lean_inc(v_modifyGet_5981_);
    crate::leanh::lean_dec_ref(v_inst_5979_);
    v___f_5982_ = crate::leanh::lean_alloc_closure(
        l_Lake_pushLogEntry___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5982_, 0, v_e_5980_);
    v___x_5983_ =
        crate::leanh::lean_apply_2(v_modifyGet_5981_, crate::leanh::lean_box(0), v___f_5982_);
    return v___x_5983_;
}
pub unsafe fn l_Lake_pushLogEntry(
    mut v_m_5984_: *mut crate::leanh::LeanObject,
    mut v_inst_5985_: *mut crate::leanh::LeanObject,
    mut v_e_5986_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_modifyGet_5987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_modifyGet_5987_ = crate::leanh::lean_ctor_get(v_inst_5985_, 2);
    crate::leanh::lean_inc(v_modifyGet_5987_);
    crate::leanh::lean_dec_ref(v_inst_5985_);
    v___f_5988_ = crate::leanh::lean_alloc_closure(
        l_Lake_pushLogEntry___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5988_, 0, v_e_5986_);
    v___x_5989_ =
        crate::leanh::lean_apply_2(v_modifyGet_5987_, crate::leanh::lean_box(0), v___f_5988_);
    return v___x_5989_;
}
pub unsafe fn l_Lake_MonadLog_ofMonadState___redArg(
    mut v_inst_5990_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5991_ =
        crate::leanh::lean_alloc_closure(l_Lake_pushLogEntry as *mut core::ffi::c_void, 3, 2);
    crate::leanh::lean_closure_set(v___x_5991_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_5991_, 1, v_inst_5990_);
    return v___x_5991_;
}
pub unsafe fn l_Lake_MonadLog_ofMonadState(
    mut v_m_5992_: *mut crate::leanh::LeanObject,
    mut v_inst_5993_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5994_ =
        crate::leanh::lean_alloc_closure(l_Lake_pushLogEntry as *mut core::ffi::c_void, 3, 2);
    crate::leanh::lean_closure_set(v___x_5994_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_5994_, 1, v_inst_5993_);
    return v___x_5994_;
}
pub unsafe fn l_Lake_getLog___redArg(
    mut v_inst_5995_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_get_5996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_get_5996_ = crate::leanh::lean_ctor_get(v_inst_5995_, 0);
    crate::leanh::lean_inc(v_get_5996_);
    return v_get_5996_;
}
pub unsafe fn l_Lake_getLog___redArg___boxed(
    mut v_inst_5997_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5998_ = l_Lake_getLog___redArg(v_inst_5997_);
    crate::leanh::lean_dec_ref(v_inst_5997_);
    return v_res_5998_;
}
pub unsafe fn l_Lake_getLog(
    mut v_m_5999_: *mut crate::leanh::LeanObject,
    mut v_inst_6000_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_get_6001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_get_6001_ = crate::leanh::lean_ctor_get(v_inst_6000_, 0);
    crate::leanh::lean_inc(v_get_6001_);
    return v_get_6001_;
}
pub unsafe fn l_Lake_getLog___boxed(
    mut v_m_6002_: *mut crate::leanh::LeanObject,
    mut v_inst_6003_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6004_ = l_Lake_getLog(v_m_6002_, v_inst_6003_);
    crate::leanh::lean_dec_ref(v_inst_6003_);
    return v_res_6004_;
}
pub unsafe fn l_Lake_getLogPos___redArg___lam__0(
    mut v_x_6005_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6006_ = lean_array_get_size(v_x_6005_);
    return v___x_6006_;
}
pub unsafe fn l_Lake_getLogPos___redArg___lam__0___boxed(
    mut v_x_6007_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6008_ = l_Lake_getLogPos___redArg___lam__0(v_x_6007_);
    crate::leanh::lean_dec_ref(v_x_6007_);
    return v_res_6008_;
}
pub unsafe fn l_Lake_getLogPos___redArg(
    mut v_inst_6010_: *mut crate::leanh::LeanObject,
    mut v_inst_6011_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_6012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_get_6013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_6012_ = crate::leanh::lean_ctor_get(v_inst_6010_, 0);
    crate::leanh::lean_inc(v_map_6012_);
    crate::leanh::lean_dec_ref(v_inst_6010_);
    v_get_6013_ = crate::leanh::lean_ctor_get(v_inst_6011_, 0);
    crate::leanh::lean_inc(v_get_6013_);
    crate::leanh::lean_dec_ref(v_inst_6011_);
    v___f_6014_ = l_Lake_getLogPos___redArg___closed__0;
    v___x_6015_ = crate::leanh::lean_apply_4(
        v_map_6012_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_6014_,
        v_get_6013_,
    );
    return v___x_6015_;
}
pub unsafe fn l_Lake_getLogPos(
    mut v_m_6016_: *mut crate::leanh::LeanObject,
    mut v_inst_6017_: *mut crate::leanh::LeanObject,
    mut v_inst_6018_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_6019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_get_6020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_6019_ = crate::leanh::lean_ctor_get(v_inst_6017_, 0);
    crate::leanh::lean_inc(v_map_6019_);
    crate::leanh::lean_dec_ref(v_inst_6017_);
    v_get_6020_ = crate::leanh::lean_ctor_get(v_inst_6018_, 0);
    crate::leanh::lean_inc(v_get_6020_);
    crate::leanh::lean_dec_ref(v_inst_6018_);
    v___f_6021_ = l_Lake_getLogPos___redArg___closed__0;
    v___x_6022_ = crate::leanh::lean_apply_4(
        v_map_6019_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_6021_,
        v_get_6020_,
    );
    return v___x_6022_;
}
pub unsafe fn l_Lake_takeLog___redArg___lam__0(
    mut v_log_6023_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6024_ = l_Lake_Log_empty___closed__0;
    v___x_6025_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6025_, 0, v_log_6023_);
    crate::leanh::lean_ctor_set(v___x_6025_, 1, v___x_6024_);
    return v___x_6025_;
}
pub unsafe fn l_Lake_takeLog___redArg(
    mut v_inst_6027_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_modifyGet_6028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_modifyGet_6028_ = crate::leanh::lean_ctor_get(v_inst_6027_, 2);
    crate::leanh::lean_inc(v_modifyGet_6028_);
    crate::leanh::lean_dec_ref(v_inst_6027_);
    v___f_6029_ = l_Lake_takeLog___redArg___closed__0;
    v___x_6030_ =
        crate::leanh::lean_apply_2(v_modifyGet_6028_, crate::leanh::lean_box(0), v___f_6029_);
    return v___x_6030_;
}
pub unsafe fn l_Lake_takeLog(
    mut v_m_6031_: *mut crate::leanh::LeanObject,
    mut v_inst_6032_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_modifyGet_6033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_modifyGet_6033_ = crate::leanh::lean_ctor_get(v_inst_6032_, 2);
    crate::leanh::lean_inc(v_modifyGet_6033_);
    crate::leanh::lean_dec_ref(v_inst_6032_);
    v___f_6034_ = l_Lake_takeLog___redArg___closed__0;
    v___x_6035_ =
        crate::leanh::lean_apply_2(v_modifyGet_6033_, crate::leanh::lean_box(0), v___f_6034_);
    return v___x_6035_;
}
pub unsafe fn l_Lake_takeLogFrom___redArg___lam__0(
    mut v_pos_6036_: *mut crate::leanh::LeanObject,
    mut v_log_6037_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6038_ = lean_array_get_size(v_log_6037_);
    crate::leanh::lean_inc(v_pos_6036_);
    v___x_6039_ = l_Array_extract___redArg(v_log_6037_, v_pos_6036_, v___x_6038_);
    v___x_6040_ = l_Array_shrink___redArg(v_log_6037_, v_pos_6036_);
    crate::leanh::lean_dec(v_pos_6036_);
    v___x_6041_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6041_, 0, v___x_6039_);
    crate::leanh::lean_ctor_set(v___x_6041_, 1, v___x_6040_);
    return v___x_6041_;
}
pub unsafe fn l_Lake_takeLogFrom___redArg(
    mut v_inst_6042_: *mut crate::leanh::LeanObject,
    mut v_pos_6043_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_modifyGet_6044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_modifyGet_6044_ = crate::leanh::lean_ctor_get(v_inst_6042_, 2);
    crate::leanh::lean_inc(v_modifyGet_6044_);
    crate::leanh::lean_dec_ref(v_inst_6042_);
    v___f_6045_ = crate::leanh::lean_alloc_closure(
        l_Lake_takeLogFrom___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_6045_, 0, v_pos_6043_);
    v___x_6046_ =
        crate::leanh::lean_apply_2(v_modifyGet_6044_, crate::leanh::lean_box(0), v___f_6045_);
    return v___x_6046_;
}
pub unsafe fn l_Lake_takeLogFrom(
    mut v_m_6047_: *mut crate::leanh::LeanObject,
    mut v_inst_6048_: *mut crate::leanh::LeanObject,
    mut v_pos_6049_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_modifyGet_6050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_modifyGet_6050_ = crate::leanh::lean_ctor_get(v_inst_6048_, 2);
    crate::leanh::lean_inc(v_modifyGet_6050_);
    crate::leanh::lean_dec_ref(v_inst_6048_);
    v___f_6051_ = crate::leanh::lean_alloc_closure(
        l_Lake_takeLogFrom___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_6051_, 0, v_pos_6049_);
    v___x_6052_ =
        crate::leanh::lean_apply_2(v_modifyGet_6050_, crate::leanh::lean_box(0), v___f_6051_);
    return v___x_6052_;
}
pub unsafe fn l_Lake_dropLogFrom___redArg___lam__0(
    mut v_pos_6053_: *mut crate::leanh::LeanObject,
    mut v_s_6054_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6055_ = crate::leanh::lean_box(0);
    v___x_6056_ = l_Array_shrink___redArg(v_s_6054_, v_pos_6053_);
    v___x_6057_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6057_, 0, v___x_6055_);
    crate::leanh::lean_ctor_set(v___x_6057_, 1, v___x_6056_);
    return v___x_6057_;
}
pub unsafe fn l_Lake_dropLogFrom___redArg___lam__0___boxed(
    mut v_pos_6058_: *mut crate::leanh::LeanObject,
    mut v_s_6059_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6060_ = l_Lake_dropLogFrom___redArg___lam__0(v_pos_6058_, v_s_6059_);
    crate::leanh::lean_dec(v_pos_6058_);
    return v_res_6060_;
}
pub unsafe fn l_Lake_dropLogFrom___redArg(
    mut v_inst_6061_: *mut crate::leanh::LeanObject,
    mut v_pos_6062_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_modifyGet_6063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_modifyGet_6063_ = crate::leanh::lean_ctor_get(v_inst_6061_, 2);
    crate::leanh::lean_inc(v_modifyGet_6063_);
    crate::leanh::lean_dec_ref(v_inst_6061_);
    v___f_6064_ = crate::leanh::lean_alloc_closure(
        l_Lake_dropLogFrom___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_6064_, 0, v_pos_6062_);
    v___x_6065_ =
        crate::leanh::lean_apply_2(v_modifyGet_6063_, crate::leanh::lean_box(0), v___f_6064_);
    return v___x_6065_;
}
pub unsafe fn l_Lake_dropLogFrom(
    mut v_m_6066_: *mut crate::leanh::LeanObject,
    mut v_inst_6067_: *mut crate::leanh::LeanObject,
    mut v_pos_6068_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_modifyGet_6069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_modifyGet_6069_ = crate::leanh::lean_ctor_get(v_inst_6067_, 2);
    crate::leanh::lean_inc(v_modifyGet_6069_);
    crate::leanh::lean_dec_ref(v_inst_6067_);
    v___f_6070_ = crate::leanh::lean_alloc_closure(
        l_Lake_dropLogFrom___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_6070_, 0, v_pos_6068_);
    v___x_6071_ =
        crate::leanh::lean_apply_2(v_modifyGet_6069_, crate::leanh::lean_box(0), v___f_6070_);
    return v___x_6071_;
}
pub unsafe fn l_Lake_extractLog___redArg___lam__1(
    mut v_iniPos_6072_: *mut crate::leanh::LeanObject,
    mut v_toPure_6073_: *mut crate::leanh::LeanObject,
    mut v_log_6074_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6075_ = lean_array_get_size(v_log_6074_);
    v___x_6076_ = l_Array_extract___redArg(v_log_6074_, v_iniPos_6072_, v___x_6075_);
    v___x_6077_ =
        crate::leanh::lean_apply_2(v_toPure_6073_, crate::leanh::lean_box(0), v___x_6076_);
    return v___x_6077_;
}
pub unsafe fn l_Lake_extractLog___redArg___lam__1___boxed(
    mut v_iniPos_6078_: *mut crate::leanh::LeanObject,
    mut v_toPure_6079_: *mut crate::leanh::LeanObject,
    mut v_log_6080_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6081_ = l_Lake_extractLog___redArg___lam__1(v_iniPos_6078_, v_toPure_6079_, v_log_6080_);
    crate::leanh::lean_dec_ref(v_log_6080_);
    return v_res_6081_;
}
pub unsafe fn l_Lake_extractLog___redArg___lam__0(
    mut v_toBind_6082_: *mut crate::leanh::LeanObject,
    mut v_get_6083_: *mut crate::leanh::LeanObject,
    mut v___f_6084_: *mut crate::leanh::LeanObject,
    mut v_____r_6085_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6086_ = crate::leanh::lean_apply_4(
        v_toBind_6082_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_get_6083_,
        v___f_6084_,
    );
    return v___x_6086_;
}
pub unsafe fn l_Lake_extractLog___redArg___lam__2(
    mut v_toPure_6087_: *mut crate::leanh::LeanObject,
    mut v_toBind_6088_: *mut crate::leanh::LeanObject,
    mut v_get_6089_: *mut crate::leanh::LeanObject,
    mut v_x_6090_: *mut crate::leanh::LeanObject,
    mut v_iniPos_6091_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_6092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_6092_ = crate::leanh::lean_alloc_closure(
        l_Lake_extractLog___redArg___lam__1___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_6092_, 0, v_iniPos_6091_);
    crate::leanh::lean_closure_set(v___f_6092_, 1, v_toPure_6087_);
    crate::leanh::lean_inc(v_toBind_6088_);
    v___f_6093_ = crate::leanh::lean_alloc_closure(
        l_Lake_extractLog___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_6093_, 0, v_toBind_6088_);
    crate::leanh::lean_closure_set(v___f_6093_, 1, v_get_6089_);
    crate::leanh::lean_closure_set(v___f_6093_, 2, v___f_6092_);
    v___x_6094_ = crate::leanh::lean_apply_4(
        v_toBind_6088_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_x_6090_,
        v___f_6093_,
    );
    return v___x_6094_;
}
pub unsafe fn l_Lake_extractLog___redArg(
    mut v_inst_6095_: *mut crate::leanh::LeanObject,
    mut v_inst_6096_: *mut crate::leanh::LeanObject,
    mut v_x_6097_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_6098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_6099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_6100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_6101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_6102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_get_6103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_6098_ = crate::leanh::lean_ctor_get(v_inst_6095_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_6098_);
    v_toFunctor_6099_ = crate::leanh::lean_ctor_get(v_toApplicative_6098_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_6099_);
    v_toBind_6100_ = crate::leanh::lean_ctor_get(v_inst_6095_, 1);
    crate::leanh::lean_inc_n(v_toBind_6100_, 2);
    crate::leanh::lean_dec_ref(v_inst_6095_);
    v_toPure_6101_ = crate::leanh::lean_ctor_get(v_toApplicative_6098_, 1);
    crate::leanh::lean_inc(v_toPure_6101_);
    crate::leanh::lean_dec_ref(v_toApplicative_6098_);
    v_map_6102_ = crate::leanh::lean_ctor_get(v_toFunctor_6099_, 0);
    crate::leanh::lean_inc(v_map_6102_);
    crate::leanh::lean_dec_ref(v_toFunctor_6099_);
    v_get_6103_ = crate::leanh::lean_ctor_get(v_inst_6096_, 0);
    crate::leanh::lean_inc_n(v_get_6103_, 2);
    crate::leanh::lean_dec_ref(v_inst_6096_);
    v___f_6104_ = l_Lake_getLogPos___redArg___closed__0;
    v___f_6105_ = crate::leanh::lean_alloc_closure(
        l_Lake_extractLog___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_6105_, 0, v_toPure_6101_);
    crate::leanh::lean_closure_set(v___f_6105_, 1, v_toBind_6100_);
    crate::leanh::lean_closure_set(v___f_6105_, 2, v_get_6103_);
    crate::leanh::lean_closure_set(v___f_6105_, 3, v_x_6097_);
    v___x_6106_ = crate::leanh::lean_apply_4(
        v_map_6102_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_6104_,
        v_get_6103_,
    );
    v___x_6107_ = crate::leanh::lean_apply_4(
        v_toBind_6100_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_6106_,
        v___f_6105_,
    );
    return v___x_6107_;
}
pub unsafe fn l_Lake_extractLog(
    mut v_m_6108_: *mut crate::leanh::LeanObject,
    mut v_inst_6109_: *mut crate::leanh::LeanObject,
    mut v_inst_6110_: *mut crate::leanh::LeanObject,
    mut v_x_6111_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_6112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_6113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_6114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_6115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_6116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_get_6117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_6112_ = crate::leanh::lean_ctor_get(v_inst_6109_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_6112_);
    v_toFunctor_6113_ = crate::leanh::lean_ctor_get(v_toApplicative_6112_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_6113_);
    v_toBind_6114_ = crate::leanh::lean_ctor_get(v_inst_6109_, 1);
    crate::leanh::lean_inc_n(v_toBind_6114_, 2);
    crate::leanh::lean_dec_ref(v_inst_6109_);
    v_toPure_6115_ = crate::leanh::lean_ctor_get(v_toApplicative_6112_, 1);
    crate::leanh::lean_inc(v_toPure_6115_);
    crate::leanh::lean_dec_ref(v_toApplicative_6112_);
    v_map_6116_ = crate::leanh::lean_ctor_get(v_toFunctor_6113_, 0);
    crate::leanh::lean_inc(v_map_6116_);
    crate::leanh::lean_dec_ref(v_toFunctor_6113_);
    v_get_6117_ = crate::leanh::lean_ctor_get(v_inst_6110_, 0);
    crate::leanh::lean_inc_n(v_get_6117_, 2);
    crate::leanh::lean_dec_ref(v_inst_6110_);
    v___f_6118_ = l_Lake_getLogPos___redArg___closed__0;
    v___f_6119_ = crate::leanh::lean_alloc_closure(
        l_Lake_extractLog___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_6119_, 0, v_toPure_6115_);
    crate::leanh::lean_closure_set(v___f_6119_, 1, v_toBind_6114_);
    crate::leanh::lean_closure_set(v___f_6119_, 2, v_get_6117_);
    crate::leanh::lean_closure_set(v___f_6119_, 3, v_x_6111_);
    v___x_6120_ = crate::leanh::lean_apply_4(
        v_map_6116_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_6118_,
        v_get_6117_,
    );
    v___x_6121_ = crate::leanh::lean_apply_4(
        v_toBind_6114_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_6120_,
        v___f_6119_,
    );
    return v___x_6121_;
}
pub unsafe fn l_Lake_withExtractLog___redArg___lam__1(
    mut v_iniPos_6122_: *mut crate::leanh::LeanObject,
    mut v_a_6123_: *mut crate::leanh::LeanObject,
    mut v_toPure_6124_: *mut crate::leanh::LeanObject,
    mut v_log_6125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6126_ = lean_array_get_size(v_log_6125_);
    v___x_6127_ = l_Array_extract___redArg(v_log_6125_, v_iniPos_6122_, v___x_6126_);
    v___x_6128_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6128_, 0, v_a_6123_);
    crate::leanh::lean_ctor_set(v___x_6128_, 1, v___x_6127_);
    v___x_6129_ =
        crate::leanh::lean_apply_2(v_toPure_6124_, crate::leanh::lean_box(0), v___x_6128_);
    return v___x_6129_;
}
pub unsafe fn l_Lake_withExtractLog___redArg___lam__1___boxed(
    mut v_iniPos_6130_: *mut crate::leanh::LeanObject,
    mut v_a_6131_: *mut crate::leanh::LeanObject,
    mut v_toPure_6132_: *mut crate::leanh::LeanObject,
    mut v_log_6133_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6134_ = l_Lake_withExtractLog___redArg___lam__1(
        v_iniPos_6130_,
        v_a_6131_,
        v_toPure_6132_,
        v_log_6133_,
    );
    crate::leanh::lean_dec_ref(v_log_6133_);
    return v_res_6134_;
}
pub unsafe fn l_Lake_withExtractLog___redArg___lam__0(
    mut v_iniPos_6135_: *mut crate::leanh::LeanObject,
    mut v_toPure_6136_: *mut crate::leanh::LeanObject,
    mut v_toBind_6137_: *mut crate::leanh::LeanObject,
    mut v_get_6138_: *mut crate::leanh::LeanObject,
    mut v_a_6139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_6140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_6140_ = crate::leanh::lean_alloc_closure(
        l_Lake_withExtractLog___redArg___lam__1___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_6140_, 0, v_iniPos_6135_);
    crate::leanh::lean_closure_set(v___f_6140_, 1, v_a_6139_);
    crate::leanh::lean_closure_set(v___f_6140_, 2, v_toPure_6136_);
    v___x_6141_ = crate::leanh::lean_apply_4(
        v_toBind_6137_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_get_6138_,
        v___f_6140_,
    );
    return v___x_6141_;
}
pub unsafe fn l_Lake_withExtractLog___redArg___lam__2(
    mut v_toPure_6142_: *mut crate::leanh::LeanObject,
    mut v_toBind_6143_: *mut crate::leanh::LeanObject,
    mut v_get_6144_: *mut crate::leanh::LeanObject,
    mut v_x_6145_: *mut crate::leanh::LeanObject,
    mut v_iniPos_6146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_6147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_toBind_6143_);
    v___f_6147_ = crate::leanh::lean_alloc_closure(
        l_Lake_withExtractLog___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_6147_, 0, v_iniPos_6146_);
    crate::leanh::lean_closure_set(v___f_6147_, 1, v_toPure_6142_);
    crate::leanh::lean_closure_set(v___f_6147_, 2, v_toBind_6143_);
    crate::leanh::lean_closure_set(v___f_6147_, 3, v_get_6144_);
    v___x_6148_ = crate::leanh::lean_apply_4(
        v_toBind_6143_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_x_6145_,
        v___f_6147_,
    );
    return v___x_6148_;
}
pub unsafe fn l_Lake_withExtractLog___redArg(
    mut v_inst_6149_: *mut crate::leanh::LeanObject,
    mut v_inst_6150_: *mut crate::leanh::LeanObject,
    mut v_x_6151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_6152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_6153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_6154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_6155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_6156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_get_6157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_6152_ = crate::leanh::lean_ctor_get(v_inst_6149_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_6152_);
    v_toFunctor_6153_ = crate::leanh::lean_ctor_get(v_toApplicative_6152_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_6153_);
    v_toBind_6154_ = crate::leanh::lean_ctor_get(v_inst_6149_, 1);
    crate::leanh::lean_inc_n(v_toBind_6154_, 2);
    crate::leanh::lean_dec_ref(v_inst_6149_);
    v_toPure_6155_ = crate::leanh::lean_ctor_get(v_toApplicative_6152_, 1);
    crate::leanh::lean_inc(v_toPure_6155_);
    crate::leanh::lean_dec_ref(v_toApplicative_6152_);
    v_map_6156_ = crate::leanh::lean_ctor_get(v_toFunctor_6153_, 0);
    crate::leanh::lean_inc(v_map_6156_);
    crate::leanh::lean_dec_ref(v_toFunctor_6153_);
    v_get_6157_ = crate::leanh::lean_ctor_get(v_inst_6150_, 0);
    crate::leanh::lean_inc_n(v_get_6157_, 2);
    crate::leanh::lean_dec_ref(v_inst_6150_);
    v___f_6158_ = l_Lake_getLogPos___redArg___closed__0;
    v___f_6159_ = crate::leanh::lean_alloc_closure(
        l_Lake_withExtractLog___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_6159_, 0, v_toPure_6155_);
    crate::leanh::lean_closure_set(v___f_6159_, 1, v_toBind_6154_);
    crate::leanh::lean_closure_set(v___f_6159_, 2, v_get_6157_);
    crate::leanh::lean_closure_set(v___f_6159_, 3, v_x_6151_);
    v___x_6160_ = crate::leanh::lean_apply_4(
        v_map_6156_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_6158_,
        v_get_6157_,
    );
    v___x_6161_ = crate::leanh::lean_apply_4(
        v_toBind_6154_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_6160_,
        v___f_6159_,
    );
    return v___x_6161_;
}
pub unsafe fn l_Lake_withExtractLog(
    mut v_m_6162_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_6163_: *mut crate::leanh::LeanObject,
    mut v_inst_6164_: *mut crate::leanh::LeanObject,
    mut v_inst_6165_: *mut crate::leanh::LeanObject,
    mut v_x_6166_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_6167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_6168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_6169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_6170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_6171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_get_6172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_6167_ = crate::leanh::lean_ctor_get(v_inst_6164_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_6167_);
    v_toFunctor_6168_ = crate::leanh::lean_ctor_get(v_toApplicative_6167_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_6168_);
    v_toBind_6169_ = crate::leanh::lean_ctor_get(v_inst_6164_, 1);
    crate::leanh::lean_inc_n(v_toBind_6169_, 2);
    crate::leanh::lean_dec_ref(v_inst_6164_);
    v_toPure_6170_ = crate::leanh::lean_ctor_get(v_toApplicative_6167_, 1);
    crate::leanh::lean_inc(v_toPure_6170_);
    crate::leanh::lean_dec_ref(v_toApplicative_6167_);
    v_map_6171_ = crate::leanh::lean_ctor_get(v_toFunctor_6168_, 0);
    crate::leanh::lean_inc(v_map_6171_);
    crate::leanh::lean_dec_ref(v_toFunctor_6168_);
    v_get_6172_ = crate::leanh::lean_ctor_get(v_inst_6165_, 0);
    crate::leanh::lean_inc_n(v_get_6172_, 2);
    crate::leanh::lean_dec_ref(v_inst_6165_);
    v___f_6173_ = l_Lake_getLogPos___redArg___closed__0;
    v___f_6174_ = crate::leanh::lean_alloc_closure(
        l_Lake_withExtractLog___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_6174_, 0, v_toPure_6170_);
    crate::leanh::lean_closure_set(v___f_6174_, 1, v_toBind_6169_);
    crate::leanh::lean_closure_set(v___f_6174_, 2, v_get_6172_);
    crate::leanh::lean_closure_set(v___f_6174_, 3, v_x_6166_);
    v___x_6175_ = crate::leanh::lean_apply_4(
        v_map_6171_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_6173_,
        v_get_6172_,
    );
    v___x_6176_ = crate::leanh::lean_apply_4(
        v_toBind_6169_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_6175_,
        v___f_6174_,
    );
    return v___x_6176_;
}
pub unsafe fn l_Lake_throwIfLogs___redArg___lam__1(
    mut v_iniPos_6177_: *mut crate::leanh::LeanObject,
    mut v_inst_6178_: *mut crate::leanh::LeanObject,
    mut v_toPure_6179_: *mut crate::leanh::LeanObject,
    mut v_a_6180_: *mut crate::leanh::LeanObject,
    mut v_endPos_6181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6182_: u8 = 0;
    v___x_6182_ = lean_nat_dec_eq(v_iniPos_6177_, v_endPos_6181_);
    if v___x_6182_ == 0 {
        let mut v_throw_6183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_a_6180_);
        crate::leanh::lean_dec(v_toPure_6179_);
        v_throw_6183_ = crate::leanh::lean_ctor_get(v_inst_6178_, 0);
        crate::leanh::lean_inc(v_throw_6183_);
        crate::leanh::lean_dec_ref(v_inst_6178_);
        v___x_6184_ =
            crate::leanh::lean_apply_2(v_throw_6183_, crate::leanh::lean_box(0), v_iniPos_6177_);
        return v___x_6184_;
    } else {
        let mut v___x_6185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_inst_6178_);
        crate::leanh::lean_dec(v_iniPos_6177_);
        v___x_6185_ =
            crate::leanh::lean_apply_2(v_toPure_6179_, crate::leanh::lean_box(0), v_a_6180_);
        return v___x_6185_;
    }
}
pub unsafe fn l_Lake_throwIfLogs___redArg___lam__1___boxed(
    mut v_iniPos_6186_: *mut crate::leanh::LeanObject,
    mut v_inst_6187_: *mut crate::leanh::LeanObject,
    mut v_toPure_6188_: *mut crate::leanh::LeanObject,
    mut v_a_6189_: *mut crate::leanh::LeanObject,
    mut v_endPos_6190_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6191_ = l_Lake_throwIfLogs___redArg___lam__1(
        v_iniPos_6186_,
        v_inst_6187_,
        v_toPure_6188_,
        v_a_6189_,
        v_endPos_6190_,
    );
    crate::leanh::lean_dec(v_endPos_6190_);
    return v_res_6191_;
}
pub unsafe fn l_Lake_throwIfLogs___redArg___lam__0(
    mut v_iniPos_6192_: *mut crate::leanh::LeanObject,
    mut v_inst_6193_: *mut crate::leanh::LeanObject,
    mut v_toPure_6194_: *mut crate::leanh::LeanObject,
    mut v_toBind_6195_: *mut crate::leanh::LeanObject,
    mut v___x_6196_: *mut crate::leanh::LeanObject,
    mut v_a_6197_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_6198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_6198_ = crate::leanh::lean_alloc_closure(
        l_Lake_throwIfLogs___redArg___lam__1___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_6198_, 0, v_iniPos_6192_);
    crate::leanh::lean_closure_set(v___f_6198_, 1, v_inst_6193_);
    crate::leanh::lean_closure_set(v___f_6198_, 2, v_toPure_6194_);
    crate::leanh::lean_closure_set(v___f_6198_, 3, v_a_6197_);
    v___x_6199_ = crate::leanh::lean_apply_4(
        v_toBind_6195_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_6196_,
        v___f_6198_,
    );
    return v___x_6199_;
}
pub unsafe fn l_Lake_throwIfLogs___redArg___lam__2(
    mut v_inst_6200_: *mut crate::leanh::LeanObject,
    mut v_toPure_6201_: *mut crate::leanh::LeanObject,
    mut v_toBind_6202_: *mut crate::leanh::LeanObject,
    mut v___x_6203_: *mut crate::leanh::LeanObject,
    mut v_x_6204_: *mut crate::leanh::LeanObject,
    mut v_iniPos_6205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_6206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_toBind_6202_);
    v___f_6206_ = crate::leanh::lean_alloc_closure(
        l_Lake_throwIfLogs___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_6206_, 0, v_iniPos_6205_);
    crate::leanh::lean_closure_set(v___f_6206_, 1, v_inst_6200_);
    crate::leanh::lean_closure_set(v___f_6206_, 2, v_toPure_6201_);
    crate::leanh::lean_closure_set(v___f_6206_, 3, v_toBind_6202_);
    crate::leanh::lean_closure_set(v___f_6206_, 4, v___x_6203_);
    v___x_6207_ = crate::leanh::lean_apply_4(
        v_toBind_6202_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_x_6204_,
        v___f_6206_,
    );
    return v___x_6207_;
}
pub unsafe fn l_Lake_throwIfLogs___redArg(
    mut v_inst_6208_: *mut crate::leanh::LeanObject,
    mut v_inst_6209_: *mut crate::leanh::LeanObject,
    mut v_inst_6210_: *mut crate::leanh::LeanObject,
    mut v_x_6211_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_6212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_6213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_6214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_6215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_6216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_get_6217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_6212_ = crate::leanh::lean_ctor_get(v_inst_6208_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_6212_);
    v_toFunctor_6213_ = crate::leanh::lean_ctor_get(v_toApplicative_6212_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_6213_);
    v_toBind_6214_ = crate::leanh::lean_ctor_get(v_inst_6208_, 1);
    crate::leanh::lean_inc_n(v_toBind_6214_, 2);
    crate::leanh::lean_dec_ref(v_inst_6208_);
    v_toPure_6215_ = crate::leanh::lean_ctor_get(v_toApplicative_6212_, 1);
    crate::leanh::lean_inc(v_toPure_6215_);
    crate::leanh::lean_dec_ref(v_toApplicative_6212_);
    v_map_6216_ = crate::leanh::lean_ctor_get(v_toFunctor_6213_, 0);
    crate::leanh::lean_inc(v_map_6216_);
    crate::leanh::lean_dec_ref(v_toFunctor_6213_);
    v_get_6217_ = crate::leanh::lean_ctor_get(v_inst_6209_, 0);
    crate::leanh::lean_inc(v_get_6217_);
    crate::leanh::lean_dec_ref(v_inst_6209_);
    v___f_6218_ = l_Lake_getLogPos___redArg___closed__0;
    v___x_6219_ = crate::leanh::lean_apply_4(
        v_map_6216_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_6218_,
        v_get_6217_,
    );
    crate::leanh::lean_inc(v___x_6219_);
    v___f_6220_ = crate::leanh::lean_alloc_closure(
        l_Lake_throwIfLogs___redArg___lam__2 as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_6220_, 0, v_inst_6210_);
    crate::leanh::lean_closure_set(v___f_6220_, 1, v_toPure_6215_);
    crate::leanh::lean_closure_set(v___f_6220_, 2, v_toBind_6214_);
    crate::leanh::lean_closure_set(v___f_6220_, 3, v___x_6219_);
    crate::leanh::lean_closure_set(v___f_6220_, 4, v_x_6211_);
    v___x_6221_ = crate::leanh::lean_apply_4(
        v_toBind_6214_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_6219_,
        v___f_6220_,
    );
    return v___x_6221_;
}
pub unsafe fn l_Lake_throwIfLogs(
    mut v_m_6222_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_6223_: *mut crate::leanh::LeanObject,
    mut v_inst_6224_: *mut crate::leanh::LeanObject,
    mut v_inst_6225_: *mut crate::leanh::LeanObject,
    mut v_inst_6226_: *mut crate::leanh::LeanObject,
    mut v_x_6227_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_6228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_6229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_6230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_6231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_6232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_get_6233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_6228_ = crate::leanh::lean_ctor_get(v_inst_6224_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_6228_);
    v_toFunctor_6229_ = crate::leanh::lean_ctor_get(v_toApplicative_6228_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_6229_);
    v_toBind_6230_ = crate::leanh::lean_ctor_get(v_inst_6224_, 1);
    crate::leanh::lean_inc_n(v_toBind_6230_, 2);
    crate::leanh::lean_dec_ref(v_inst_6224_);
    v_toPure_6231_ = crate::leanh::lean_ctor_get(v_toApplicative_6228_, 1);
    crate::leanh::lean_inc(v_toPure_6231_);
    crate::leanh::lean_dec_ref(v_toApplicative_6228_);
    v_map_6232_ = crate::leanh::lean_ctor_get(v_toFunctor_6229_, 0);
    crate::leanh::lean_inc(v_map_6232_);
    crate::leanh::lean_dec_ref(v_toFunctor_6229_);
    v_get_6233_ = crate::leanh::lean_ctor_get(v_inst_6225_, 0);
    crate::leanh::lean_inc(v_get_6233_);
    crate::leanh::lean_dec_ref(v_inst_6225_);
    v___f_6234_ = l_Lake_getLogPos___redArg___closed__0;
    v___x_6235_ = crate::leanh::lean_apply_4(
        v_map_6232_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_6234_,
        v_get_6233_,
    );
    crate::leanh::lean_inc(v___x_6235_);
    v___f_6236_ = crate::leanh::lean_alloc_closure(
        l_Lake_throwIfLogs___redArg___lam__2 as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_6236_, 0, v_inst_6226_);
    crate::leanh::lean_closure_set(v___f_6236_, 1, v_toPure_6231_);
    crate::leanh::lean_closure_set(v___f_6236_, 2, v_toBind_6230_);
    crate::leanh::lean_closure_set(v___f_6236_, 3, v___x_6235_);
    crate::leanh::lean_closure_set(v___f_6236_, 4, v_x_6227_);
    v___x_6237_ = crate::leanh::lean_apply_4(
        v_toBind_6230_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_6235_,
        v___f_6236_,
    );
    return v___x_6237_;
}
pub unsafe fn l_Lake_withLogErrorPos___redArg___lam__1(
    mut v_throw_6238_: *mut crate::leanh::LeanObject,
    mut v_iniPos_6239_: *mut crate::leanh::LeanObject,
    mut v_x_6240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6241_ =
        crate::leanh::lean_apply_2(v_throw_6238_, crate::leanh::lean_box(0), v_iniPos_6239_);
    return v___x_6241_;
}
pub unsafe fn l_Lake_withLogErrorPos___redArg___lam__1___boxed(
    mut v_throw_6242_: *mut crate::leanh::LeanObject,
    mut v_iniPos_6243_: *mut crate::leanh::LeanObject,
    mut v_x_6244_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6245_ =
        l_Lake_withLogErrorPos___redArg___lam__1(v_throw_6242_, v_iniPos_6243_, v_x_6244_);
    crate::leanh::lean_dec(v_x_6244_);
    return v_res_6245_;
}
pub unsafe fn l_Lake_withLogErrorPos___redArg___lam__0(
    mut v_inst_6246_: *mut crate::leanh::LeanObject,
    mut v_self_6247_: *mut crate::leanh::LeanObject,
    mut v_iniPos_6248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_throw_6249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tryCatch_6250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_throw_6249_ = crate::leanh::lean_ctor_get(v_inst_6246_, 0);
    crate::leanh::lean_inc(v_throw_6249_);
    v_tryCatch_6250_ = crate::leanh::lean_ctor_get(v_inst_6246_, 1);
    crate::leanh::lean_inc(v_tryCatch_6250_);
    crate::leanh::lean_dec_ref(v_inst_6246_);
    v___f_6251_ = crate::leanh::lean_alloc_closure(
        l_Lake_withLogErrorPos___redArg___lam__1___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_6251_, 0, v_throw_6249_);
    crate::leanh::lean_closure_set(v___f_6251_, 1, v_iniPos_6248_);
    v___x_6252_ = crate::leanh::lean_apply_3(
        v_tryCatch_6250_,
        crate::leanh::lean_box(0),
        v_self_6247_,
        v___f_6251_,
    );
    return v___x_6252_;
}
pub unsafe fn l_Lake_withLogErrorPos___redArg(
    mut v_inst_6253_: *mut crate::leanh::LeanObject,
    mut v_inst_6254_: *mut crate::leanh::LeanObject,
    mut v_inst_6255_: *mut crate::leanh::LeanObject,
    mut v_self_6256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_6257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_6258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_6259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_6260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_get_6261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_6257_ = crate::leanh::lean_ctor_get(v_inst_6253_, 0);
    v_toFunctor_6258_ = crate::leanh::lean_ctor_get(v_toApplicative_6257_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_6258_);
    v_toBind_6259_ = crate::leanh::lean_ctor_get(v_inst_6253_, 1);
    crate::leanh::lean_inc(v_toBind_6259_);
    crate::leanh::lean_dec_ref(v_inst_6253_);
    v_map_6260_ = crate::leanh::lean_ctor_get(v_toFunctor_6258_, 0);
    crate::leanh::lean_inc(v_map_6260_);
    crate::leanh::lean_dec_ref(v_toFunctor_6258_);
    v_get_6261_ = crate::leanh::lean_ctor_get(v_inst_6254_, 0);
    crate::leanh::lean_inc(v_get_6261_);
    crate::leanh::lean_dec_ref(v_inst_6254_);
    v___f_6262_ = l_Lake_getLogPos___redArg___closed__0;
    v___f_6263_ = crate::leanh::lean_alloc_closure(
        l_Lake_withLogErrorPos___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_6263_, 0, v_inst_6255_);
    crate::leanh::lean_closure_set(v___f_6263_, 1, v_self_6256_);
    v___x_6264_ = crate::leanh::lean_apply_4(
        v_map_6260_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_6262_,
        v_get_6261_,
    );
    v___x_6265_ = crate::leanh::lean_apply_4(
        v_toBind_6259_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_6264_,
        v___f_6263_,
    );
    return v___x_6265_;
}
pub unsafe fn l_Lake_withLogErrorPos(
    mut v_m_6266_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_6267_: *mut crate::leanh::LeanObject,
    mut v_inst_6268_: *mut crate::leanh::LeanObject,
    mut v_inst_6269_: *mut crate::leanh::LeanObject,
    mut v_inst_6270_: *mut crate::leanh::LeanObject,
    mut v_self_6271_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_6272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_6273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_6274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_6275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_get_6276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_6272_ = crate::leanh::lean_ctor_get(v_inst_6268_, 0);
    v_toFunctor_6273_ = crate::leanh::lean_ctor_get(v_toApplicative_6272_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_6273_);
    v_toBind_6274_ = crate::leanh::lean_ctor_get(v_inst_6268_, 1);
    crate::leanh::lean_inc(v_toBind_6274_);
    crate::leanh::lean_dec_ref(v_inst_6268_);
    v_map_6275_ = crate::leanh::lean_ctor_get(v_toFunctor_6273_, 0);
    crate::leanh::lean_inc(v_map_6275_);
    crate::leanh::lean_dec_ref(v_toFunctor_6273_);
    v_get_6276_ = crate::leanh::lean_ctor_get(v_inst_6269_, 0);
    crate::leanh::lean_inc(v_get_6276_);
    crate::leanh::lean_dec_ref(v_inst_6269_);
    v___f_6277_ = l_Lake_getLogPos___redArg___closed__0;
    v___f_6278_ = crate::leanh::lean_alloc_closure(
        l_Lake_withLogErrorPos___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_6278_, 0, v_inst_6270_);
    crate::leanh::lean_closure_set(v___f_6278_, 1, v_self_6271_);
    v___x_6279_ = crate::leanh::lean_apply_4(
        v_map_6275_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_6277_,
        v_get_6276_,
    );
    v___x_6280_ = crate::leanh::lean_apply_4(
        v_toBind_6274_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_6279_,
        v___f_6278_,
    );
    return v___x_6280_;
}
pub unsafe fn l_Lake_errorWithLog___redArg___lam__1(
    mut v_toPure_6281_: *mut crate::leanh::LeanObject,
    mut v_x_6282_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6283_ = crate::leanh::lean_box(0);
    v___x_6284_ =
        crate::leanh::lean_apply_2(v_toPure_6281_, crate::leanh::lean_box(0), v___x_6283_);
    return v___x_6284_;
}
pub unsafe fn l_Lake_errorWithLog___redArg___lam__1___boxed(
    mut v_toPure_6285_: *mut crate::leanh::LeanObject,
    mut v_x_6286_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6287_ = l_Lake_errorWithLog___redArg___lam__1(v_toPure_6285_, v_x_6286_);
    crate::leanh::lean_dec(v_x_6286_);
    return v_res_6287_;
}
pub unsafe fn l_Lake_errorWithLog___redArg___lam__0(
    mut v_throw_6288_: *mut crate::leanh::LeanObject,
    mut v_iniPos_6289_: *mut crate::leanh::LeanObject,
    mut v_____r_6290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6291_ =
        crate::leanh::lean_apply_2(v_throw_6288_, crate::leanh::lean_box(0), v_iniPos_6289_);
    return v___x_6291_;
}
pub unsafe fn l_Lake_errorWithLog___redArg___lam__2(
    mut v_inst_6292_: *mut crate::leanh::LeanObject,
    mut v_self_6293_: *mut crate::leanh::LeanObject,
    mut v___f_6294_: *mut crate::leanh::LeanObject,
    mut v_toBind_6295_: *mut crate::leanh::LeanObject,
    mut v_iniPos_6296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_throw_6297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tryCatch_6298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_throw_6297_ = crate::leanh::lean_ctor_get(v_inst_6292_, 0);
    crate::leanh::lean_inc(v_throw_6297_);
    v_tryCatch_6298_ = crate::leanh::lean_ctor_get(v_inst_6292_, 1);
    crate::leanh::lean_inc(v_tryCatch_6298_);
    crate::leanh::lean_dec_ref(v_inst_6292_);
    v___f_6299_ = crate::leanh::lean_alloc_closure(
        l_Lake_errorWithLog___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_6299_, 0, v_throw_6297_);
    crate::leanh::lean_closure_set(v___f_6299_, 1, v_iniPos_6296_);
    v___x_6300_ = crate::leanh::lean_apply_3(
        v_tryCatch_6298_,
        crate::leanh::lean_box(0),
        v_self_6293_,
        v___f_6294_,
    );
    v___x_6301_ = crate::leanh::lean_apply_4(
        v_toBind_6295_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_6300_,
        v___f_6299_,
    );
    return v___x_6301_;
}
pub unsafe fn l_Lake_errorWithLog___redArg(
    mut v_inst_6302_: *mut crate::leanh::LeanObject,
    mut v_inst_6303_: *mut crate::leanh::LeanObject,
    mut v_inst_6304_: *mut crate::leanh::LeanObject,
    mut v_self_6305_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_6306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_6307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_6308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_6309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_6310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_get_6311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_6306_ = crate::leanh::lean_ctor_get(v_inst_6302_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_6306_);
    v_toFunctor_6307_ = crate::leanh::lean_ctor_get(v_toApplicative_6306_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_6307_);
    v_toBind_6308_ = crate::leanh::lean_ctor_get(v_inst_6302_, 1);
    crate::leanh::lean_inc_n(v_toBind_6308_, 2);
    crate::leanh::lean_dec_ref(v_inst_6302_);
    v_toPure_6309_ = crate::leanh::lean_ctor_get(v_toApplicative_6306_, 1);
    crate::leanh::lean_inc(v_toPure_6309_);
    crate::leanh::lean_dec_ref(v_toApplicative_6306_);
    v_map_6310_ = crate::leanh::lean_ctor_get(v_toFunctor_6307_, 0);
    crate::leanh::lean_inc(v_map_6310_);
    crate::leanh::lean_dec_ref(v_toFunctor_6307_);
    v_get_6311_ = crate::leanh::lean_ctor_get(v_inst_6303_, 0);
    crate::leanh::lean_inc(v_get_6311_);
    crate::leanh::lean_dec_ref(v_inst_6303_);
    v___f_6312_ = l_Lake_getLogPos___redArg___closed__0;
    v___f_6313_ = crate::leanh::lean_alloc_closure(
        l_Lake_errorWithLog___redArg___lam__1___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_6313_, 0, v_toPure_6309_);
    v___f_6314_ = crate::leanh::lean_alloc_closure(
        l_Lake_errorWithLog___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_6314_, 0, v_inst_6304_);
    crate::leanh::lean_closure_set(v___f_6314_, 1, v_self_6305_);
    crate::leanh::lean_closure_set(v___f_6314_, 2, v___f_6313_);
    crate::leanh::lean_closure_set(v___f_6314_, 3, v_toBind_6308_);
    v___x_6315_ = crate::leanh::lean_apply_4(
        v_map_6310_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_6312_,
        v_get_6311_,
    );
    v___x_6316_ = crate::leanh::lean_apply_4(
        v_toBind_6308_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_6315_,
        v___f_6314_,
    );
    return v___x_6316_;
}
pub unsafe fn l_Lake_errorWithLog(
    mut v_m_6317_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6318_: *mut crate::leanh::LeanObject,
    mut v_inst_6319_: *mut crate::leanh::LeanObject,
    mut v_inst_6320_: *mut crate::leanh::LeanObject,
    mut v_inst_6321_: *mut crate::leanh::LeanObject,
    mut v_self_6322_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_6323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_6324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_6325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_6326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_6327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_get_6328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_6323_ = crate::leanh::lean_ctor_get(v_inst_6319_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_6323_);
    v_toFunctor_6324_ = crate::leanh::lean_ctor_get(v_toApplicative_6323_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_6324_);
    v_toBind_6325_ = crate::leanh::lean_ctor_get(v_inst_6319_, 1);
    crate::leanh::lean_inc_n(v_toBind_6325_, 2);
    crate::leanh::lean_dec_ref(v_inst_6319_);
    v_toPure_6326_ = crate::leanh::lean_ctor_get(v_toApplicative_6323_, 1);
    crate::leanh::lean_inc(v_toPure_6326_);
    crate::leanh::lean_dec_ref(v_toApplicative_6323_);
    v_map_6327_ = crate::leanh::lean_ctor_get(v_toFunctor_6324_, 0);
    crate::leanh::lean_inc(v_map_6327_);
    crate::leanh::lean_dec_ref(v_toFunctor_6324_);
    v_get_6328_ = crate::leanh::lean_ctor_get(v_inst_6320_, 0);
    crate::leanh::lean_inc(v_get_6328_);
    crate::leanh::lean_dec_ref(v_inst_6320_);
    v___f_6329_ = l_Lake_getLogPos___redArg___closed__0;
    v___f_6330_ = crate::leanh::lean_alloc_closure(
        l_Lake_errorWithLog___redArg___lam__1___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_6330_, 0, v_toPure_6326_);
    v___f_6331_ = crate::leanh::lean_alloc_closure(
        l_Lake_errorWithLog___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_6331_, 0, v_inst_6321_);
    crate::leanh::lean_closure_set(v___f_6331_, 1, v_self_6322_);
    crate::leanh::lean_closure_set(v___f_6331_, 2, v___f_6330_);
    crate::leanh::lean_closure_set(v___f_6331_, 3, v_toBind_6325_);
    v___x_6332_ = crate::leanh::lean_apply_4(
        v_map_6327_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_6329_,
        v_get_6328_,
    );
    v___x_6333_ = crate::leanh::lean_apply_4(
        v_toBind_6325_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_6332_,
        v___f_6331_,
    );
    return v___x_6333_;
}
pub unsafe fn l_Lake_withLoggedIO___redArg___lam__0(
    mut v_x_6334_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_6335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_6335_ = crate::leanh::lean_ctor_get(v_x_6334_, 0);
    crate::leanh::lean_inc(v_fst_6335_);
    return v_fst_6335_;
}
pub unsafe fn l_Lake_withLoggedIO___redArg___lam__0___boxed(
    mut v_x_6336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6337_ = l_Lake_withLoggedIO___redArg___lam__0(v_x_6336_);
    crate::leanh::lean_dec_ref(v_x_6336_);
    return v_res_6337_;
}
pub unsafe fn l_Lake_withLoggedIO___redArg___lam__1(
    mut v_buf_6338_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6340_ = lean_st_ref_get(v_buf_6338_);
    return v___x_6340_;
}
pub unsafe fn l_Lake_withLoggedIO___redArg___lam__1___boxed(
    mut v_buf_6341_: *mut crate::leanh::LeanObject,
    mut v___y_6342_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6343_ = l_Lake_withLoggedIO___redArg___lam__1(v_buf_6341_);
    crate::leanh::lean_dec(v_buf_6341_);
    return v_res_6343_;
}
pub unsafe fn l_Lake_withLoggedIO___redArg___lam__2(
    mut v_toPure_6344_: *mut crate::leanh::LeanObject,
    mut v_a_6345_: *mut crate::leanh::LeanObject,
    mut v_____r_6346_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6347_ = crate::leanh::lean_apply_2(v_toPure_6344_, crate::leanh::lean_box(0), v_a_6345_);
    return v___x_6347_;
}
pub unsafe fn _init_l_Lake_withLoggedIO___redArg___lam__3___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6352_ = l_Lake_withLoggedIO___redArg___lam__3___closed__3;
    v___x_6353_ = crate::leanh::lean_unsigned_to_nat(46);
    v___x_6354_ = crate::leanh::lean_unsigned_to_nat(193);
    v___x_6355_ = l_Lake_withLoggedIO___redArg___lam__3___closed__2;
    v___x_6356_ = l_Lake_withLoggedIO___redArg___lam__3___closed__1;
    v___x_6357_ = l_mkPanicMessageWithDecl(
        v___x_6356_,
        v___x_6355_,
        v___x_6354_,
        v___x_6353_,
        v___x_6352_,
    );
    return v___x_6357_;
}
pub unsafe fn l_Lake_withLoggedIO___redArg___lam__3(
    mut v___x_6358_: *mut crate::leanh::LeanObject,
    mut v_inst_6359_: *mut crate::leanh::LeanObject,
    mut v_toBind_6360_: *mut crate::leanh::LeanObject,
    mut v___f_6361_: *mut crate::leanh::LeanObject,
    mut v_toPure_6362_: *mut crate::leanh::LeanObject,
    mut v_a_6363_: *mut crate::leanh::LeanObject,
    mut v_buf_6364_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_6366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6368_: u8 = 0;
    let mut v___x_6369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6374_: u8 = 0;
    let mut v___x_6375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_6379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6380_: u8 = 0;
    let mut v___x_6381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_data_6379_ = crate::leanh::lean_ctor_get(v_buf_6364_, 0);
                crate::leanh::lean_inc_ref(v_data_6379_);
                crate::leanh::lean_dec_ref(v_buf_6364_);
                v___x_6380_ = lean_string_validate_utf8(v_data_6379_);
                if v___x_6380_ == 0 {
                    crate::leanh::lean_dec_ref(v_data_6379_);
                    v___x_6381_ = l_Lake_instInhabitedLogEntry_default___closed__0;
                    v___x_6382_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_withLoggedIO___redArg___lam__3___closed__4),
                        core::ptr::addr_of_mut!(
                            l_Lake_withLoggedIO___redArg___lam__3___closed__4_once
                        ),
                        _init_l_Lake_withLoggedIO___redArg___lam__3___closed__4,
                    );
                    v___x_6383_ = l_panic___redArg(v___x_6381_, v___x_6382_);
                    v___y_6366_ = v___x_6383_;
                    state = 1;
                    continue;
                } else {
                    v___x_6384_ = lean_string_from_utf8_unchecked(v_data_6379_);
                    v___y_6366_ = v___x_6384_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6367_ = lean_string_utf8_byte_size(v___y_6366_);
                v___x_6368_ = lean_nat_dec_eq(v___x_6367_, v___x_6358_);
                if v___x_6368_ == 0 {
                    crate::leanh::lean_dec(v_a_6363_);
                    crate::leanh::lean_dec(v_toPure_6362_);
                    v___x_6369_ = l_Lake_withLoggedIO___redArg___lam__3___closed__0;
                    v___x_6370_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6370_, 0, v___y_6366_);
                    crate::leanh::lean_ctor_set(v___x_6370_, 1, v___x_6358_);
                    crate::leanh::lean_ctor_set(v___x_6370_, 2, v___x_6367_);
                    v___x_6371_ = l_String_Slice_trimAscii(v___x_6370_);
                    v___x_6372_ = l_String_Slice_toString(v___x_6371_);
                    crate::leanh::lean_dec_ref(v___x_6371_);
                    v___x_6373_ = lean_string_append(v___x_6369_, v___x_6372_);
                    crate::leanh::lean_dec_ref(v___x_6372_);
                    v___x_6374_ = 1;
                    v___x_6375_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_6375_, 0, v___x_6373_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_6375_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_6374_,
                    );
                    v___x_6376_ = crate::leanh::lean_apply_1(v_inst_6359_, v___x_6375_);
                    v___x_6377_ = crate::leanh::lean_apply_4(
                        v_toBind_6360_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_6376_,
                        v___f_6361_,
                    );
                    return v___x_6377_;
                } else {
                    crate::leanh::lean_dec_ref(v___y_6366_);
                    crate::leanh::lean_dec(v___f_6361_);
                    crate::leanh::lean_dec(v_toBind_6360_);
                    crate::leanh::lean_dec(v_inst_6359_);
                    crate::leanh::lean_dec(v___x_6358_);
                    v___x_6378_ = crate::leanh::lean_apply_2(
                        v_toPure_6362_,
                        crate::leanh::lean_box(0),
                        v_a_6363_,
                    );
                    return v___x_6378_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_withLoggedIO___redArg___lam__4(
    mut v_toPure_6385_: *mut crate::leanh::LeanObject,
    mut v___x_6386_: *mut crate::leanh::LeanObject,
    mut v_inst_6387_: *mut crate::leanh::LeanObject,
    mut v_toBind_6388_: *mut crate::leanh::LeanObject,
    mut v_inst_6389_: *mut crate::leanh::LeanObject,
    mut v___f_6390_: *mut crate::leanh::LeanObject,
    mut v_a_6391_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_6392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_6391_);
    crate::leanh::lean_inc(v_toPure_6385_);
    v___f_6392_ = crate::leanh::lean_alloc_closure(
        l_Lake_withLoggedIO___redArg___lam__2 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_6392_, 0, v_toPure_6385_);
    crate::leanh::lean_closure_set(v___f_6392_, 1, v_a_6391_);
    crate::leanh::lean_inc(v_toBind_6388_);
    v___f_6393_ = crate::leanh::lean_alloc_closure(
        l_Lake_withLoggedIO___redArg___lam__3 as *mut core::ffi::c_void,
        7,
        6,
    );
    crate::leanh::lean_closure_set(v___f_6393_, 0, v___x_6386_);
    crate::leanh::lean_closure_set(v___f_6393_, 1, v_inst_6387_);
    crate::leanh::lean_closure_set(v___f_6393_, 2, v_toBind_6388_);
    crate::leanh::lean_closure_set(v___f_6393_, 3, v___f_6392_);
    crate::leanh::lean_closure_set(v___f_6393_, 4, v_toPure_6385_);
    crate::leanh::lean_closure_set(v___f_6393_, 5, v_a_6391_);
    v___x_6394_ = crate::leanh::lean_apply_2(v_inst_6389_, crate::leanh::lean_box(0), v___f_6390_);
    v___x_6395_ = crate::leanh::lean_apply_4(
        v_toBind_6388_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_6394_,
        v___f_6393_,
    );
    return v___x_6395_;
}
pub unsafe fn l_Lake_withLoggedIO___redArg___lam__5(
    mut v_stderr_6396_: *mut crate::leanh::LeanObject,
    mut v_inst_6397_: *mut crate::leanh::LeanObject,
    mut v_mapConst_6398_: *mut crate::leanh::LeanObject,
    mut v_____r_6399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6400_ =
        crate::leanh::lean_alloc_closure(l_IO_setStderr___boxed as *mut core::ffi::c_void, 2, 1);
    crate::leanh::lean_closure_set(v___x_6400_, 0, v_stderr_6396_);
    v___x_6401_ = crate::leanh::lean_apply_2(v_inst_6397_, crate::leanh::lean_box(0), v___x_6400_);
    v___x_6402_ = crate::leanh::lean_box(0);
    v___x_6403_ = crate::leanh::lean_apply_4(
        v_mapConst_6398_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_6402_,
        v___x_6401_,
    );
    return v___x_6403_;
}
pub unsafe fn l_Lake_withLoggedIO___redArg___lam__6(
    mut v___x_6404_: *mut crate::leanh::LeanObject,
    mut v_x_6405_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v___x_6404_);
    return v___x_6404_;
}
pub unsafe fn l_Lake_withLoggedIO___redArg___lam__6___boxed(
    mut v___x_6406_: *mut crate::leanh::LeanObject,
    mut v_x_6407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6408_ = l_Lake_withLoggedIO___redArg___lam__6(v___x_6406_, v_x_6407_);
    crate::leanh::lean_dec(v_x_6407_);
    crate::leanh::lean_dec(v___x_6406_);
    return v_res_6408_;
}
pub unsafe fn l_Lake_withLoggedIO___redArg___lam__7(
    mut v_toFunctor_6409_: *mut crate::leanh::LeanObject,
    mut v_inst_6410_: *mut crate::leanh::LeanObject,
    mut v_stdout_6411_: *mut crate::leanh::LeanObject,
    mut v_toBind_6412_: *mut crate::leanh::LeanObject,
    mut v_inst_6413_: *mut crate::leanh::LeanObject,
    mut v_x_6414_: *mut crate::leanh::LeanObject,
    mut v___f_6415_: *mut crate::leanh::LeanObject,
    mut v___f_6416_: *mut crate::leanh::LeanObject,
    mut v_stderr_6417_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_6418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mapConst_6419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_6427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_6418_ = crate::leanh::lean_ctor_get(v_toFunctor_6409_, 0);
    crate::leanh::lean_inc(v_map_6418_);
    v_mapConst_6419_ = crate::leanh::lean_ctor_get(v_toFunctor_6409_, 1);
    crate::leanh::lean_inc_n(v_mapConst_6419_, 2);
    crate::leanh::lean_dec_ref(v_toFunctor_6409_);
    crate::leanh::lean_inc(v_inst_6410_);
    v___f_6420_ = crate::leanh::lean_alloc_closure(
        l_Lake_withLoggedIO___redArg___lam__5 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_6420_, 0, v_stderr_6417_);
    crate::leanh::lean_closure_set(v___f_6420_, 1, v_inst_6410_);
    crate::leanh::lean_closure_set(v___f_6420_, 2, v_mapConst_6419_);
    v___x_6421_ =
        crate::leanh::lean_alloc_closure(l_IO_setStdout___boxed as *mut core::ffi::c_void, 2, 1);
    crate::leanh::lean_closure_set(v___x_6421_, 0, v_stdout_6411_);
    v___x_6422_ = crate::leanh::lean_apply_2(v_inst_6410_, crate::leanh::lean_box(0), v___x_6421_);
    v___x_6423_ = crate::leanh::lean_box(0);
    v___x_6424_ = crate::leanh::lean_apply_4(
        v_mapConst_6419_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_6423_,
        v___x_6422_,
    );
    crate::leanh::lean_inc(v_toBind_6412_);
    v___x_6425_ = crate::leanh::lean_apply_4(
        v_toBind_6412_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_6424_,
        v___f_6420_,
    );
    v___f_6426_ = crate::leanh::lean_alloc_closure(
        l_Lake_withLoggedIO___redArg___lam__6___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_6426_, 0, v___x_6425_);
    v_y_6427_ = crate::leanh::lean_apply_4(
        v_inst_6413_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_x_6414_,
        v___f_6426_,
    );
    v___x_6428_ = crate::leanh::lean_apply_4(
        v_map_6418_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_6415_,
        v_y_6427_,
    );
    v___x_6429_ = crate::leanh::lean_apply_4(
        v_toBind_6412_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_6428_,
        v___f_6416_,
    );
    return v___x_6429_;
}
pub unsafe fn l_Lake_withLoggedIO___redArg___lam__8(
    mut v_toFunctor_6430_: *mut crate::leanh::LeanObject,
    mut v_inst_6431_: *mut crate::leanh::LeanObject,
    mut v_toBind_6432_: *mut crate::leanh::LeanObject,
    mut v_inst_6433_: *mut crate::leanh::LeanObject,
    mut v_x_6434_: *mut crate::leanh::LeanObject,
    mut v___f_6435_: *mut crate::leanh::LeanObject,
    mut v___f_6436_: *mut crate::leanh::LeanObject,
    mut v___x_6437_: *mut crate::leanh::LeanObject,
    mut v_stdout_6438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_6439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_toBind_6432_);
    crate::leanh::lean_inc(v_inst_6431_);
    v___f_6439_ = crate::leanh::lean_alloc_closure(
        l_Lake_withLoggedIO___redArg___lam__7 as *mut core::ffi::c_void,
        9,
        8,
    );
    crate::leanh::lean_closure_set(v___f_6439_, 0, v_toFunctor_6430_);
    crate::leanh::lean_closure_set(v___f_6439_, 1, v_inst_6431_);
    crate::leanh::lean_closure_set(v___f_6439_, 2, v_stdout_6438_);
    crate::leanh::lean_closure_set(v___f_6439_, 3, v_toBind_6432_);
    crate::leanh::lean_closure_set(v___f_6439_, 4, v_inst_6433_);
    crate::leanh::lean_closure_set(v___f_6439_, 5, v_x_6434_);
    crate::leanh::lean_closure_set(v___f_6439_, 6, v___f_6435_);
    crate::leanh::lean_closure_set(v___f_6439_, 7, v___f_6436_);
    v___x_6440_ =
        crate::leanh::lean_alloc_closure(l_IO_setStderr___boxed as *mut core::ffi::c_void, 2, 1);
    crate::leanh::lean_closure_set(v___x_6440_, 0, v___x_6437_);
    v___x_6441_ = crate::leanh::lean_apply_2(v_inst_6431_, crate::leanh::lean_box(0), v___x_6440_);
    v___x_6442_ = crate::leanh::lean_apply_4(
        v_toBind_6432_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_6441_,
        v___f_6439_,
    );
    return v___x_6442_;
}
pub unsafe fn l_Lake_withLoggedIO___redArg___lam__9(
    mut v_toPure_6443_: *mut crate::leanh::LeanObject,
    mut v___x_6444_: *mut crate::leanh::LeanObject,
    mut v_inst_6445_: *mut crate::leanh::LeanObject,
    mut v_toBind_6446_: *mut crate::leanh::LeanObject,
    mut v_inst_6447_: *mut crate::leanh::LeanObject,
    mut v_toFunctor_6448_: *mut crate::leanh::LeanObject,
    mut v_inst_6449_: *mut crate::leanh::LeanObject,
    mut v_x_6450_: *mut crate::leanh::LeanObject,
    mut v___f_6451_: *mut crate::leanh::LeanObject,
    mut v_buf_6452_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_6453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_buf_6452_);
    v___f_6453_ = crate::leanh::lean_alloc_closure(
        l_Lake_withLoggedIO___redArg___lam__1___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_6453_, 0, v_buf_6452_);
    crate::leanh::lean_inc_n(v_inst_6447_, 2);
    crate::leanh::lean_inc_n(v_toBind_6446_, 2);
    v___f_6454_ = crate::leanh::lean_alloc_closure(
        l_Lake_withLoggedIO___redArg___lam__4 as *mut core::ffi::c_void,
        7,
        6,
    );
    crate::leanh::lean_closure_set(v___f_6454_, 0, v_toPure_6443_);
    crate::leanh::lean_closure_set(v___f_6454_, 1, v___x_6444_);
    crate::leanh::lean_closure_set(v___f_6454_, 2, v_inst_6445_);
    crate::leanh::lean_closure_set(v___f_6454_, 3, v_toBind_6446_);
    crate::leanh::lean_closure_set(v___f_6454_, 4, v_inst_6447_);
    crate::leanh::lean_closure_set(v___f_6454_, 5, v___f_6453_);
    v___x_6455_ = l_IO_FS_Stream_ofBuffer(v_buf_6452_);
    crate::leanh::lean_inc_ref(v___x_6455_);
    v___f_6456_ = crate::leanh::lean_alloc_closure(
        l_Lake_withLoggedIO___redArg___lam__8 as *mut core::ffi::c_void,
        9,
        8,
    );
    crate::leanh::lean_closure_set(v___f_6456_, 0, v_toFunctor_6448_);
    crate::leanh::lean_closure_set(v___f_6456_, 1, v_inst_6447_);
    crate::leanh::lean_closure_set(v___f_6456_, 2, v_toBind_6446_);
    crate::leanh::lean_closure_set(v___f_6456_, 3, v_inst_6449_);
    crate::leanh::lean_closure_set(v___f_6456_, 4, v_x_6450_);
    crate::leanh::lean_closure_set(v___f_6456_, 5, v___f_6451_);
    crate::leanh::lean_closure_set(v___f_6456_, 6, v___f_6454_);
    crate::leanh::lean_closure_set(v___f_6456_, 7, v___x_6455_);
    v___x_6457_ =
        crate::leanh::lean_alloc_closure(l_IO_setStdout___boxed as *mut core::ffi::c_void, 2, 1);
    crate::leanh::lean_closure_set(v___x_6457_, 0, v___x_6455_);
    v___x_6458_ = crate::leanh::lean_apply_2(v_inst_6447_, crate::leanh::lean_box(0), v___x_6457_);
    v___x_6459_ = crate::leanh::lean_apply_4(
        v_toBind_6446_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_6458_,
        v___f_6456_,
    );
    return v___x_6459_;
}
pub unsafe fn _init_l_Lake_withLoggedIO___redArg___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_6461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6461_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_6462_ = l_ByteArray_empty;
    v___x_6463_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6463_, 0, v___x_6462_);
    crate::leanh::lean_ctor_set(v___x_6463_, 1, v___x_6461_);
    return v___x_6463_;
}
pub unsafe fn _init_l_Lake_withLoggedIO___redArg___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_6464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6464_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_withLoggedIO___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lake_withLoggedIO___redArg___closed__1_once),
        _init_l_Lake_withLoggedIO___redArg___closed__1,
    );
    v___x_6465_ =
        crate::leanh::lean_alloc_closure(l_IO_mkRef___boxed as *mut core::ffi::c_void, 3, 2);
    crate::leanh::lean_closure_set(v___x_6465_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_6465_, 1, v___x_6464_);
    return v___x_6465_;
}
pub unsafe fn l_Lake_withLoggedIO___redArg(
    mut v_inst_6466_: *mut crate::leanh::LeanObject,
    mut v_inst_6467_: *mut crate::leanh::LeanObject,
    mut v_inst_6468_: *mut crate::leanh::LeanObject,
    mut v_inst_6469_: *mut crate::leanh::LeanObject,
    mut v_x_6470_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_6471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_6472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_6473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_6474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_6471_ = crate::leanh::lean_ctor_get(v_inst_6466_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_6471_);
    v_toBind_6472_ = crate::leanh::lean_ctor_get(v_inst_6466_, 1);
    crate::leanh::lean_inc_n(v_toBind_6472_, 2);
    crate::leanh::lean_dec_ref(v_inst_6466_);
    v_toFunctor_6473_ = crate::leanh::lean_ctor_get(v_toApplicative_6471_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_6473_);
    v_toPure_6474_ = crate::leanh::lean_ctor_get(v_toApplicative_6471_, 1);
    crate::leanh::lean_inc(v_toPure_6474_);
    crate::leanh::lean_dec_ref(v_toApplicative_6471_);
    v___f_6475_ = l_Lake_withLoggedIO___redArg___closed__0;
    v___x_6476_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_6477_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_withLoggedIO___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Lake_withLoggedIO___redArg___closed__2_once),
        _init_l_Lake_withLoggedIO___redArg___closed__2,
    );
    crate::leanh::lean_inc(v_inst_6467_);
    v___x_6478_ = crate::leanh::lean_apply_2(v_inst_6467_, crate::leanh::lean_box(0), v___x_6477_);
    v___f_6479_ = crate::leanh::lean_alloc_closure(
        l_Lake_withLoggedIO___redArg___lam__9 as *mut core::ffi::c_void,
        10,
        9,
    );
    crate::leanh::lean_closure_set(v___f_6479_, 0, v_toPure_6474_);
    crate::leanh::lean_closure_set(v___f_6479_, 1, v___x_6476_);
    crate::leanh::lean_closure_set(v___f_6479_, 2, v_inst_6468_);
    crate::leanh::lean_closure_set(v___f_6479_, 3, v_toBind_6472_);
    crate::leanh::lean_closure_set(v___f_6479_, 4, v_inst_6467_);
    crate::leanh::lean_closure_set(v___f_6479_, 5, v_toFunctor_6473_);
    crate::leanh::lean_closure_set(v___f_6479_, 6, v_inst_6469_);
    crate::leanh::lean_closure_set(v___f_6479_, 7, v_x_6470_);
    crate::leanh::lean_closure_set(v___f_6479_, 8, v___f_6475_);
    v___x_6480_ = crate::leanh::lean_apply_4(
        v_toBind_6472_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_6478_,
        v___f_6479_,
    );
    return v___x_6480_;
}
pub unsafe fn l_Lake_withLoggedIO(
    mut v_m_6481_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_6482_: *mut crate::leanh::LeanObject,
    mut v_inst_6483_: *mut crate::leanh::LeanObject,
    mut v_inst_6484_: *mut crate::leanh::LeanObject,
    mut v_inst_6485_: *mut crate::leanh::LeanObject,
    mut v_inst_6486_: *mut crate::leanh::LeanObject,
    mut v_x_6487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_6488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_6489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_6490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_6491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_6488_ = crate::leanh::lean_ctor_get(v_inst_6483_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_6488_);
    v_toBind_6489_ = crate::leanh::lean_ctor_get(v_inst_6483_, 1);
    crate::leanh::lean_inc_n(v_toBind_6489_, 2);
    crate::leanh::lean_dec_ref(v_inst_6483_);
    v_toFunctor_6490_ = crate::leanh::lean_ctor_get(v_toApplicative_6488_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_6490_);
    v_toPure_6491_ = crate::leanh::lean_ctor_get(v_toApplicative_6488_, 1);
    crate::leanh::lean_inc(v_toPure_6491_);
    crate::leanh::lean_dec_ref(v_toApplicative_6488_);
    v___f_6492_ = l_Lake_withLoggedIO___redArg___closed__0;
    v___x_6493_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_6494_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_withLoggedIO___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Lake_withLoggedIO___redArg___closed__2_once),
        _init_l_Lake_withLoggedIO___redArg___closed__2,
    );
    crate::leanh::lean_inc(v_inst_6484_);
    v___x_6495_ = crate::leanh::lean_apply_2(v_inst_6484_, crate::leanh::lean_box(0), v___x_6494_);
    v___f_6496_ = crate::leanh::lean_alloc_closure(
        l_Lake_withLoggedIO___redArg___lam__9 as *mut core::ffi::c_void,
        10,
        9,
    );
    crate::leanh::lean_closure_set(v___f_6496_, 0, v_toPure_6491_);
    crate::leanh::lean_closure_set(v___f_6496_, 1, v___x_6493_);
    crate::leanh::lean_closure_set(v___f_6496_, 2, v_inst_6485_);
    crate::leanh::lean_closure_set(v___f_6496_, 3, v_toBind_6489_);
    crate::leanh::lean_closure_set(v___f_6496_, 4, v_inst_6484_);
    crate::leanh::lean_closure_set(v___f_6496_, 5, v_toFunctor_6490_);
    crate::leanh::lean_closure_set(v___f_6496_, 6, v_inst_6486_);
    crate::leanh::lean_closure_set(v___f_6496_, 7, v_x_6487_);
    crate::leanh::lean_closure_set(v___f_6496_, 8, v___f_6492_);
    v___x_6497_ = crate::leanh::lean_apply_4(
        v_toBind_6489_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_6495_,
        v___f_6496_,
    );
    return v___x_6497_;
}
pub unsafe fn l_Lake_ELog_error___redArg___lam__3(
    mut v_inst_6498_: *mut crate::leanh::LeanObject,
    mut v___x_6499_: *mut crate::leanh::LeanObject,
    mut v___f_6500_: *mut crate::leanh::LeanObject,
    mut v_toBind_6501_: *mut crate::leanh::LeanObject,
    mut v_iniPos_6502_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_throw_6503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tryCatch_6504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_throw_6503_ = crate::leanh::lean_ctor_get(v_inst_6498_, 0);
    crate::leanh::lean_inc(v_throw_6503_);
    v_tryCatch_6504_ = crate::leanh::lean_ctor_get(v_inst_6498_, 1);
    crate::leanh::lean_inc(v_tryCatch_6504_);
    crate::leanh::lean_dec_ref(v_inst_6498_);
    v___f_6505_ = crate::leanh::lean_alloc_closure(
        l_Lake_errorWithLog___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_6505_, 0, v_throw_6503_);
    crate::leanh::lean_closure_set(v___f_6505_, 1, v_iniPos_6502_);
    v___x_6506_ = crate::leanh::lean_apply_3(
        v_tryCatch_6504_,
        crate::leanh::lean_box(0),
        v___x_6499_,
        v___f_6500_,
    );
    v___x_6507_ = crate::leanh::lean_apply_4(
        v_toBind_6501_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_6506_,
        v___f_6505_,
    );
    return v___x_6507_;
}
pub unsafe fn l_Lake_ELog_error___redArg(
    mut v_inst_6508_: *mut crate::leanh::LeanObject,
    mut v_inst_6509_: *mut crate::leanh::LeanObject,
    mut v_inst_6510_: *mut crate::leanh::LeanObject,
    mut v_inst_6511_: *mut crate::leanh::LeanObject,
    mut v_msg_6512_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_6513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_6514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_6515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_6516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_6517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_get_6518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6520_: u8 = 0;
    let mut v___x_6521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_6513_ = crate::leanh::lean_ctor_get(v_inst_6508_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_6513_);
    v_toFunctor_6514_ = crate::leanh::lean_ctor_get(v_toApplicative_6513_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_6514_);
    v_toBind_6515_ = crate::leanh::lean_ctor_get(v_inst_6508_, 1);
    crate::leanh::lean_inc_n(v_toBind_6515_, 2);
    crate::leanh::lean_dec_ref(v_inst_6508_);
    v_toPure_6516_ = crate::leanh::lean_ctor_get(v_toApplicative_6513_, 1);
    crate::leanh::lean_inc(v_toPure_6516_);
    crate::leanh::lean_dec_ref(v_toApplicative_6513_);
    v_map_6517_ = crate::leanh::lean_ctor_get(v_toFunctor_6514_, 0);
    crate::leanh::lean_inc(v_map_6517_);
    crate::leanh::lean_dec_ref(v_toFunctor_6514_);
    v_get_6518_ = crate::leanh::lean_ctor_get(v_inst_6510_, 0);
    crate::leanh::lean_inc(v_get_6518_);
    crate::leanh::lean_dec_ref(v_inst_6510_);
    v___f_6519_ = l_Lake_getLogPos___redArg___closed__0;
    v___x_6520_ = 3;
    v___x_6521_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_6521_, 0, v_msg_6512_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_6521_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_6520_,
    );
    v___x_6522_ = crate::leanh::lean_apply_1(v_inst_6509_, v___x_6521_);
    v___f_6523_ = crate::leanh::lean_alloc_closure(
        l_Lake_errorWithLog___redArg___lam__1___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_6523_, 0, v_toPure_6516_);
    v___f_6524_ = crate::leanh::lean_alloc_closure(
        l_Lake_ELog_error___redArg___lam__3 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_6524_, 0, v_inst_6511_);
    crate::leanh::lean_closure_set(v___f_6524_, 1, v___x_6522_);
    crate::leanh::lean_closure_set(v___f_6524_, 2, v___f_6523_);
    crate::leanh::lean_closure_set(v___f_6524_, 3, v_toBind_6515_);
    v___x_6525_ = crate::leanh::lean_apply_4(
        v_map_6517_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_6519_,
        v_get_6518_,
    );
    v___x_6526_ = crate::leanh::lean_apply_4(
        v_toBind_6515_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_6525_,
        v___f_6524_,
    );
    return v___x_6526_;
}
pub unsafe fn l_Lake_ELog_error(
    mut v_m_6527_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_6528_: *mut crate::leanh::LeanObject,
    mut v_inst_6529_: *mut crate::leanh::LeanObject,
    mut v_inst_6530_: *mut crate::leanh::LeanObject,
    mut v_inst_6531_: *mut crate::leanh::LeanObject,
    mut v_inst_6532_: *mut crate::leanh::LeanObject,
    mut v_msg_6533_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_6534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_6535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_6536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_6537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_6538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_get_6539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6541_: u8 = 0;
    let mut v___x_6542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_6534_ = crate::leanh::lean_ctor_get(v_inst_6529_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_6534_);
    v_toFunctor_6535_ = crate::leanh::lean_ctor_get(v_toApplicative_6534_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_6535_);
    v_toBind_6536_ = crate::leanh::lean_ctor_get(v_inst_6529_, 1);
    crate::leanh::lean_inc_n(v_toBind_6536_, 2);
    crate::leanh::lean_dec_ref(v_inst_6529_);
    v_toPure_6537_ = crate::leanh::lean_ctor_get(v_toApplicative_6534_, 1);
    crate::leanh::lean_inc(v_toPure_6537_);
    crate::leanh::lean_dec_ref(v_toApplicative_6534_);
    v_map_6538_ = crate::leanh::lean_ctor_get(v_toFunctor_6535_, 0);
    crate::leanh::lean_inc(v_map_6538_);
    crate::leanh::lean_dec_ref(v_toFunctor_6535_);
    v_get_6539_ = crate::leanh::lean_ctor_get(v_inst_6531_, 0);
    crate::leanh::lean_inc(v_get_6539_);
    crate::leanh::lean_dec_ref(v_inst_6531_);
    v___f_6540_ = l_Lake_getLogPos___redArg___closed__0;
    v___x_6541_ = 3;
    v___x_6542_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_6542_, 0, v_msg_6533_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_6542_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_6541_,
    );
    v___x_6543_ = crate::leanh::lean_apply_1(v_inst_6530_, v___x_6542_);
    v___f_6544_ = crate::leanh::lean_alloc_closure(
        l_Lake_errorWithLog___redArg___lam__1___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_6544_, 0, v_toPure_6537_);
    v___f_6545_ = crate::leanh::lean_alloc_closure(
        l_Lake_ELog_error___redArg___lam__3 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_6545_, 0, v_inst_6532_);
    crate::leanh::lean_closure_set(v___f_6545_, 1, v___x_6543_);
    crate::leanh::lean_closure_set(v___f_6545_, 2, v___f_6544_);
    crate::leanh::lean_closure_set(v___f_6545_, 3, v_toBind_6536_);
    v___x_6546_ = crate::leanh::lean_apply_4(
        v_map_6538_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_6540_,
        v_get_6539_,
    );
    v___x_6547_ = crate::leanh::lean_apply_4(
        v_toBind_6536_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_6546_,
        v___f_6545_,
    );
    return v___x_6547_;
}
pub unsafe fn l_Lake_ELog_monadError___redArg___lam__4(
    mut v_inst_6548_: *mut crate::leanh::LeanObject,
    mut v_inst_6549_: *mut crate::leanh::LeanObject,
    mut v_inst_6550_: *mut crate::leanh::LeanObject,
    mut v_inst_6551_: *mut crate::leanh::LeanObject,
    mut v___f_6552_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_6553_: *mut crate::leanh::LeanObject,
    mut v___y_6554_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_6555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_6556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_6557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_6558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_6559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_get_6560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6561_: u8 = 0;
    let mut v___x_6562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_6555_ = crate::leanh::lean_ctor_get(v_inst_6548_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_6555_);
    v_toFunctor_6556_ = crate::leanh::lean_ctor_get(v_toApplicative_6555_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_6556_);
    v_toBind_6557_ = crate::leanh::lean_ctor_get(v_inst_6548_, 1);
    crate::leanh::lean_inc_n(v_toBind_6557_, 2);
    crate::leanh::lean_dec_ref(v_inst_6548_);
    v_toPure_6558_ = crate::leanh::lean_ctor_get(v_toApplicative_6555_, 1);
    crate::leanh::lean_inc(v_toPure_6558_);
    crate::leanh::lean_dec_ref(v_toApplicative_6555_);
    v_map_6559_ = crate::leanh::lean_ctor_get(v_toFunctor_6556_, 0);
    crate::leanh::lean_inc(v_map_6559_);
    crate::leanh::lean_dec_ref(v_toFunctor_6556_);
    v_get_6560_ = crate::leanh::lean_ctor_get(v_inst_6549_, 0);
    crate::leanh::lean_inc(v_get_6560_);
    crate::leanh::lean_dec_ref(v_inst_6549_);
    v___x_6561_ = 3;
    v___x_6562_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_6562_, 0, v___y_6554_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_6562_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_6561_,
    );
    v___x_6563_ = crate::leanh::lean_apply_1(v_inst_6550_, v___x_6562_);
    v___f_6564_ = crate::leanh::lean_alloc_closure(
        l_Lake_errorWithLog___redArg___lam__1___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_6564_, 0, v_toPure_6558_);
    v___f_6565_ = crate::leanh::lean_alloc_closure(
        l_Lake_ELog_error___redArg___lam__3 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_6565_, 0, v_inst_6551_);
    crate::leanh::lean_closure_set(v___f_6565_, 1, v___x_6563_);
    crate::leanh::lean_closure_set(v___f_6565_, 2, v___f_6564_);
    crate::leanh::lean_closure_set(v___f_6565_, 3, v_toBind_6557_);
    v___x_6566_ = crate::leanh::lean_apply_4(
        v_map_6559_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_6552_,
        v_get_6560_,
    );
    v___x_6567_ = crate::leanh::lean_apply_4(
        v_toBind_6557_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_6566_,
        v___f_6565_,
    );
    return v___x_6567_;
}
pub unsafe fn l_Lake_ELog_monadError___redArg(
    mut v_inst_6568_: *mut crate::leanh::LeanObject,
    mut v_inst_6569_: *mut crate::leanh::LeanObject,
    mut v_inst_6570_: *mut crate::leanh::LeanObject,
    mut v_inst_6571_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_6572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_6572_ = l_Lake_getLogPos___redArg___closed__0;
    v___f_6573_ = crate::leanh::lean_alloc_closure(
        l_Lake_ELog_monadError___redArg___lam__4 as *mut core::ffi::c_void,
        7,
        5,
    );
    crate::leanh::lean_closure_set(v___f_6573_, 0, v_inst_6568_);
    crate::leanh::lean_closure_set(v___f_6573_, 1, v_inst_6570_);
    crate::leanh::lean_closure_set(v___f_6573_, 2, v_inst_6569_);
    crate::leanh::lean_closure_set(v___f_6573_, 3, v_inst_6571_);
    crate::leanh::lean_closure_set(v___f_6573_, 4, v___f_6572_);
    return v___f_6573_;
}
pub unsafe fn l_Lake_ELog_monadError(
    mut v_m_6574_: *mut crate::leanh::LeanObject,
    mut v_inst_6575_: *mut crate::leanh::LeanObject,
    mut v_inst_6576_: *mut crate::leanh::LeanObject,
    mut v_inst_6577_: *mut crate::leanh::LeanObject,
    mut v_inst_6578_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_6579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_6579_ = l_Lake_getLogPos___redArg___closed__0;
    v___f_6580_ = crate::leanh::lean_alloc_closure(
        l_Lake_ELog_monadError___redArg___lam__4 as *mut core::ffi::c_void,
        7,
        5,
    );
    crate::leanh::lean_closure_set(v___f_6580_, 0, v_inst_6575_);
    crate::leanh::lean_closure_set(v___f_6580_, 1, v_inst_6577_);
    crate::leanh::lean_closure_set(v___f_6580_, 2, v_inst_6576_);
    crate::leanh::lean_closure_set(v___f_6580_, 3, v_inst_6578_);
    crate::leanh::lean_closure_set(v___f_6580_, 4, v___f_6579_);
    return v___f_6580_;
}
pub unsafe fn l_Lake_ELog_failure___redArg___lam__1(
    mut v_inst_6581_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_6582_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_throw_6583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_throw_6583_ = crate::leanh::lean_ctor_get(v_inst_6581_, 0);
    crate::leanh::lean_inc(v_throw_6583_);
    crate::leanh::lean_dec_ref(v_inst_6581_);
    v___x_6584_ = crate::leanh::lean_apply_2(
        v_throw_6583_,
        crate::leanh::lean_box(0),
        v_____do__lift_6582_,
    );
    return v___x_6584_;
}
pub unsafe fn l_Lake_ELog_failure___redArg(
    mut v_inst_6585_: *mut crate::leanh::LeanObject,
    mut v_inst_6586_: *mut crate::leanh::LeanObject,
    mut v_inst_6587_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_6588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_6589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_6590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_6591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_get_6592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_6588_ = crate::leanh::lean_ctor_get(v_inst_6585_, 0);
    v_toFunctor_6589_ = crate::leanh::lean_ctor_get(v_toApplicative_6588_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_6589_);
    v_toBind_6590_ = crate::leanh::lean_ctor_get(v_inst_6585_, 1);
    crate::leanh::lean_inc(v_toBind_6590_);
    crate::leanh::lean_dec_ref(v_inst_6585_);
    v_map_6591_ = crate::leanh::lean_ctor_get(v_toFunctor_6589_, 0);
    crate::leanh::lean_inc(v_map_6591_);
    crate::leanh::lean_dec_ref(v_toFunctor_6589_);
    v_get_6592_ = crate::leanh::lean_ctor_get(v_inst_6586_, 0);
    crate::leanh::lean_inc(v_get_6592_);
    crate::leanh::lean_dec_ref(v_inst_6586_);
    v___f_6593_ = l_Lake_getLogPos___redArg___closed__0;
    v___f_6594_ = crate::leanh::lean_alloc_closure(
        l_Lake_ELog_failure___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_6594_, 0, v_inst_6587_);
    v___x_6595_ = crate::leanh::lean_apply_4(
        v_map_6591_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_6593_,
        v_get_6592_,
    );
    v___x_6596_ = crate::leanh::lean_apply_4(
        v_toBind_6590_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_6595_,
        v___f_6594_,
    );
    return v___x_6596_;
}
pub unsafe fn l_Lake_ELog_failure(
    mut v_m_6597_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_6598_: *mut crate::leanh::LeanObject,
    mut v_inst_6599_: *mut crate::leanh::LeanObject,
    mut v_inst_6600_: *mut crate::leanh::LeanObject,
    mut v_inst_6601_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_6602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_6603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_6604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_6605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_get_6606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_6602_ = crate::leanh::lean_ctor_get(v_inst_6599_, 0);
    v_toFunctor_6603_ = crate::leanh::lean_ctor_get(v_toApplicative_6602_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_6603_);
    v_toBind_6604_ = crate::leanh::lean_ctor_get(v_inst_6599_, 1);
    crate::leanh::lean_inc(v_toBind_6604_);
    crate::leanh::lean_dec_ref(v_inst_6599_);
    v_map_6605_ = crate::leanh::lean_ctor_get(v_toFunctor_6603_, 0);
    crate::leanh::lean_inc(v_map_6605_);
    crate::leanh::lean_dec_ref(v_toFunctor_6603_);
    v_get_6606_ = crate::leanh::lean_ctor_get(v_inst_6600_, 0);
    crate::leanh::lean_inc(v_get_6606_);
    crate::leanh::lean_dec_ref(v_inst_6600_);
    v___f_6607_ = l_Lake_getLogPos___redArg___closed__0;
    v___f_6608_ = crate::leanh::lean_alloc_closure(
        l_Lake_ELog_failure___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_6608_, 0, v_inst_6601_);
    v___x_6609_ = crate::leanh::lean_apply_4(
        v_map_6605_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_6607_,
        v_get_6606_,
    );
    v___x_6610_ = crate::leanh::lean_apply_4(
        v_toBind_6604_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_6609_,
        v___f_6608_,
    );
    return v___x_6610_;
}
pub unsafe fn l_Lake_ELog_orElse___redArg___lam__0(
    mut v_y_6611_: *mut crate::leanh::LeanObject,
    mut v_____r_6612_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6613_ = crate::leanh::lean_box(0);
    v___x_6614_ = crate::leanh::lean_apply_1(v_y_6611_, v___x_6613_);
    return v___x_6614_;
}
pub unsafe fn l_Lake_ELog_orElse___redArg___lam__1(
    mut v_errPos_6615_: *mut crate::leanh::LeanObject,
    mut v_s_6616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6617_ = crate::leanh::lean_box(0);
    v___x_6618_ = l_Array_shrink___redArg(v_s_6616_, v_errPos_6615_);
    v___x_6619_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6619_, 0, v___x_6617_);
    crate::leanh::lean_ctor_set(v___x_6619_, 1, v___x_6618_);
    return v___x_6619_;
}
pub unsafe fn l_Lake_ELog_orElse___redArg___lam__1___boxed(
    mut v_errPos_6620_: *mut crate::leanh::LeanObject,
    mut v_s_6621_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6622_ = l_Lake_ELog_orElse___redArg___lam__1(v_errPos_6620_, v_s_6621_);
    crate::leanh::lean_dec(v_errPos_6620_);
    return v_res_6622_;
}
pub unsafe fn l_Lake_ELog_orElse___redArg___lam__2(
    mut v_inst_6623_: *mut crate::leanh::LeanObject,
    mut v_toBind_6624_: *mut crate::leanh::LeanObject,
    mut v___f_6625_: *mut crate::leanh::LeanObject,
    mut v_errPos_6626_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_modifyGet_6627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_modifyGet_6627_ = crate::leanh::lean_ctor_get(v_inst_6623_, 2);
    crate::leanh::lean_inc(v_modifyGet_6627_);
    crate::leanh::lean_dec_ref(v_inst_6623_);
    v___f_6628_ = crate::leanh::lean_alloc_closure(
        l_Lake_ELog_orElse___redArg___lam__1___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_6628_, 0, v_errPos_6626_);
    v___x_6629_ =
        crate::leanh::lean_apply_2(v_modifyGet_6627_, crate::leanh::lean_box(0), v___f_6628_);
    v___x_6630_ = crate::leanh::lean_apply_4(
        v_toBind_6624_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_6629_,
        v___f_6625_,
    );
    return v___x_6630_;
}
pub unsafe fn l_Lake_ELog_orElse___redArg(
    mut v_inst_6631_: *mut crate::leanh::LeanObject,
    mut v_inst_6632_: *mut crate::leanh::LeanObject,
    mut v_inst_6633_: *mut crate::leanh::LeanObject,
    mut v_x_6634_: *mut crate::leanh::LeanObject,
    mut v_y_6635_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_6636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tryCatch_6637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_6636_ = crate::leanh::lean_ctor_get(v_inst_6631_, 1);
    crate::leanh::lean_inc(v_toBind_6636_);
    crate::leanh::lean_dec_ref(v_inst_6631_);
    v_tryCatch_6637_ = crate::leanh::lean_ctor_get(v_inst_6633_, 1);
    crate::leanh::lean_inc(v_tryCatch_6637_);
    crate::leanh::lean_dec_ref(v_inst_6633_);
    v___f_6638_ = crate::leanh::lean_alloc_closure(
        l_Lake_ELog_orElse___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_6638_, 0, v_y_6635_);
    v___f_6639_ = crate::leanh::lean_alloc_closure(
        l_Lake_ELog_orElse___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_6639_, 0, v_inst_6632_);
    crate::leanh::lean_closure_set(v___f_6639_, 1, v_toBind_6636_);
    crate::leanh::lean_closure_set(v___f_6639_, 2, v___f_6638_);
    v___x_6640_ = crate::leanh::lean_apply_3(
        v_tryCatch_6637_,
        crate::leanh::lean_box(0),
        v_x_6634_,
        v___f_6639_,
    );
    return v___x_6640_;
}
pub unsafe fn l_Lake_ELog_orElse(
    mut v_m_6641_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_6642_: *mut crate::leanh::LeanObject,
    mut v_inst_6643_: *mut crate::leanh::LeanObject,
    mut v_inst_6644_: *mut crate::leanh::LeanObject,
    mut v_inst_6645_: *mut crate::leanh::LeanObject,
    mut v_x_6646_: *mut crate::leanh::LeanObject,
    mut v_y_6647_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_6648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tryCatch_6649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_6648_ = crate::leanh::lean_ctor_get(v_inst_6643_, 1);
    crate::leanh::lean_inc(v_toBind_6648_);
    crate::leanh::lean_dec_ref(v_inst_6643_);
    v_tryCatch_6649_ = crate::leanh::lean_ctor_get(v_inst_6645_, 1);
    crate::leanh::lean_inc(v_tryCatch_6649_);
    crate::leanh::lean_dec_ref(v_inst_6645_);
    v___f_6650_ = crate::leanh::lean_alloc_closure(
        l_Lake_ELog_orElse___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_6650_, 0, v_y_6647_);
    v___f_6651_ = crate::leanh::lean_alloc_closure(
        l_Lake_ELog_orElse___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_6651_, 0, v_inst_6644_);
    crate::leanh::lean_closure_set(v___f_6651_, 1, v_toBind_6648_);
    crate::leanh::lean_closure_set(v___f_6651_, 2, v___f_6650_);
    v___x_6652_ = crate::leanh::lean_apply_3(
        v_tryCatch_6649_,
        crate::leanh::lean_box(0),
        v_x_6646_,
        v___f_6651_,
    );
    return v___x_6652_;
}
pub unsafe fn l_Lake_ELog_alternative___redArg___lam__2(
    mut v_toApplicative_6653_: *mut crate::leanh::LeanObject,
    mut v_inst_6654_: *mut crate::leanh::LeanObject,
    mut v___f_6655_: *mut crate::leanh::LeanObject,
    mut v_toBind_6656_: *mut crate::leanh::LeanObject,
    mut v___f_6657_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_6658_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toFunctor_6659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_6660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_get_6661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toFunctor_6659_ = crate::leanh::lean_ctor_get(v_toApplicative_6653_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_6659_);
    crate::leanh::lean_dec_ref(v_toApplicative_6653_);
    v_map_6660_ = crate::leanh::lean_ctor_get(v_toFunctor_6659_, 0);
    crate::leanh::lean_inc(v_map_6660_);
    crate::leanh::lean_dec_ref(v_toFunctor_6659_);
    v_get_6661_ = crate::leanh::lean_ctor_get(v_inst_6654_, 0);
    crate::leanh::lean_inc(v_get_6661_);
    crate::leanh::lean_dec_ref(v_inst_6654_);
    v___x_6662_ = crate::leanh::lean_apply_4(
        v_map_6660_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_6655_,
        v_get_6661_,
    );
    v___x_6663_ = crate::leanh::lean_apply_4(
        v_toBind_6656_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_6662_,
        v___f_6657_,
    );
    return v___x_6663_;
}
pub unsafe fn l_Lake_ELog_alternative___redArg___lam__0(
    mut v___y_6664_: *mut crate::leanh::LeanObject,
    mut v_____r_6665_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6666_ = crate::leanh::lean_box(0);
    v___x_6667_ = crate::leanh::lean_apply_1(v___y_6664_, v___x_6666_);
    return v___x_6667_;
}
pub unsafe fn l_Lake_ELog_alternative___redArg___lam__4(
    mut v_inst_6668_: *mut crate::leanh::LeanObject,
    mut v_inst_6669_: *mut crate::leanh::LeanObject,
    mut v_toBind_6670_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_6671_: *mut crate::leanh::LeanObject,
    mut v___y_6672_: *mut crate::leanh::LeanObject,
    mut v___y_6673_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_tryCatch_6674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_tryCatch_6674_ = crate::leanh::lean_ctor_get(v_inst_6668_, 1);
    crate::leanh::lean_inc(v_tryCatch_6674_);
    crate::leanh::lean_dec_ref(v_inst_6668_);
    v___f_6675_ = crate::leanh::lean_alloc_closure(
        l_Lake_ELog_alternative___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_6675_, 0, v___y_6673_);
    v___f_6676_ = crate::leanh::lean_alloc_closure(
        l_Lake_ELog_orElse___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_6676_, 0, v_inst_6669_);
    crate::leanh::lean_closure_set(v___f_6676_, 1, v_toBind_6670_);
    crate::leanh::lean_closure_set(v___f_6676_, 2, v___f_6675_);
    v___x_6677_ = crate::leanh::lean_apply_3(
        v_tryCatch_6674_,
        crate::leanh::lean_box(0),
        v___y_6672_,
        v___f_6676_,
    );
    return v___x_6677_;
}
pub unsafe fn l_Lake_ELog_alternative___redArg(
    mut v_inst_6678_: *mut crate::leanh::LeanObject,
    mut v_inst_6679_: *mut crate::leanh::LeanObject,
    mut v_inst_6680_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_6681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_6682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_6681_ = crate::leanh::lean_ctor_get(v_inst_6678_, 0);
    crate::leanh::lean_inc_ref_n(v_toApplicative_6681_, 2);
    v_toBind_6682_ = crate::leanh::lean_ctor_get(v_inst_6678_, 1);
    crate::leanh::lean_inc_n(v_toBind_6682_, 2);
    crate::leanh::lean_dec_ref(v_inst_6678_);
    v___f_6683_ = l_Lake_getLogPos___redArg___closed__0;
    crate::leanh::lean_inc_ref(v_inst_6680_);
    v___f_6684_ = crate::leanh::lean_alloc_closure(
        l_Lake_ELog_failure___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_6684_, 0, v_inst_6680_);
    crate::leanh::lean_inc_ref(v_inst_6679_);
    v___f_6685_ = crate::leanh::lean_alloc_closure(
        l_Lake_ELog_alternative___redArg___lam__2 as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_6685_, 0, v_toApplicative_6681_);
    crate::leanh::lean_closure_set(v___f_6685_, 1, v_inst_6679_);
    crate::leanh::lean_closure_set(v___f_6685_, 2, v___f_6683_);
    crate::leanh::lean_closure_set(v___f_6685_, 3, v_toBind_6682_);
    crate::leanh::lean_closure_set(v___f_6685_, 4, v___f_6684_);
    v___f_6686_ = crate::leanh::lean_alloc_closure(
        l_Lake_ELog_alternative___redArg___lam__4 as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_6686_, 0, v_inst_6680_);
    crate::leanh::lean_closure_set(v___f_6686_, 1, v_inst_6679_);
    crate::leanh::lean_closure_set(v___f_6686_, 2, v_toBind_6682_);
    v___x_6687_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6687_, 0, v_toApplicative_6681_);
    crate::leanh::lean_ctor_set(v___x_6687_, 1, v___f_6685_);
    crate::leanh::lean_ctor_set(v___x_6687_, 2, v___f_6686_);
    return v___x_6687_;
}
pub unsafe fn l_Lake_ELog_alternative(
    mut v_m_6688_: *mut crate::leanh::LeanObject,
    mut v_inst_6689_: *mut crate::leanh::LeanObject,
    mut v_inst_6690_: *mut crate::leanh::LeanObject,
    mut v_inst_6691_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_6692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_6693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_6692_ = crate::leanh::lean_ctor_get(v_inst_6689_, 0);
    crate::leanh::lean_inc_ref_n(v_toApplicative_6692_, 2);
    v_toBind_6693_ = crate::leanh::lean_ctor_get(v_inst_6689_, 1);
    crate::leanh::lean_inc_n(v_toBind_6693_, 2);
    crate::leanh::lean_dec_ref(v_inst_6689_);
    v___f_6694_ = l_Lake_getLogPos___redArg___closed__0;
    crate::leanh::lean_inc_ref(v_inst_6691_);
    v___f_6695_ = crate::leanh::lean_alloc_closure(
        l_Lake_ELog_failure___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_6695_, 0, v_inst_6691_);
    crate::leanh::lean_inc_ref(v_inst_6690_);
    v___f_6696_ = crate::leanh::lean_alloc_closure(
        l_Lake_ELog_alternative___redArg___lam__2 as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_6696_, 0, v_toApplicative_6692_);
    crate::leanh::lean_closure_set(v___f_6696_, 1, v_inst_6690_);
    crate::leanh::lean_closure_set(v___f_6696_, 2, v___f_6694_);
    crate::leanh::lean_closure_set(v___f_6696_, 3, v_toBind_6693_);
    crate::leanh::lean_closure_set(v___f_6696_, 4, v___f_6695_);
    v___f_6697_ = crate::leanh::lean_alloc_closure(
        l_Lake_ELog_alternative___redArg___lam__4 as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_6697_, 0, v_inst_6691_);
    crate::leanh::lean_closure_set(v___f_6697_, 1, v_inst_6690_);
    crate::leanh::lean_closure_set(v___f_6697_, 2, v_toBind_6693_);
    v___x_6698_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6698_, 0, v_toApplicative_6692_);
    crate::leanh::lean_ctor_set(v___x_6698_, 1, v___f_6696_);
    crate::leanh::lean_ctor_set(v___x_6698_, 2, v___f_6697_);
    return v___x_6698_;
}
pub unsafe fn l_Lake_instMonadLogLogTOfMonad___redArg(
    mut v_inst_6699_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6700_ = l_instMonadStateOfStateTOfMonad___redArg(v_inst_6699_);
    v___x_6701_ =
        crate::leanh::lean_alloc_closure(l_Lake_pushLogEntry as *mut core::ffi::c_void, 3, 2);
    crate::leanh::lean_closure_set(v___x_6701_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_6701_, 1, v___x_6700_);
    return v___x_6701_;
}
pub unsafe fn l_Lake_instMonadLogLogTOfMonad(
    mut v_m_6702_: *mut crate::leanh::LeanObject,
    mut v_inst_6703_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6704_ = l_Lake_instMonadLogLogTOfMonad___redArg(v_inst_6703_);
    return v___x_6704_;
}
pub unsafe fn l_Lake_LogT_run___redArg(
    mut v_self_6705_: *mut crate::leanh::LeanObject,
    mut v_log_6706_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6707_ = crate::leanh::lean_apply_1(v_self_6705_, v_log_6706_);
    return v___x_6707_;
}
pub unsafe fn l_Lake_LogT_run(
    mut v_m_6708_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_6709_: *mut crate::leanh::LeanObject,
    mut v_self_6710_: *mut crate::leanh::LeanObject,
    mut v_log_6711_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6712_ = crate::leanh::lean_apply_1(v_self_6710_, v_log_6711_);
    return v___x_6712_;
}
pub unsafe fn l_Lake_LogT_run_x27___redArg___lam__0(
    mut v_x_6713_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_6714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_6714_ = crate::leanh::lean_ctor_get(v_x_6713_, 0);
    crate::leanh::lean_inc(v_fst_6714_);
    return v_fst_6714_;
}
pub unsafe fn l_Lake_LogT_run_x27___redArg___lam__0___boxed(
    mut v_x_6715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6716_ = l_Lake_LogT_run_x27___redArg___lam__0(v_x_6715_);
    crate::leanh::lean_dec_ref(v_x_6715_);
    return v_res_6716_;
}
pub unsafe fn l_Lake_LogT_run_x27___redArg(
    mut v_inst_6718_: *mut crate::leanh::LeanObject,
    mut v_self_6719_: *mut crate::leanh::LeanObject,
    mut v_log_6720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_6721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_6721_ = crate::leanh::lean_ctor_get(v_inst_6718_, 0);
    crate::leanh::lean_inc(v_map_6721_);
    crate::leanh::lean_dec_ref(v_inst_6718_);
    v___f_6722_ = l_Lake_LogT_run_x27___redArg___closed__0;
    v___x_6723_ = crate::leanh::lean_apply_1(v_self_6719_, v_log_6720_);
    v___x_6724_ = crate::leanh::lean_apply_4(
        v_map_6721_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_6722_,
        v___x_6723_,
    );
    return v___x_6724_;
}
pub unsafe fn l_Lake_LogT_run_x27(
    mut v_m_6725_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_6726_: *mut crate::leanh::LeanObject,
    mut v_inst_6727_: *mut crate::leanh::LeanObject,
    mut v_self_6728_: *mut crate::leanh::LeanObject,
    mut v_log_6729_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_6730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_6730_ = crate::leanh::lean_ctor_get(v_inst_6727_, 0);
    crate::leanh::lean_inc(v_map_6730_);
    crate::leanh::lean_dec_ref(v_inst_6727_);
    v___f_6731_ = l_Lake_LogT_run_x27___redArg___closed__0;
    v___x_6732_ = crate::leanh::lean_apply_1(v_self_6728_, v_log_6729_);
    v___x_6733_ = crate::leanh::lean_apply_4(
        v_map_6730_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_6731_,
        v___x_6732_,
    );
    return v___x_6733_;
}
pub unsafe fn l_Lake_LogT_takeAndRun___redArg___lam__1(
    mut v_toPure_6734_: *mut crate::leanh::LeanObject,
    mut v_fst_6735_: *mut crate::leanh::LeanObject,
    mut v_____r_6736_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6737_ =
        crate::leanh::lean_apply_2(v_toPure_6734_, crate::leanh::lean_box(0), v_fst_6735_);
    return v___x_6737_;
}
pub unsafe fn l_Lake_LogT_takeAndRun___redArg___lam__0(
    mut v_toPure_6738_: *mut crate::leanh::LeanObject,
    mut v_set_6739_: *mut crate::leanh::LeanObject,
    mut v_toBind_6740_: *mut crate::leanh::LeanObject,
    mut v_____x_6741_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_6742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_6742_ = crate::leanh::lean_ctor_get(v_____x_6741_, 0);
    crate::leanh::lean_inc(v_fst_6742_);
    v_snd_6743_ = crate::leanh::lean_ctor_get(v_____x_6741_, 1);
    crate::leanh::lean_inc(v_snd_6743_);
    crate::leanh::lean_dec_ref(v_____x_6741_);
    v___f_6744_ = crate::leanh::lean_alloc_closure(
        l_Lake_LogT_takeAndRun___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_6744_, 0, v_toPure_6738_);
    crate::leanh::lean_closure_set(v___f_6744_, 1, v_fst_6742_);
    v___x_6745_ = crate::leanh::lean_apply_1(v_set_6739_, v_snd_6743_);
    v___x_6746_ = crate::leanh::lean_apply_4(
        v_toBind_6740_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_6745_,
        v___f_6744_,
    );
    return v___x_6746_;
}
pub unsafe fn l_Lake_LogT_takeAndRun___redArg___lam__2(
    mut v_self_6747_: *mut crate::leanh::LeanObject,
    mut v_inst_6748_: *mut crate::leanh::LeanObject,
    mut v_toBind_6749_: *mut crate::leanh::LeanObject,
    mut v___f_6750_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_6751_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6752_ = crate::leanh::lean_apply_1(v_self_6747_, v_____do__lift_6751_);
    v___x_6753_ = crate::leanh::lean_apply_2(v_inst_6748_, crate::leanh::lean_box(0), v___x_6752_);
    v___x_6754_ = crate::leanh::lean_apply_4(
        v_toBind_6749_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_6753_,
        v___f_6750_,
    );
    return v___x_6754_;
}
pub unsafe fn l_Lake_LogT_takeAndRun___redArg(
    mut v_inst_6755_: *mut crate::leanh::LeanObject,
    mut v_inst_6756_: *mut crate::leanh::LeanObject,
    mut v_inst_6757_: *mut crate::leanh::LeanObject,
    mut v_self_6758_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_6759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_6760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_set_6761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_6762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_6763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_6759_ = crate::leanh::lean_ctor_get(v_inst_6755_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_6759_);
    v_toBind_6760_ = crate::leanh::lean_ctor_get(v_inst_6755_, 1);
    crate::leanh::lean_inc_n(v_toBind_6760_, 3);
    crate::leanh::lean_dec_ref(v_inst_6755_);
    v_set_6761_ = crate::leanh::lean_ctor_get(v_inst_6756_, 1);
    crate::leanh::lean_inc(v_set_6761_);
    v_modifyGet_6762_ = crate::leanh::lean_ctor_get(v_inst_6756_, 2);
    crate::leanh::lean_inc(v_modifyGet_6762_);
    crate::leanh::lean_dec_ref(v_inst_6756_);
    v_toPure_6763_ = crate::leanh::lean_ctor_get(v_toApplicative_6759_, 1);
    crate::leanh::lean_inc(v_toPure_6763_);
    crate::leanh::lean_dec_ref(v_toApplicative_6759_);
    v___f_6764_ = l_Lake_takeLog___redArg___closed__0;
    v___x_6765_ =
        crate::leanh::lean_apply_2(v_modifyGet_6762_, crate::leanh::lean_box(0), v___f_6764_);
    v___f_6766_ = crate::leanh::lean_alloc_closure(
        l_Lake_LogT_takeAndRun___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_6766_, 0, v_toPure_6763_);
    crate::leanh::lean_closure_set(v___f_6766_, 1, v_set_6761_);
    crate::leanh::lean_closure_set(v___f_6766_, 2, v_toBind_6760_);
    v___f_6767_ = crate::leanh::lean_alloc_closure(
        l_Lake_LogT_takeAndRun___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_6767_, 0, v_self_6758_);
    crate::leanh::lean_closure_set(v___f_6767_, 1, v_inst_6757_);
    crate::leanh::lean_closure_set(v___f_6767_, 2, v_toBind_6760_);
    crate::leanh::lean_closure_set(v___f_6767_, 3, v___f_6766_);
    v___x_6768_ = crate::leanh::lean_apply_4(
        v_toBind_6760_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_6765_,
        v___f_6767_,
    );
    return v___x_6768_;
}
pub unsafe fn l_Lake_LogT_takeAndRun(
    mut v_n_6769_: *mut crate::leanh::LeanObject,
    mut v_m_6770_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_6771_: *mut crate::leanh::LeanObject,
    mut v_inst_6772_: *mut crate::leanh::LeanObject,
    mut v_inst_6773_: *mut crate::leanh::LeanObject,
    mut v_inst_6774_: *mut crate::leanh::LeanObject,
    mut v_inst_6775_: *mut crate::leanh::LeanObject,
    mut v_self_6776_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_6777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_6778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_set_6779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_6780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_6781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_6777_ = crate::leanh::lean_ctor_get(v_inst_6772_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_6777_);
    v_toBind_6778_ = crate::leanh::lean_ctor_get(v_inst_6772_, 1);
    crate::leanh::lean_inc_n(v_toBind_6778_, 3);
    crate::leanh::lean_dec_ref(v_inst_6772_);
    v_set_6779_ = crate::leanh::lean_ctor_get(v_inst_6773_, 1);
    crate::leanh::lean_inc(v_set_6779_);
    v_modifyGet_6780_ = crate::leanh::lean_ctor_get(v_inst_6773_, 2);
    crate::leanh::lean_inc(v_modifyGet_6780_);
    crate::leanh::lean_dec_ref(v_inst_6773_);
    v_toPure_6781_ = crate::leanh::lean_ctor_get(v_toApplicative_6777_, 1);
    crate::leanh::lean_inc(v_toPure_6781_);
    crate::leanh::lean_dec_ref(v_toApplicative_6777_);
    v___f_6782_ = l_Lake_takeLog___redArg___closed__0;
    v___x_6783_ =
        crate::leanh::lean_apply_2(v_modifyGet_6780_, crate::leanh::lean_box(0), v___f_6782_);
    v___f_6784_ = crate::leanh::lean_alloc_closure(
        l_Lake_LogT_takeAndRun___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_6784_, 0, v_toPure_6781_);
    crate::leanh::lean_closure_set(v___f_6784_, 1, v_set_6779_);
    crate::leanh::lean_closure_set(v___f_6784_, 2, v_toBind_6778_);
    v___f_6785_ = crate::leanh::lean_alloc_closure(
        l_Lake_LogT_takeAndRun___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_6785_, 0, v_self_6776_);
    crate::leanh::lean_closure_set(v___f_6785_, 1, v_inst_6774_);
    crate::leanh::lean_closure_set(v___f_6785_, 2, v_toBind_6778_);
    crate::leanh::lean_closure_set(v___f_6785_, 3, v___f_6784_);
    v___x_6786_ = crate::leanh::lean_apply_4(
        v_toBind_6778_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_6783_,
        v___f_6785_,
    );
    return v___x_6786_;
}
pub unsafe fn l_Lake_LogT_takeAndRun___boxed(
    mut v_n_6787_: *mut crate::leanh::LeanObject,
    mut v_m_6788_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_6789_: *mut crate::leanh::LeanObject,
    mut v_inst_6790_: *mut crate::leanh::LeanObject,
    mut v_inst_6791_: *mut crate::leanh::LeanObject,
    mut v_inst_6792_: *mut crate::leanh::LeanObject,
    mut v_inst_6793_: *mut crate::leanh::LeanObject,
    mut v_self_6794_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6795_ = l_Lake_LogT_takeAndRun(
        v_n_6787_,
        v_m_6788_,
        v_00_u03b1_6789_,
        v_inst_6790_,
        v_inst_6791_,
        v_inst_6792_,
        v_inst_6793_,
        v_self_6794_,
    );
    crate::leanh::lean_dec(v_inst_6793_);
    return v_res_6795_;
}
pub unsafe fn l_Lake_LogT_replayLog___redArg___lam__2(
    mut v_toPure_6796_: *mut crate::leanh::LeanObject,
    mut v___x_6797_: *mut crate::leanh::LeanObject,
    mut v_toBind_6798_: *mut crate::leanh::LeanObject,
    mut v_inst_6799_: *mut crate::leanh::LeanObject,
    mut v___f_6800_: *mut crate::leanh::LeanObject,
    mut v_____x_6801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_6802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6807_: u8 = 0;
    v_fst_6802_ = crate::leanh::lean_ctor_get(v_____x_6801_, 0);
    crate::leanh::lean_inc(v_fst_6802_);
    v_snd_6803_ = crate::leanh::lean_ctor_get(v_____x_6801_, 1);
    crate::leanh::lean_inc(v_snd_6803_);
    crate::leanh::lean_dec_ref(v_____x_6801_);
    crate::leanh::lean_inc(v_toPure_6796_);
    v___f_6804_ = crate::leanh::lean_alloc_closure(
        l_Lake_LogT_takeAndRun___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_6804_, 0, v_toPure_6796_);
    crate::leanh::lean_closure_set(v___f_6804_, 1, v_fst_6802_);
    v___x_6805_ = lean_array_get_size(v_snd_6803_);
    v___x_6806_ = crate::leanh::lean_box(0);
    v___x_6807_ = lean_nat_dec_lt(v___x_6797_, v___x_6805_);
    if v___x_6807_ == 0 {
        let mut v___x_6808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_snd_6803_);
        crate::leanh::lean_dec(v___f_6800_);
        crate::leanh::lean_dec_ref(v_inst_6799_);
        v___x_6808_ =
            crate::leanh::lean_apply_2(v_toPure_6796_, crate::leanh::lean_box(0), v___x_6806_);
        v___x_6809_ = crate::leanh::lean_apply_4(
            v_toBind_6798_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_6808_,
            v___f_6804_,
        );
        return v___x_6809_;
    } else {
        let mut v___x_6810_: u8 = 0;
        v___x_6810_ = lean_nat_dec_le(v___x_6805_, v___x_6805_);
        if v___x_6810_ == 0 {
            if v___x_6807_ == 0 {
                let mut v___x_6811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_6812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_snd_6803_);
                crate::leanh::lean_dec(v___f_6800_);
                crate::leanh::lean_dec_ref(v_inst_6799_);
                v___x_6811_ = crate::leanh::lean_apply_2(
                    v_toPure_6796_,
                    crate::leanh::lean_box(0),
                    v___x_6806_,
                );
                v___x_6812_ = crate::leanh::lean_apply_4(
                    v_toBind_6798_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_6811_,
                    v___f_6804_,
                );
                return v___x_6812_;
            } else {
                let mut v___x_6813_: usize = 0;
                let mut v___x_6814_: usize = 0;
                let mut v___x_6815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_6816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_toPure_6796_);
                v___x_6813_ = 0usize;
                v___x_6814_ = lean_usize_of_nat(v___x_6805_);
                v___x_6815_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v_inst_6799_,
                    v___f_6800_,
                    v_snd_6803_,
                    v___x_6813_,
                    v___x_6814_,
                    v___x_6806_,
                );
                v___x_6816_ = crate::leanh::lean_apply_4(
                    v_toBind_6798_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_6815_,
                    v___f_6804_,
                );
                return v___x_6816_;
            }
        } else {
            let mut v___x_6817_: usize = 0;
            let mut v___x_6818_: usize = 0;
            let mut v___x_6819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_toPure_6796_);
            v___x_6817_ = 0usize;
            v___x_6818_ = lean_usize_of_nat(v___x_6805_);
            v___x_6819_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v_inst_6799_,
                v___f_6800_,
                v_snd_6803_,
                v___x_6817_,
                v___x_6818_,
                v___x_6806_,
            );
            v___x_6820_ = crate::leanh::lean_apply_4(
                v_toBind_6798_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_6819_,
                v___f_6804_,
            );
            return v___x_6820_;
        }
    }
}
pub unsafe fn l_Lake_LogT_replayLog___redArg___lam__2___boxed(
    mut v_toPure_6821_: *mut crate::leanh::LeanObject,
    mut v___x_6822_: *mut crate::leanh::LeanObject,
    mut v_toBind_6823_: *mut crate::leanh::LeanObject,
    mut v_inst_6824_: *mut crate::leanh::LeanObject,
    mut v___f_6825_: *mut crate::leanh::LeanObject,
    mut v_____x_6826_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6827_ = l_Lake_LogT_replayLog___redArg___lam__2(
        v_toPure_6821_,
        v___x_6822_,
        v_toBind_6823_,
        v_inst_6824_,
        v___f_6825_,
        v_____x_6826_,
    );
    crate::leanh::lean_dec(v___x_6822_);
    return v_res_6827_;
}
pub unsafe fn l_Lake_LogT_replayLog___redArg(
    mut v_inst_6828_: *mut crate::leanh::LeanObject,
    mut v_logger_6829_: *mut crate::leanh::LeanObject,
    mut v_inst_6830_: *mut crate::leanh::LeanObject,
    mut v_self_6831_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_6832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_6833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_6834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_6832_ = crate::leanh::lean_ctor_get(v_inst_6828_, 0);
    v_toBind_6833_ = crate::leanh::lean_ctor_get(v_inst_6828_, 1);
    crate::leanh::lean_inc_n(v_toBind_6833_, 2);
    v_toPure_6834_ = crate::leanh::lean_ctor_get(v_toApplicative_6832_, 1);
    crate::leanh::lean_inc(v_toPure_6834_);
    v___f_6835_ = crate::leanh::lean_alloc_closure(
        l_Lake_Log_replay___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_6835_, 0, v_logger_6829_);
    v___x_6836_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_6837_ = l_Lake_Log_empty___closed__0;
    v___x_6838_ = crate::leanh::lean_apply_1(v_self_6831_, v___x_6837_);
    v___x_6839_ = crate::leanh::lean_apply_2(v_inst_6830_, crate::leanh::lean_box(0), v___x_6838_);
    v___f_6840_ = crate::leanh::lean_alloc_closure(
        l_Lake_LogT_replayLog___redArg___lam__2___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_6840_, 0, v_toPure_6834_);
    crate::leanh::lean_closure_set(v___f_6840_, 1, v___x_6836_);
    crate::leanh::lean_closure_set(v___f_6840_, 2, v_toBind_6833_);
    crate::leanh::lean_closure_set(v___f_6840_, 3, v_inst_6828_);
    crate::leanh::lean_closure_set(v___f_6840_, 4, v___f_6835_);
    v___x_6841_ = crate::leanh::lean_apply_4(
        v_toBind_6833_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_6839_,
        v___f_6840_,
    );
    return v___x_6841_;
}
pub unsafe fn l_Lake_LogT_replayLog(
    mut v_n_6842_: *mut crate::leanh::LeanObject,
    mut v_m_6843_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_6844_: *mut crate::leanh::LeanObject,
    mut v_inst_6845_: *mut crate::leanh::LeanObject,
    mut v_logger_6846_: *mut crate::leanh::LeanObject,
    mut v_inst_6847_: *mut crate::leanh::LeanObject,
    mut v_self_6848_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_6849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_6850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_6851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_6849_ = crate::leanh::lean_ctor_get(v_inst_6845_, 0);
    v_toBind_6850_ = crate::leanh::lean_ctor_get(v_inst_6845_, 1);
    crate::leanh::lean_inc_n(v_toBind_6850_, 2);
    v_toPure_6851_ = crate::leanh::lean_ctor_get(v_toApplicative_6849_, 1);
    crate::leanh::lean_inc(v_toPure_6851_);
    v___f_6852_ = crate::leanh::lean_alloc_closure(
        l_Lake_Log_replay___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_6852_, 0, v_logger_6846_);
    v___x_6853_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_6854_ = l_Lake_Log_empty___closed__0;
    v___x_6855_ = crate::leanh::lean_apply_1(v_self_6848_, v___x_6854_);
    v___x_6856_ = crate::leanh::lean_apply_2(v_inst_6847_, crate::leanh::lean_box(0), v___x_6855_);
    v___f_6857_ = crate::leanh::lean_alloc_closure(
        l_Lake_LogT_replayLog___redArg___lam__2___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_6857_, 0, v_toPure_6851_);
    crate::leanh::lean_closure_set(v___f_6857_, 1, v___x_6853_);
    crate::leanh::lean_closure_set(v___f_6857_, 2, v_toBind_6850_);
    crate::leanh::lean_closure_set(v___f_6857_, 3, v_inst_6845_);
    crate::leanh::lean_closure_set(v___f_6857_, 4, v___f_6852_);
    v___x_6858_ = crate::leanh::lean_apply_4(
        v_toBind_6850_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_6856_,
        v___f_6857_,
    );
    return v___x_6858_;
}
pub unsafe fn l_Lake_instMonadLogELogTOfMonad___redArg(
    mut v_inst_6859_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_6860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_6861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_6860_ = crate::leanh::lean_ctor_get(v_inst_6859_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_6860_);
    crate::leanh::lean_dec_ref(v_inst_6859_);
    v_toPure_6861_ = crate::leanh::lean_ctor_get(v_toApplicative_6860_, 1);
    crate::leanh::lean_inc(v_toPure_6861_);
    crate::leanh::lean_dec_ref(v_toApplicative_6860_);
    v___x_6862_ = l_Lake_EStateT_instMonadStateOfOfPure___redArg(v_toPure_6861_);
    v___x_6863_ =
        crate::leanh::lean_alloc_closure(l_Lake_pushLogEntry as *mut core::ffi::c_void, 3, 2);
    crate::leanh::lean_closure_set(v___x_6863_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_6863_, 1, v___x_6862_);
    return v___x_6863_;
}
pub unsafe fn l_Lake_instMonadLogELogTOfMonad(
    mut v_m_6864_: *mut crate::leanh::LeanObject,
    mut v_inst_6865_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6866_ = l_Lake_instMonadLogELogTOfMonad___redArg(v_inst_6865_);
    return v___x_6866_;
}
pub unsafe fn l_Lake_instMonadErrorELogTOfMonad___redArg___lam__0(
    mut v_x_6867_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_6868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6872_: u8 = 0;
    let mut v___x_6873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6877_: u8 = 0;
    let mut v_a_6878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6882_: u8 = 0;
    let mut v___x_6884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6886_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_6867_) == 0 {
                    v_a_6868_ = crate::leanh::lean_ctor_get(v_x_6867_, 0);
                    v_a_6869_ = crate::leanh::lean_ctor_get(v_x_6867_, 1);
                    v_isSharedCheck_6877_ = (!crate::leanh::lean_is_exclusive(v_x_6867_)) as u8;
                    if v_isSharedCheck_6877_ == 0 {
                        v___x_6871_ = v_x_6867_;
                        v_isShared_6872_ = v_isSharedCheck_6877_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6869_);
                        crate::leanh::lean_inc(v_a_6868_);
                        crate::leanh::lean_dec(v_x_6867_);
                        v___x_6871_ = crate::leanh::lean_box(0);
                        v_isShared_6872_ = v_isSharedCheck_6877_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6878_ = crate::leanh::lean_ctor_get(v_x_6867_, 0);
                    v_a_6879_ = crate::leanh::lean_ctor_get(v_x_6867_, 1);
                    v_isSharedCheck_6886_ = (!crate::leanh::lean_is_exclusive(v_x_6867_)) as u8;
                    if v_isSharedCheck_6886_ == 0 {
                        v___x_6881_ = v_x_6867_;
                        v_isShared_6882_ = v_isSharedCheck_6886_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6879_);
                        crate::leanh::lean_inc(v_a_6878_);
                        crate::leanh::lean_dec(v_x_6867_);
                        v___x_6881_ = crate::leanh::lean_box(0);
                        v_isShared_6882_ = v_isSharedCheck_6886_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6873_ = lean_array_get_size(v_a_6868_);
                crate::leanh::lean_dec(v_a_6868_);
                if v_isShared_6872_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6871_, 0, v___x_6873_);
                    v___x_6875_ = v___x_6871_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6876_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6876_, 0, v___x_6873_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6876_, 1, v_a_6869_);
                    v___x_6875_ = v_reuseFailAlloc_6876_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6875_;
            }
            3 => {
                if v_isShared_6882_ == 0 {
                    v___x_6884_ = v___x_6881_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6885_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6885_, 0, v_a_6878_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6885_, 1, v_a_6879_);
                    v___x_6884_ = v_reuseFailAlloc_6885_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6884_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instMonadErrorELogTOfMonad___redArg___lam__1(
    mut v_a_6887_: *mut crate::leanh::LeanObject,
    mut v_toPure_6888_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_6889_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_6890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6893_: u8 = 0;
    let mut v___x_6895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6898_: u8 = 0;
    let mut v_unused_6899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6904_: u8 = 0;
    let mut v___x_6906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6909_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_____do__lift_6889_) == 0 {
                    v_a_6890_ = crate::leanh::lean_ctor_get(v_____do__lift_6889_, 1);
                    v_isSharedCheck_6898_ =
                        (!crate::leanh::lean_is_exclusive(v_____do__lift_6889_)) as u8;
                    if v_isSharedCheck_6898_ == 0 {
                        v_unused_6899_ = crate::leanh::lean_ctor_get(v_____do__lift_6889_, 0);
                        crate::leanh::lean_dec(v_unused_6899_);
                        v___x_6892_ = v_____do__lift_6889_;
                        v_isShared_6893_ = v_isSharedCheck_6898_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6890_);
                        crate::leanh::lean_dec(v_____do__lift_6889_);
                        v___x_6892_ = crate::leanh::lean_box(0);
                        v_isShared_6893_ = v_isSharedCheck_6898_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_6887_);
                    v_a_6900_ = crate::leanh::lean_ctor_get(v_____do__lift_6889_, 0);
                    v_a_6901_ = crate::leanh::lean_ctor_get(v_____do__lift_6889_, 1);
                    v_isSharedCheck_6909_ =
                        (!crate::leanh::lean_is_exclusive(v_____do__lift_6889_)) as u8;
                    if v_isSharedCheck_6909_ == 0 {
                        v___x_6903_ = v_____do__lift_6889_;
                        v_isShared_6904_ = v_isSharedCheck_6909_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6901_);
                        crate::leanh::lean_inc(v_a_6900_);
                        crate::leanh::lean_dec(v_____do__lift_6889_);
                        v___x_6903_ = crate::leanh::lean_box(0);
                        v_isShared_6904_ = v_isSharedCheck_6909_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6893_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6892_, 1);
                    crate::leanh::lean_ctor_set(v___x_6892_, 0, v_a_6887_);
                    v___x_6895_ = v___x_6892_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6897_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6897_, 0, v_a_6887_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6897_, 1, v_a_6890_);
                    v___x_6895_ = v_reuseFailAlloc_6897_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6896_ = crate::leanh::lean_apply_2(
                    v_toPure_6888_,
                    crate::leanh::lean_box(0),
                    v___x_6895_,
                );
                return v___x_6896_;
            }
            3 => {
                if v_isShared_6904_ == 0 {
                    v___x_6906_ = v___x_6903_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6908_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6908_, 0, v_a_6900_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6908_, 1, v_a_6901_);
                    v___x_6906_ = v_reuseFailAlloc_6908_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6907_ = crate::leanh::lean_apply_2(
                    v_toPure_6888_,
                    crate::leanh::lean_box(0),
                    v___x_6906_,
                );
                return v___x_6907_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instMonadErrorELogTOfMonad___redArg___lam__2(
    mut v_toPure_6910_: *mut crate::leanh::LeanObject,
    mut v___x_6911_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_6912_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6917_: u8 = 0;
    let mut v___x_6919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6922_: u8 = 0;
    let mut v_unused_6923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_____do__lift_6912_) == 0 {
                    v___x_6913_ = crate::leanh::lean_apply_2(
                        v_toPure_6910_,
                        crate::leanh::lean_box(0),
                        v_____do__lift_6912_,
                    );
                    return v___x_6913_;
                } else {
                    v_a_6914_ = crate::leanh::lean_ctor_get(v_____do__lift_6912_, 1);
                    v_isSharedCheck_6922_ =
                        (!crate::leanh::lean_is_exclusive(v_____do__lift_6912_)) as u8;
                    if v_isSharedCheck_6922_ == 0 {
                        v_unused_6923_ = crate::leanh::lean_ctor_get(v_____do__lift_6912_, 0);
                        crate::leanh::lean_dec(v_unused_6923_);
                        v___x_6916_ = v_____do__lift_6912_;
                        v_isShared_6917_ = v_isSharedCheck_6922_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6914_);
                        crate::leanh::lean_dec(v_____do__lift_6912_);
                        v___x_6916_ = crate::leanh::lean_box(0);
                        v_isShared_6917_ = v_isSharedCheck_6922_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6917_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6916_, 0);
                    crate::leanh::lean_ctor_set(v___x_6916_, 0, v___x_6911_);
                    v___x_6919_ = v___x_6916_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6921_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6921_, 0, v___x_6911_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6921_, 1, v_a_6914_);
                    v___x_6919_ = v_reuseFailAlloc_6921_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6920_ = crate::leanh::lean_apply_2(
                    v_toPure_6910_,
                    crate::leanh::lean_box(0),
                    v___x_6919_,
                );
                return v___x_6920_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instMonadErrorELogTOfMonad___redArg___lam__3(
    mut v_toPure_6924_: *mut crate::leanh::LeanObject,
    mut v___x_6925_: *mut crate::leanh::LeanObject,
    mut v_toBind_6926_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_6927_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_6928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6932_: u8 = 0;
    let mut v___f_6933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6943_: u8 = 0;
    let mut v_a_6944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6948_: u8 = 0;
    let mut v___x_6950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6953_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_____do__lift_6927_) == 0 {
                    v_a_6928_ = crate::leanh::lean_ctor_get(v_____do__lift_6927_, 0);
                    v_a_6929_ = crate::leanh::lean_ctor_get(v_____do__lift_6927_, 1);
                    v_isSharedCheck_6943_ =
                        (!crate::leanh::lean_is_exclusive(v_____do__lift_6927_)) as u8;
                    if v_isSharedCheck_6943_ == 0 {
                        v___x_6931_ = v_____do__lift_6927_;
                        v_isShared_6932_ = v_isSharedCheck_6943_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6929_);
                        crate::leanh::lean_inc(v_a_6928_);
                        crate::leanh::lean_dec(v_____do__lift_6927_);
                        v___x_6931_ = crate::leanh::lean_box(0);
                        v_isShared_6932_ = v_isSharedCheck_6943_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_toBind_6926_);
                    crate::leanh::lean_dec_ref(v___x_6925_);
                    v_a_6944_ = crate::leanh::lean_ctor_get(v_____do__lift_6927_, 0);
                    v_a_6945_ = crate::leanh::lean_ctor_get(v_____do__lift_6927_, 1);
                    v_isSharedCheck_6953_ =
                        (!crate::leanh::lean_is_exclusive(v_____do__lift_6927_)) as u8;
                    if v_isSharedCheck_6953_ == 0 {
                        v___x_6947_ = v_____do__lift_6927_;
                        v_isShared_6948_ = v_isSharedCheck_6953_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6945_);
                        crate::leanh::lean_inc(v_a_6944_);
                        crate::leanh::lean_dec(v_____do__lift_6927_);
                        v___x_6947_ = crate::leanh::lean_box(0);
                        v_isShared_6948_ = v_isSharedCheck_6953_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_n(v_toPure_6924_, 2);
                v___f_6933_ = crate::leanh::lean_alloc_closure(
                    l_Lake_instMonadErrorELogTOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_6933_, 0, v_a_6928_);
                crate::leanh::lean_closure_set(v___f_6933_, 1, v_toPure_6924_);
                v___x_6934_ = crate::leanh::lean_box(0);
                v___f_6935_ = crate::leanh::lean_alloc_closure(
                    l_Lake_instMonadErrorELogTOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_6935_, 0, v_toPure_6924_);
                crate::leanh::lean_closure_set(v___f_6935_, 1, v___x_6934_);
                v___x_6936_ = lean_array_push(v_a_6929_, v___x_6925_);
                if v_isShared_6932_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6931_, 1, v___x_6936_);
                    crate::leanh::lean_ctor_set(v___x_6931_, 0, v___x_6934_);
                    v___x_6938_ = v___x_6931_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6942_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6942_, 0, v___x_6934_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6942_, 1, v___x_6936_);
                    v___x_6938_ = v_reuseFailAlloc_6942_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6939_ = crate::leanh::lean_apply_2(
                    v_toPure_6924_,
                    crate::leanh::lean_box(0),
                    v___x_6938_,
                );
                crate::leanh::lean_inc(v_toBind_6926_);
                v___x_6940_ = crate::leanh::lean_apply_4(
                    v_toBind_6926_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_6939_,
                    v___f_6935_,
                );
                v___x_6941_ = crate::leanh::lean_apply_4(
                    v_toBind_6926_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_6940_,
                    v___f_6933_,
                );
                return v___x_6941_;
            }
            3 => {
                if v_isShared_6948_ == 0 {
                    v___x_6950_ = v___x_6947_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6952_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6952_, 0, v_a_6944_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6952_, 1, v_a_6945_);
                    v___x_6950_ = v_reuseFailAlloc_6952_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6951_ = crate::leanh::lean_apply_2(
                    v_toPure_6924_,
                    crate::leanh::lean_box(0),
                    v___x_6950_,
                );
                return v___x_6951_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instMonadErrorELogTOfMonad___redArg___lam__4(
    mut v_toFunctor_6954_: *mut crate::leanh::LeanObject,
    mut v_toPure_6955_: *mut crate::leanh::LeanObject,
    mut v_toBind_6956_: *mut crate::leanh::LeanObject,
    mut v___f_6957_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_6958_: *mut crate::leanh::LeanObject,
    mut v___y_6959_: *mut crate::leanh::LeanObject,
    mut v___y_6960_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_6961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6964_: u8 = 0;
    let mut v___x_6965_: u8 = 0;
    let mut v___x_6966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6974_: u8 = 0;
    let mut v_unused_6975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_6961_ = crate::leanh::lean_ctor_get(v_toFunctor_6954_, 0);
                v_isSharedCheck_6974_ = (!crate::leanh::lean_is_exclusive(v_toFunctor_6954_)) as u8;
                if v_isSharedCheck_6974_ == 0 {
                    v_unused_6975_ = crate::leanh::lean_ctor_get(v_toFunctor_6954_, 1);
                    crate::leanh::lean_dec(v_unused_6975_);
                    v___x_6963_ = v_toFunctor_6954_;
                    v_isShared_6964_ = v_isSharedCheck_6974_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_map_6961_);
                    crate::leanh::lean_dec(v_toFunctor_6954_);
                    v___x_6963_ = crate::leanh::lean_box(0);
                    v_isShared_6964_ = v_isSharedCheck_6974_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6965_ = 3;
                v___x_6966_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_6966_, 0, v___y_6959_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6966_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_6965_,
                );
                crate::leanh::lean_inc(v_toBind_6956_);
                crate::leanh::lean_inc(v_toPure_6955_);
                v___f_6967_ = crate::leanh::lean_alloc_closure(
                    l_Lake_instMonadErrorELogTOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_6967_, 0, v_toPure_6955_);
                crate::leanh::lean_closure_set(v___f_6967_, 1, v___x_6966_);
                crate::leanh::lean_closure_set(v___f_6967_, 2, v_toBind_6956_);
                crate::leanh::lean_inc_ref(v___y_6960_);
                if v_isShared_6964_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6963_, 1, v___y_6960_);
                    crate::leanh::lean_ctor_set(v___x_6963_, 0, v___y_6960_);
                    v___x_6969_ = v___x_6963_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6973_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6973_, 0, v___y_6960_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6973_, 1, v___y_6960_);
                    v___x_6969_ = v_reuseFailAlloc_6973_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6970_ = crate::leanh::lean_apply_2(
                    v_toPure_6955_,
                    crate::leanh::lean_box(0),
                    v___x_6969_,
                );
                v___x_6971_ = crate::leanh::lean_apply_4(
                    v_map_6961_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___f_6957_,
                    v___x_6970_,
                );
                v___x_6972_ = crate::leanh::lean_apply_4(
                    v_toBind_6956_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_6971_,
                    v___f_6967_,
                );
                return v___x_6972_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instMonadErrorELogTOfMonad___redArg(
    mut v_inst_6977_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_6978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_6979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_6980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_6981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_6978_ = crate::leanh::lean_ctor_get(v_inst_6977_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_6978_);
    v_toBind_6979_ = crate::leanh::lean_ctor_get(v_inst_6977_, 1);
    crate::leanh::lean_inc(v_toBind_6979_);
    crate::leanh::lean_dec_ref(v_inst_6977_);
    v_toFunctor_6980_ = crate::leanh::lean_ctor_get(v_toApplicative_6978_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_6980_);
    v_toPure_6981_ = crate::leanh::lean_ctor_get(v_toApplicative_6978_, 1);
    crate::leanh::lean_inc(v_toPure_6981_);
    crate::leanh::lean_dec_ref(v_toApplicative_6978_);
    v___f_6982_ = l_Lake_instMonadErrorELogTOfMonad___redArg___closed__0;
    v___f_6983_ = crate::leanh::lean_alloc_closure(
        l_Lake_instMonadErrorELogTOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
        7,
        4,
    );
    crate::leanh::lean_closure_set(v___f_6983_, 0, v_toFunctor_6980_);
    crate::leanh::lean_closure_set(v___f_6983_, 1, v_toPure_6981_);
    crate::leanh::lean_closure_set(v___f_6983_, 2, v_toBind_6979_);
    crate::leanh::lean_closure_set(v___f_6983_, 3, v___f_6982_);
    return v___f_6983_;
}
pub unsafe fn l_Lake_instMonadErrorELogTOfMonad(
    mut v_m_6984_: *mut crate::leanh::LeanObject,
    mut v_inst_6985_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6986_ = l_Lake_instMonadErrorELogTOfMonad___redArg(v_inst_6985_);
    return v___x_6986_;
}
pub unsafe fn l_Lake_instAlternativeELogTOfMonad___redArg___lam__1(
    mut v___y_6987_: *mut crate::leanh::LeanObject,
    mut v___x_6988_: *mut crate::leanh::LeanObject,
    mut v_toPure_6989_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_6990_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_6991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6997_: u8 = 0;
    let mut v___x_6999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7002_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_____do__lift_6990_) == 0 {
                    crate::leanh::lean_dec(v_toPure_6989_);
                    v_a_6991_ = crate::leanh::lean_ctor_get(v_____do__lift_6990_, 1);
                    crate::leanh::lean_inc(v_a_6991_);
                    crate::leanh::lean_dec_ref_known(v_____do__lift_6990_, 2);
                    v___x_6992_ = crate::leanh::lean_apply_2(v___y_6987_, v___x_6988_, v_a_6991_);
                    return v___x_6992_;
                } else {
                    crate::leanh::lean_dec(v___y_6987_);
                    v_a_6993_ = crate::leanh::lean_ctor_get(v_____do__lift_6990_, 0);
                    v_a_6994_ = crate::leanh::lean_ctor_get(v_____do__lift_6990_, 1);
                    v_isSharedCheck_7002_ =
                        (!crate::leanh::lean_is_exclusive(v_____do__lift_6990_)) as u8;
                    if v_isSharedCheck_7002_ == 0 {
                        v___x_6996_ = v_____do__lift_6990_;
                        v_isShared_6997_ = v_isSharedCheck_7002_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6994_);
                        crate::leanh::lean_inc(v_a_6993_);
                        crate::leanh::lean_dec(v_____do__lift_6990_);
                        v___x_6996_ = crate::leanh::lean_box(0);
                        v_isShared_6997_ = v_isSharedCheck_7002_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6997_ == 0 {
                    v___x_6999_ = v___x_6996_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7001_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7001_, 0, v_a_6993_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7001_, 1, v_a_6994_);
                    v___x_6999_ = v_reuseFailAlloc_7001_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7000_ = crate::leanh::lean_apply_2(
                    v_toPure_6989_,
                    crate::leanh::lean_box(0),
                    v___x_6999_,
                );
                return v___x_7000_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instAlternativeELogTOfMonad___redArg___lam__0(
    mut v_toPure_7003_: *mut crate::leanh::LeanObject,
    mut v___y_7004_: *mut crate::leanh::LeanObject,
    mut v_toBind_7005_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_7006_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7012_: u8 = 0;
    let mut v___x_7013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7021_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_____do__lift_7006_) == 0 {
                    crate::leanh::lean_dec(v_toBind_7005_);
                    crate::leanh::lean_dec(v___y_7004_);
                    v___x_7007_ = crate::leanh::lean_apply_2(
                        v_toPure_7003_,
                        crate::leanh::lean_box(0),
                        v_____do__lift_7006_,
                    );
                    return v___x_7007_;
                } else {
                    v_a_7008_ = crate::leanh::lean_ctor_get(v_____do__lift_7006_, 0);
                    v_a_7009_ = crate::leanh::lean_ctor_get(v_____do__lift_7006_, 1);
                    v_isSharedCheck_7021_ =
                        (!crate::leanh::lean_is_exclusive(v_____do__lift_7006_)) as u8;
                    if v_isSharedCheck_7021_ == 0 {
                        v___x_7011_ = v_____do__lift_7006_;
                        v_isShared_7012_ = v_isSharedCheck_7021_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7009_);
                        crate::leanh::lean_inc(v_a_7008_);
                        crate::leanh::lean_dec(v_____do__lift_7006_);
                        v___x_7011_ = crate::leanh::lean_box(0);
                        v_isShared_7012_ = v_isSharedCheck_7021_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7013_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_toPure_7003_);
                v___f_7014_ = crate::leanh::lean_alloc_closure(
                    l_Lake_instAlternativeELogTOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_7014_, 0, v___y_7004_);
                crate::leanh::lean_closure_set(v___f_7014_, 1, v___x_7013_);
                crate::leanh::lean_closure_set(v___f_7014_, 2, v_toPure_7003_);
                v___x_7015_ = l_Array_shrink___redArg(v_a_7009_, v_a_7008_);
                crate::leanh::lean_dec(v_a_7008_);
                if v_isShared_7012_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_7011_, 0);
                    crate::leanh::lean_ctor_set(v___x_7011_, 1, v___x_7015_);
                    crate::leanh::lean_ctor_set(v___x_7011_, 0, v___x_7013_);
                    v___x_7017_ = v___x_7011_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7020_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7020_, 0, v___x_7013_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7020_, 1, v___x_7015_);
                    v___x_7017_ = v_reuseFailAlloc_7020_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7018_ = crate::leanh::lean_apply_2(
                    v_toPure_7003_,
                    crate::leanh::lean_box(0),
                    v___x_7017_,
                );
                v___x_7019_ = crate::leanh::lean_apply_4(
                    v_toBind_7005_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_7018_,
                    v___f_7014_,
                );
                return v___x_7019_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instAlternativeELogTOfMonad___redArg___lam__2(
    mut v_toPure_7022_: *mut crate::leanh::LeanObject,
    mut v_toBind_7023_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_7024_: *mut crate::leanh::LeanObject,
    mut v___y_7025_: *mut crate::leanh::LeanObject,
    mut v___y_7026_: *mut crate::leanh::LeanObject,
    mut v___y_7027_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_7028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_toBind_7023_);
    v___f_7028_ = crate::leanh::lean_alloc_closure(
        l_Lake_instAlternativeELogTOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_7028_, 0, v_toPure_7022_);
    crate::leanh::lean_closure_set(v___f_7028_, 1, v___y_7026_);
    crate::leanh::lean_closure_set(v___f_7028_, 2, v_toBind_7023_);
    v___x_7029_ = crate::leanh::lean_apply_1(v___y_7025_, v___y_7027_);
    v___x_7030_ = crate::leanh::lean_apply_4(
        v_toBind_7023_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_7029_,
        v___f_7028_,
    );
    return v___x_7030_;
}
pub unsafe fn l_Lake_instAlternativeELogTOfMonad___redArg___lam__3(
    mut v_toPure_7031_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_7032_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_7033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7037_: u8 = 0;
    let mut v___x_7039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7042_: u8 = 0;
    let mut v_a_7043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7047_: u8 = 0;
    let mut v___x_7049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7052_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_____do__lift_7032_) == 0 {
                    v_a_7033_ = crate::leanh::lean_ctor_get(v_____do__lift_7032_, 0);
                    v_a_7034_ = crate::leanh::lean_ctor_get(v_____do__lift_7032_, 1);
                    v_isSharedCheck_7042_ =
                        (!crate::leanh::lean_is_exclusive(v_____do__lift_7032_)) as u8;
                    if v_isSharedCheck_7042_ == 0 {
                        v___x_7036_ = v_____do__lift_7032_;
                        v_isShared_7037_ = v_isSharedCheck_7042_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7034_);
                        crate::leanh::lean_inc(v_a_7033_);
                        crate::leanh::lean_dec(v_____do__lift_7032_);
                        v___x_7036_ = crate::leanh::lean_box(0);
                        v_isShared_7037_ = v_isSharedCheck_7042_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7043_ = crate::leanh::lean_ctor_get(v_____do__lift_7032_, 0);
                    v_a_7044_ = crate::leanh::lean_ctor_get(v_____do__lift_7032_, 1);
                    v_isSharedCheck_7052_ =
                        (!crate::leanh::lean_is_exclusive(v_____do__lift_7032_)) as u8;
                    if v_isSharedCheck_7052_ == 0 {
                        v___x_7046_ = v_____do__lift_7032_;
                        v_isShared_7047_ = v_isSharedCheck_7052_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7044_);
                        crate::leanh::lean_inc(v_a_7043_);
                        crate::leanh::lean_dec(v_____do__lift_7032_);
                        v___x_7046_ = crate::leanh::lean_box(0);
                        v_isShared_7047_ = v_isSharedCheck_7052_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7037_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_7036_, 1);
                    v___x_7039_ = v___x_7036_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7041_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7041_, 0, v_a_7033_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7041_, 1, v_a_7034_);
                    v___x_7039_ = v_reuseFailAlloc_7041_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7040_ = crate::leanh::lean_apply_2(
                    v_toPure_7031_,
                    crate::leanh::lean_box(0),
                    v___x_7039_,
                );
                return v___x_7040_;
            }
            3 => {
                if v_isShared_7047_ == 0 {
                    v___x_7049_ = v___x_7046_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7051_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7051_, 0, v_a_7043_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7051_, 1, v_a_7044_);
                    v___x_7049_ = v_reuseFailAlloc_7051_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_7050_ = crate::leanh::lean_apply_2(
                    v_toPure_7031_,
                    crate::leanh::lean_box(0),
                    v___x_7049_,
                );
                return v___x_7050_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instAlternativeELogTOfMonad___redArg___lam__4(
    mut v_toFunctor_7053_: *mut crate::leanh::LeanObject,
    mut v_toPure_7054_: *mut crate::leanh::LeanObject,
    mut v___f_7055_: *mut crate::leanh::LeanObject,
    mut v_toBind_7056_: *mut crate::leanh::LeanObject,
    mut v___f_7057_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_7058_: *mut crate::leanh::LeanObject,
    mut v___y_7059_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_7060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7063_: u8 = 0;
    let mut v___x_7065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7070_: u8 = 0;
    let mut v_unused_7071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_7060_ = crate::leanh::lean_ctor_get(v_toFunctor_7053_, 0);
                v_isSharedCheck_7070_ = (!crate::leanh::lean_is_exclusive(v_toFunctor_7053_)) as u8;
                if v_isSharedCheck_7070_ == 0 {
                    v_unused_7071_ = crate::leanh::lean_ctor_get(v_toFunctor_7053_, 1);
                    crate::leanh::lean_dec(v_unused_7071_);
                    v___x_7062_ = v_toFunctor_7053_;
                    v_isShared_7063_ = v_isSharedCheck_7070_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_map_7060_);
                    crate::leanh::lean_dec(v_toFunctor_7053_);
                    v___x_7062_ = crate::leanh::lean_box(0);
                    v_isShared_7063_ = v_isSharedCheck_7070_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v___y_7059_);
                if v_isShared_7063_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7062_, 1, v___y_7059_);
                    crate::leanh::lean_ctor_set(v___x_7062_, 0, v___y_7059_);
                    v___x_7065_ = v___x_7062_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7069_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7069_, 0, v___y_7059_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7069_, 1, v___y_7059_);
                    v___x_7065_ = v_reuseFailAlloc_7069_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7066_ = crate::leanh::lean_apply_2(
                    v_toPure_7054_,
                    crate::leanh::lean_box(0),
                    v___x_7065_,
                );
                v___x_7067_ = crate::leanh::lean_apply_4(
                    v_map_7060_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___f_7055_,
                    v___x_7066_,
                );
                v___x_7068_ = crate::leanh::lean_apply_4(
                    v_toBind_7056_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_7067_,
                    v___f_7057_,
                );
                return v___x_7068_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instAlternativeELogTOfMonad___redArg(
    mut v_inst_7072_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_7073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_7074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_7075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_7076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7079_: u8 = 0;
    let mut v___f_7080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7094_: u8 = 0;
    let mut v_unused_7095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_7073_ = crate::leanh::lean_ctor_get(v_inst_7072_, 0);
                crate::leanh::lean_inc_ref(v_toApplicative_7073_);
                v_toBind_7074_ = crate::leanh::lean_ctor_get(v_inst_7072_, 1);
                crate::leanh::lean_inc(v_toBind_7074_);
                crate::leanh::lean_dec_ref(v_inst_7072_);
                v_toFunctor_7075_ = crate::leanh::lean_ctor_get(v_toApplicative_7073_, 0);
                v_toPure_7076_ = crate::leanh::lean_ctor_get(v_toApplicative_7073_, 1);
                v_isSharedCheck_7094_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_7073_)) as u8;
                if v_isSharedCheck_7094_ == 0 {
                    v_unused_7095_ = crate::leanh::lean_ctor_get(v_toApplicative_7073_, 4);
                    crate::leanh::lean_dec(v_unused_7095_);
                    v_unused_7096_ = crate::leanh::lean_ctor_get(v_toApplicative_7073_, 3);
                    crate::leanh::lean_dec(v_unused_7096_);
                    v_unused_7097_ = crate::leanh::lean_ctor_get(v_toApplicative_7073_, 2);
                    crate::leanh::lean_dec(v_unused_7097_);
                    v___x_7078_ = v_toApplicative_7073_;
                    v_isShared_7079_ = v_isSharedCheck_7094_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toPure_7076_);
                    crate::leanh::lean_inc(v_toFunctor_7075_);
                    crate::leanh::lean_dec(v_toApplicative_7073_);
                    v___x_7078_ = crate::leanh::lean_box(0);
                    v_isShared_7079_ = v_isSharedCheck_7094_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_7080_ = l_Lake_instMonadErrorELogTOfMonad___redArg___closed__0;
                crate::leanh::lean_inc_n(v_toBind_7074_, 4);
                crate::leanh::lean_inc_n(v_toPure_7076_, 7);
                v___f_7081_ = crate::leanh::lean_alloc_closure(
                    l_Lake_instAlternativeELogTOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
                    6,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_7081_, 0, v_toPure_7076_);
                crate::leanh::lean_closure_set(v___f_7081_, 1, v_toBind_7074_);
                v___f_7082_ = crate::leanh::lean_alloc_closure(
                    l_Lake_instAlternativeELogTOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_7082_, 0, v_toPure_7076_);
                crate::leanh::lean_inc_ref_n(v_toFunctor_7075_, 2);
                v___f_7083_ = crate::leanh::lean_alloc_closure(
                    l_Lake_instAlternativeELogTOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    7,
                    5,
                );
                crate::leanh::lean_closure_set(v___f_7083_, 0, v_toFunctor_7075_);
                crate::leanh::lean_closure_set(v___f_7083_, 1, v_toPure_7076_);
                crate::leanh::lean_closure_set(v___f_7083_, 2, v___f_7080_);
                crate::leanh::lean_closure_set(v___f_7083_, 3, v_toBind_7074_);
                crate::leanh::lean_closure_set(v___f_7083_, 4, v___f_7082_);
                v___f_7084_ = crate::leanh::lean_alloc_closure(
                    l_Lake_EStateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    7,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_7084_, 0, v_toPure_7076_);
                crate::leanh::lean_closure_set(v___f_7084_, 1, v_toBind_7074_);
                v___f_7085_ = crate::leanh::lean_alloc_closure(
                    l_Lake_EStateT_instMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    7,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_7085_, 0, v_toPure_7076_);
                crate::leanh::lean_closure_set(v___f_7085_, 1, v_toBind_7074_);
                v___f_7086_ = crate::leanh::lean_alloc_closure(
                    l_Lake_EStateT_instMonad___redArg___lam__5 as *mut core::ffi::c_void,
                    7,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_7086_, 0, v_toPure_7076_);
                crate::leanh::lean_closure_set(v___f_7086_, 1, v___f_7084_);
                v___f_7087_ = crate::leanh::lean_alloc_closure(
                    l_Lake_EStateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
                    8,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_7087_, 0, v_toFunctor_7075_);
                crate::leanh::lean_closure_set(v___f_7087_, 1, v_toPure_7076_);
                crate::leanh::lean_closure_set(v___f_7087_, 2, v_toBind_7074_);
                v___x_7088_ = l_Lake_EStateT_instFunctor___redArg(v_toFunctor_7075_);
                v___f_7089_ = crate::leanh::lean_alloc_closure(
                    l_Lake_EStateT_instPure___redArg___lam__0 as *mut core::ffi::c_void,
                    4,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_7089_, 0, v_toPure_7076_);
                if v_isShared_7079_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7078_, 4, v___f_7085_);
                    crate::leanh::lean_ctor_set(v___x_7078_, 3, v___f_7086_);
                    crate::leanh::lean_ctor_set(v___x_7078_, 2, v___f_7087_);
                    crate::leanh::lean_ctor_set(v___x_7078_, 1, v___f_7089_);
                    crate::leanh::lean_ctor_set(v___x_7078_, 0, v___x_7088_);
                    v___x_7091_ = v___x_7078_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7093_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7093_, 0, v___x_7088_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7093_, 1, v___f_7089_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7093_, 2, v___f_7087_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7093_, 3, v___f_7086_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7093_, 4, v___f_7085_);
                    v___x_7091_ = v_reuseFailAlloc_7093_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7092_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7092_, 0, v___x_7091_);
                crate::leanh::lean_ctor_set(v___x_7092_, 1, v___f_7083_);
                crate::leanh::lean_ctor_set(v___x_7092_, 2, v___f_7081_);
                return v___x_7092_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instAlternativeELogTOfMonad(
    mut v_m_7098_: *mut crate::leanh::LeanObject,
    mut v_inst_7099_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7100_ = l_Lake_instAlternativeELogTOfMonad___redArg(v_inst_7099_);
    return v___x_7100_;
}
pub unsafe fn l_Lake_ELogT_run___redArg(
    mut v_self_7101_: *mut crate::leanh::LeanObject,
    mut v_log_7102_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7103_ = crate::leanh::lean_apply_1(v_self_7101_, v_log_7102_);
    return v___x_7103_;
}
pub unsafe fn l_Lake_ELogT_run(
    mut v_m_7104_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_7105_: *mut crate::leanh::LeanObject,
    mut v_self_7106_: *mut crate::leanh::LeanObject,
    mut v_log_7107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7108_ = crate::leanh::lean_apply_1(v_self_7106_, v_log_7107_);
    return v___x_7108_;
}
pub unsafe fn l_Lake_ELogT_run_x27___redArg(
    mut v_inst_7110_: *mut crate::leanh::LeanObject,
    mut v_self_7111_: *mut crate::leanh::LeanObject,
    mut v_log_7112_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_7113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_7113_ = crate::leanh::lean_ctor_get(v_inst_7110_, 0);
    crate::leanh::lean_inc(v_map_7113_);
    crate::leanh::lean_dec_ref(v_inst_7110_);
    v___x_7114_ = l_Lake_ELogT_run_x27___redArg___closed__0;
    v___x_7115_ = crate::leanh::lean_apply_1(v_self_7111_, v_log_7112_);
    v___x_7116_ = crate::leanh::lean_apply_4(
        v_map_7113_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_7114_,
        v___x_7115_,
    );
    return v___x_7116_;
}
pub unsafe fn l_Lake_ELogT_run_x27(
    mut v_m_7117_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_7118_: *mut crate::leanh::LeanObject,
    mut v_inst_7119_: *mut crate::leanh::LeanObject,
    mut v_self_7120_: *mut crate::leanh::LeanObject,
    mut v_log_7121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_7122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_7122_ = crate::leanh::lean_ctor_get(v_inst_7119_, 0);
    crate::leanh::lean_inc(v_map_7122_);
    crate::leanh::lean_dec_ref(v_inst_7119_);
    v___x_7123_ = l_Lake_ELogT_run_x27___redArg___closed__0;
    v___x_7124_ = crate::leanh::lean_apply_1(v_self_7120_, v_log_7121_);
    v___x_7125_ = crate::leanh::lean_apply_4(
        v_map_7122_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_7123_,
        v___x_7124_,
    );
    return v___x_7125_;
}
pub unsafe fn l_Lake_ELogT_toLogT___redArg(
    mut v_inst_7127_: *mut crate::leanh::LeanObject,
    mut v_self_7128_: *mut crate::leanh::LeanObject,
    mut v_a_7129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_7130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_7130_ = crate::leanh::lean_ctor_get(v_inst_7127_, 0);
    crate::leanh::lean_inc(v_map_7130_);
    crate::leanh::lean_dec_ref(v_inst_7127_);
    v___x_7131_ = l_Lake_ELogT_toLogT___redArg___closed__0;
    v___x_7132_ = crate::leanh::lean_apply_1(v_self_7128_, v_a_7129_);
    v___x_7133_ = crate::leanh::lean_apply_4(
        v_map_7130_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_7131_,
        v___x_7132_,
    );
    return v___x_7133_;
}
pub unsafe fn l_Lake_ELogT_toLogT(
    mut v_m_7134_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_7135_: *mut crate::leanh::LeanObject,
    mut v_inst_7136_: *mut crate::leanh::LeanObject,
    mut v_self_7137_: *mut crate::leanh::LeanObject,
    mut v_a_7138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_7139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_7139_ = crate::leanh::lean_ctor_get(v_inst_7136_, 0);
    crate::leanh::lean_inc(v_map_7139_);
    crate::leanh::lean_dec_ref(v_inst_7136_);
    v___x_7140_ = l_Lake_ELogT_toLogT___redArg___closed__0;
    v___x_7141_ = crate::leanh::lean_apply_1(v_self_7137_, v_a_7138_);
    v___x_7142_ = crate::leanh::lean_apply_4(
        v_map_7139_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_7140_,
        v___x_7141_,
    );
    return v___x_7142_;
}
pub unsafe fn l_Lake_ELogT_toLogT_x3f___redArg(
    mut v_inst_7144_: *mut crate::leanh::LeanObject,
    mut v_self_7145_: *mut crate::leanh::LeanObject,
    mut v_a_7146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_7147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_7147_ = crate::leanh::lean_ctor_get(v_inst_7144_, 0);
    crate::leanh::lean_inc(v_map_7147_);
    crate::leanh::lean_dec_ref(v_inst_7144_);
    v___x_7148_ = l_Lake_ELogT_toLogT_x3f___redArg___closed__0;
    v___x_7149_ = crate::leanh::lean_apply_1(v_self_7145_, v_a_7146_);
    v___x_7150_ = crate::leanh::lean_apply_4(
        v_map_7147_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_7148_,
        v___x_7149_,
    );
    return v___x_7150_;
}
pub unsafe fn l_Lake_ELogT_toLogT_x3f(
    mut v_m_7151_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_7152_: *mut crate::leanh::LeanObject,
    mut v_inst_7153_: *mut crate::leanh::LeanObject,
    mut v_self_7154_: *mut crate::leanh::LeanObject,
    mut v_a_7155_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_7156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_7156_ = crate::leanh::lean_ctor_get(v_inst_7153_, 0);
    crate::leanh::lean_inc(v_map_7156_);
    crate::leanh::lean_dec_ref(v_inst_7153_);
    v___x_7157_ = l_Lake_ELogT_toLogT_x3f___redArg___closed__0;
    v___x_7158_ = crate::leanh::lean_apply_1(v_self_7154_, v_a_7155_);
    v___x_7159_ = crate::leanh::lean_apply_4(
        v_map_7156_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_7157_,
        v___x_7158_,
    );
    return v___x_7159_;
}
pub unsafe fn l_Lake_ELogT_run_x3f___redArg(
    mut v_inst_7160_: *mut crate::leanh::LeanObject,
    mut v_self_7161_: *mut crate::leanh::LeanObject,
    mut v_log_7162_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_7163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_7163_ = crate::leanh::lean_ctor_get(v_inst_7160_, 0);
    crate::leanh::lean_inc(v_map_7163_);
    crate::leanh::lean_dec_ref(v_inst_7160_);
    v___x_7164_ = l_Lake_ELogT_toLogT_x3f___redArg___closed__0;
    v___x_7165_ = crate::leanh::lean_apply_1(v_self_7161_, v_log_7162_);
    v___x_7166_ = crate::leanh::lean_apply_4(
        v_map_7163_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_7164_,
        v___x_7165_,
    );
    return v___x_7166_;
}
pub unsafe fn l_Lake_ELogT_run_x3f(
    mut v_m_7167_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_7168_: *mut crate::leanh::LeanObject,
    mut v_inst_7169_: *mut crate::leanh::LeanObject,
    mut v_self_7170_: *mut crate::leanh::LeanObject,
    mut v_log_7171_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_7172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_7172_ = crate::leanh::lean_ctor_get(v_inst_7169_, 0);
    crate::leanh::lean_inc(v_map_7172_);
    crate::leanh::lean_dec_ref(v_inst_7169_);
    v___x_7173_ = l_Lake_ELogT_toLogT_x3f___redArg___closed__0;
    v___x_7174_ = crate::leanh::lean_apply_1(v_self_7170_, v_log_7171_);
    v___x_7175_ = crate::leanh::lean_apply_4(
        v_map_7172_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_7173_,
        v___x_7174_,
    );
    return v___x_7175_;
}
pub unsafe fn l_Lake_ELogT_run_x3f_x27___redArg(
    mut v_inst_7177_: *mut crate::leanh::LeanObject,
    mut v_self_7178_: *mut crate::leanh::LeanObject,
    mut v_log_7179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_7180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_7180_ = crate::leanh::lean_ctor_get(v_inst_7177_, 0);
    crate::leanh::lean_inc(v_map_7180_);
    crate::leanh::lean_dec_ref(v_inst_7177_);
    v___x_7181_ = l_Lake_ELogT_run_x3f_x27___redArg___closed__0;
    v___x_7182_ = crate::leanh::lean_apply_1(v_self_7178_, v_log_7179_);
    v___x_7183_ = crate::leanh::lean_apply_4(
        v_map_7180_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_7181_,
        v___x_7182_,
    );
    return v___x_7183_;
}
pub unsafe fn l_Lake_ELogT_run_x3f_x27(
    mut v_m_7184_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_7185_: *mut crate::leanh::LeanObject,
    mut v_inst_7186_: *mut crate::leanh::LeanObject,
    mut v_self_7187_: *mut crate::leanh::LeanObject,
    mut v_log_7188_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_7189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_7189_ = crate::leanh::lean_ctor_get(v_inst_7186_, 0);
    crate::leanh::lean_inc(v_map_7189_);
    crate::leanh::lean_dec_ref(v_inst_7186_);
    v___x_7190_ = l_Lake_ELogT_run_x3f_x27___redArg___closed__0;
    v___x_7191_ = crate::leanh::lean_apply_1(v_self_7187_, v_log_7188_);
    v___x_7192_ = crate::leanh::lean_apply_4(
        v_map_7189_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_7190_,
        v___x_7191_,
    );
    return v___x_7192_;
}
pub unsafe fn l_Lake_ELogT_catchLog___redArg___lam__0(
    mut v_f_7193_: *mut crate::leanh::LeanObject,
    mut v_____x_7194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_7195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_7195_ = crate::leanh::lean_ctor_get(v_____x_7194_, 0);
    crate::leanh::lean_inc(v_fst_7195_);
    v_snd_7196_ = crate::leanh::lean_ctor_get(v_____x_7194_, 1);
    crate::leanh::lean_inc(v_snd_7196_);
    crate::leanh::lean_dec_ref(v_____x_7194_);
    v___x_7197_ = crate::leanh::lean_apply_2(v_f_7193_, v_fst_7195_, v_snd_7196_);
    return v___x_7197_;
}
pub unsafe fn l_Lake_ELogT_catchLog___redArg___lam__1(
    mut v_toPure_7198_: *mut crate::leanh::LeanObject,
    mut v_toBind_7199_: *mut crate::leanh::LeanObject,
    mut v___f_7200_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_7201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_7202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7206_: u8 = 0;
    let mut v___x_7208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7211_: u8 = 0;
    let mut v_a_7212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7216_: u8 = 0;
    let mut v___x_7217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7225_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_____do__lift_7201_) == 0 {
                    crate::leanh::lean_dec(v___f_7200_);
                    crate::leanh::lean_dec(v_toBind_7199_);
                    v_a_7202_ = crate::leanh::lean_ctor_get(v_____do__lift_7201_, 0);
                    v_a_7203_ = crate::leanh::lean_ctor_get(v_____do__lift_7201_, 1);
                    v_isSharedCheck_7211_ =
                        (!crate::leanh::lean_is_exclusive(v_____do__lift_7201_)) as u8;
                    if v_isSharedCheck_7211_ == 0 {
                        v___x_7205_ = v_____do__lift_7201_;
                        v_isShared_7206_ = v_isSharedCheck_7211_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7203_);
                        crate::leanh::lean_inc(v_a_7202_);
                        crate::leanh::lean_dec(v_____do__lift_7201_);
                        v___x_7205_ = crate::leanh::lean_box(0);
                        v_isShared_7206_ = v_isSharedCheck_7211_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7212_ = crate::leanh::lean_ctor_get(v_____do__lift_7201_, 0);
                    v_a_7213_ = crate::leanh::lean_ctor_get(v_____do__lift_7201_, 1);
                    v_isSharedCheck_7225_ =
                        (!crate::leanh::lean_is_exclusive(v_____do__lift_7201_)) as u8;
                    if v_isSharedCheck_7225_ == 0 {
                        v___x_7215_ = v_____do__lift_7201_;
                        v_isShared_7216_ = v_isSharedCheck_7225_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7213_);
                        crate::leanh::lean_inc(v_a_7212_);
                        crate::leanh::lean_dec(v_____do__lift_7201_);
                        v___x_7215_ = crate::leanh::lean_box(0);
                        v_isShared_7216_ = v_isSharedCheck_7225_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7206_ == 0 {
                    v___x_7208_ = v___x_7205_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7210_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7210_, 0, v_a_7202_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7210_, 1, v_a_7203_);
                    v___x_7208_ = v_reuseFailAlloc_7210_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7209_ = crate::leanh::lean_apply_2(
                    v_toPure_7198_,
                    crate::leanh::lean_box(0),
                    v___x_7208_,
                );
                return v___x_7209_;
            }
            3 => {
                v___x_7217_ = lean_array_get_size(v_a_7213_);
                crate::leanh::lean_inc(v_a_7212_);
                v___x_7218_ = l_Array_extract___redArg(v_a_7213_, v_a_7212_, v___x_7217_);
                v___x_7219_ = l_Array_shrink___redArg(v_a_7213_, v_a_7212_);
                crate::leanh::lean_dec(v_a_7212_);
                if v_isShared_7216_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_7215_, 0);
                    crate::leanh::lean_ctor_set(v___x_7215_, 1, v___x_7219_);
                    crate::leanh::lean_ctor_set(v___x_7215_, 0, v___x_7218_);
                    v___x_7221_ = v___x_7215_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7224_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7224_, 0, v___x_7218_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7224_, 1, v___x_7219_);
                    v___x_7221_ = v_reuseFailAlloc_7224_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_7222_ = crate::leanh::lean_apply_2(
                    v_toPure_7198_,
                    crate::leanh::lean_box(0),
                    v___x_7221_,
                );
                v___x_7223_ = crate::leanh::lean_apply_4(
                    v_toBind_7199_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_7222_,
                    v___f_7200_,
                );
                return v___x_7223_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_ELogT_catchLog___redArg(
    mut v_inst_7226_: *mut crate::leanh::LeanObject,
    mut v_f_7227_: *mut crate::leanh::LeanObject,
    mut v_self_7228_: *mut crate::leanh::LeanObject,
    mut v_a_7229_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_7230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_7231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_7232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_7230_ = crate::leanh::lean_ctor_get(v_inst_7226_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_7230_);
    v_toBind_7231_ = crate::leanh::lean_ctor_get(v_inst_7226_, 1);
    crate::leanh::lean_inc_n(v_toBind_7231_, 2);
    crate::leanh::lean_dec_ref(v_inst_7226_);
    v_toPure_7232_ = crate::leanh::lean_ctor_get(v_toApplicative_7230_, 1);
    crate::leanh::lean_inc(v_toPure_7232_);
    crate::leanh::lean_dec_ref(v_toApplicative_7230_);
    v___f_7233_ = crate::leanh::lean_alloc_closure(
        l_Lake_ELogT_catchLog___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_7233_, 0, v_f_7227_);
    v___x_7234_ = crate::leanh::lean_apply_1(v_self_7228_, v_a_7229_);
    v___f_7235_ = crate::leanh::lean_alloc_closure(
        l_Lake_ELogT_catchLog___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_7235_, 0, v_toPure_7232_);
    crate::leanh::lean_closure_set(v___f_7235_, 1, v_toBind_7231_);
    crate::leanh::lean_closure_set(v___f_7235_, 2, v___f_7233_);
    v___x_7236_ = crate::leanh::lean_apply_4(
        v_toBind_7231_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_7234_,
        v___f_7235_,
    );
    return v___x_7236_;
}
pub unsafe fn l_Lake_ELogT_catchLog(
    mut v_m_7237_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_7238_: *mut crate::leanh::LeanObject,
    mut v_inst_7239_: *mut crate::leanh::LeanObject,
    mut v_f_7240_: *mut crate::leanh::LeanObject,
    mut v_self_7241_: *mut crate::leanh::LeanObject,
    mut v_a_7242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_7243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_7244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_7245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_7243_ = crate::leanh::lean_ctor_get(v_inst_7239_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_7243_);
    v_toBind_7244_ = crate::leanh::lean_ctor_get(v_inst_7239_, 1);
    crate::leanh::lean_inc_n(v_toBind_7244_, 2);
    crate::leanh::lean_dec_ref(v_inst_7239_);
    v_toPure_7245_ = crate::leanh::lean_ctor_get(v_toApplicative_7243_, 1);
    crate::leanh::lean_inc(v_toPure_7245_);
    crate::leanh::lean_dec_ref(v_toApplicative_7243_);
    v___f_7246_ = crate::leanh::lean_alloc_closure(
        l_Lake_ELogT_catchLog___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_7246_, 0, v_f_7240_);
    v___x_7247_ = crate::leanh::lean_apply_1(v_self_7241_, v_a_7242_);
    v___f_7248_ = crate::leanh::lean_alloc_closure(
        l_Lake_ELogT_catchLog___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_7248_, 0, v_toPure_7245_);
    crate::leanh::lean_closure_set(v___f_7248_, 1, v_toBind_7244_);
    crate::leanh::lean_closure_set(v___f_7248_, 2, v___f_7246_);
    v___x_7249_ = crate::leanh::lean_apply_4(
        v_toBind_7244_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_7247_,
        v___f_7248_,
    );
    return v___x_7249_;
}
pub unsafe fn l_Lake_ELogT_takeAndRun___redArg___lam__1(
    mut v_toPure_7250_: *mut crate::leanh::LeanObject,
    mut v_a_7251_: *mut crate::leanh::LeanObject,
    mut v_____r_7252_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7253_ = crate::leanh::lean_apply_2(v_toPure_7250_, crate::leanh::lean_box(0), v_a_7251_);
    return v___x_7253_;
}
pub unsafe fn l_Lake_ELogT_takeAndRun___redArg___lam__0(
    mut v_inst_7254_: *mut crate::leanh::LeanObject,
    mut v_a_7255_: *mut crate::leanh::LeanObject,
    mut v_____r_7256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_throw_7257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_throw_7257_ = crate::leanh::lean_ctor_get(v_inst_7254_, 0);
    crate::leanh::lean_inc(v_throw_7257_);
    crate::leanh::lean_dec_ref(v_inst_7254_);
    v___x_7258_ = crate::leanh::lean_apply_2(v_throw_7257_, crate::leanh::lean_box(0), v_a_7255_);
    return v___x_7258_;
}
pub unsafe fn l_Lake_ELogT_takeAndRun___redArg___lam__2(
    mut v_toPure_7259_: *mut crate::leanh::LeanObject,
    mut v_set_7260_: *mut crate::leanh::LeanObject,
    mut v_toBind_7261_: *mut crate::leanh::LeanObject,
    mut v_inst_7262_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_7263_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_7263_) == 0 {
        let mut v_a_7264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_7265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_7266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_inst_7262_);
        v_a_7264_ = crate::leanh::lean_ctor_get(v_____do__lift_7263_, 0);
        crate::leanh::lean_inc(v_a_7264_);
        v_a_7265_ = crate::leanh::lean_ctor_get(v_____do__lift_7263_, 1);
        crate::leanh::lean_inc(v_a_7265_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_7263_, 2);
        v___f_7266_ = crate::leanh::lean_alloc_closure(
            l_Lake_ELogT_takeAndRun___redArg___lam__1 as *mut core::ffi::c_void,
            3,
            2,
        );
        crate::leanh::lean_closure_set(v___f_7266_, 0, v_toPure_7259_);
        crate::leanh::lean_closure_set(v___f_7266_, 1, v_a_7264_);
        v___x_7267_ = crate::leanh::lean_apply_1(v_set_7260_, v_a_7265_);
        v___x_7268_ = crate::leanh::lean_apply_4(
            v_toBind_7261_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_7267_,
            v___f_7266_,
        );
        return v___x_7268_;
    } else {
        let mut v_a_7269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_7270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_7271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_7259_);
        v_a_7269_ = crate::leanh::lean_ctor_get(v_____do__lift_7263_, 0);
        crate::leanh::lean_inc(v_a_7269_);
        v_a_7270_ = crate::leanh::lean_ctor_get(v_____do__lift_7263_, 1);
        crate::leanh::lean_inc(v_a_7270_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_7263_, 2);
        v___f_7271_ = crate::leanh::lean_alloc_closure(
            l_Lake_ELogT_takeAndRun___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            2,
        );
        crate::leanh::lean_closure_set(v___f_7271_, 0, v_inst_7262_);
        crate::leanh::lean_closure_set(v___f_7271_, 1, v_a_7269_);
        v___x_7272_ = crate::leanh::lean_apply_1(v_set_7260_, v_a_7270_);
        v___x_7273_ = crate::leanh::lean_apply_4(
            v_toBind_7261_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_7272_,
            v___f_7271_,
        );
        return v___x_7273_;
    }
}
pub unsafe fn l_Lake_ELogT_takeAndRun___redArg___lam__3(
    mut v_self_7274_: *mut crate::leanh::LeanObject,
    mut v_inst_7275_: *mut crate::leanh::LeanObject,
    mut v_toBind_7276_: *mut crate::leanh::LeanObject,
    mut v___f_7277_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_7278_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7279_ = crate::leanh::lean_apply_1(v_self_7274_, v_____do__lift_7278_);
    v___x_7280_ = crate::leanh::lean_apply_2(v_inst_7275_, crate::leanh::lean_box(0), v___x_7279_);
    v___x_7281_ = crate::leanh::lean_apply_4(
        v_toBind_7276_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_7280_,
        v___f_7277_,
    );
    return v___x_7281_;
}
pub unsafe fn l_Lake_ELogT_takeAndRun___redArg(
    mut v_inst_7282_: *mut crate::leanh::LeanObject,
    mut v_inst_7283_: *mut crate::leanh::LeanObject,
    mut v_inst_7284_: *mut crate::leanh::LeanObject,
    mut v_inst_7285_: *mut crate::leanh::LeanObject,
    mut v_self_7286_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_7287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_7288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_set_7289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_7290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_7291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_7287_ = crate::leanh::lean_ctor_get(v_inst_7282_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_7287_);
    v_toBind_7288_ = crate::leanh::lean_ctor_get(v_inst_7282_, 1);
    crate::leanh::lean_inc_n(v_toBind_7288_, 3);
    crate::leanh::lean_dec_ref(v_inst_7282_);
    v_set_7289_ = crate::leanh::lean_ctor_get(v_inst_7283_, 1);
    crate::leanh::lean_inc(v_set_7289_);
    v_modifyGet_7290_ = crate::leanh::lean_ctor_get(v_inst_7283_, 2);
    crate::leanh::lean_inc(v_modifyGet_7290_);
    crate::leanh::lean_dec_ref(v_inst_7283_);
    v_toPure_7291_ = crate::leanh::lean_ctor_get(v_toApplicative_7287_, 1);
    crate::leanh::lean_inc(v_toPure_7291_);
    crate::leanh::lean_dec_ref(v_toApplicative_7287_);
    v___f_7292_ = l_Lake_takeLog___redArg___closed__0;
    v___x_7293_ =
        crate::leanh::lean_apply_2(v_modifyGet_7290_, crate::leanh::lean_box(0), v___f_7292_);
    v___f_7294_ = crate::leanh::lean_alloc_closure(
        l_Lake_ELogT_takeAndRun___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_7294_, 0, v_toPure_7291_);
    crate::leanh::lean_closure_set(v___f_7294_, 1, v_set_7289_);
    crate::leanh::lean_closure_set(v___f_7294_, 2, v_toBind_7288_);
    crate::leanh::lean_closure_set(v___f_7294_, 3, v_inst_7284_);
    v___f_7295_ = crate::leanh::lean_alloc_closure(
        l_Lake_ELogT_takeAndRun___redArg___lam__3 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_7295_, 0, v_self_7286_);
    crate::leanh::lean_closure_set(v___f_7295_, 1, v_inst_7285_);
    crate::leanh::lean_closure_set(v___f_7295_, 2, v_toBind_7288_);
    crate::leanh::lean_closure_set(v___f_7295_, 3, v___f_7294_);
    v___x_7296_ = crate::leanh::lean_apply_4(
        v_toBind_7288_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_7293_,
        v___f_7295_,
    );
    return v___x_7296_;
}
pub unsafe fn l_Lake_ELogT_takeAndRun(
    mut v_n_7297_: *mut crate::leanh::LeanObject,
    mut v_m_7298_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_7299_: *mut crate::leanh::LeanObject,
    mut v_inst_7300_: *mut crate::leanh::LeanObject,
    mut v_inst_7301_: *mut crate::leanh::LeanObject,
    mut v_inst_7302_: *mut crate::leanh::LeanObject,
    mut v_inst_7303_: *mut crate::leanh::LeanObject,
    mut v_self_7304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_7305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_7306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_set_7307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_7308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_7309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_7305_ = crate::leanh::lean_ctor_get(v_inst_7300_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_7305_);
    v_toBind_7306_ = crate::leanh::lean_ctor_get(v_inst_7300_, 1);
    crate::leanh::lean_inc_n(v_toBind_7306_, 3);
    crate::leanh::lean_dec_ref(v_inst_7300_);
    v_set_7307_ = crate::leanh::lean_ctor_get(v_inst_7301_, 1);
    crate::leanh::lean_inc(v_set_7307_);
    v_modifyGet_7308_ = crate::leanh::lean_ctor_get(v_inst_7301_, 2);
    crate::leanh::lean_inc(v_modifyGet_7308_);
    crate::leanh::lean_dec_ref(v_inst_7301_);
    v_toPure_7309_ = crate::leanh::lean_ctor_get(v_toApplicative_7305_, 1);
    crate::leanh::lean_inc(v_toPure_7309_);
    crate::leanh::lean_dec_ref(v_toApplicative_7305_);
    v___f_7310_ = l_Lake_takeLog___redArg___closed__0;
    v___x_7311_ =
        crate::leanh::lean_apply_2(v_modifyGet_7308_, crate::leanh::lean_box(0), v___f_7310_);
    v___f_7312_ = crate::leanh::lean_alloc_closure(
        l_Lake_ELogT_takeAndRun___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_7312_, 0, v_toPure_7309_);
    crate::leanh::lean_closure_set(v___f_7312_, 1, v_set_7307_);
    crate::leanh::lean_closure_set(v___f_7312_, 2, v_toBind_7306_);
    crate::leanh::lean_closure_set(v___f_7312_, 3, v_inst_7302_);
    v___f_7313_ = crate::leanh::lean_alloc_closure(
        l_Lake_ELogT_takeAndRun___redArg___lam__3 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_7313_, 0, v_self_7304_);
    crate::leanh::lean_closure_set(v___f_7313_, 1, v_inst_7303_);
    crate::leanh::lean_closure_set(v___f_7313_, 2, v_toBind_7306_);
    crate::leanh::lean_closure_set(v___f_7313_, 3, v___f_7312_);
    v___x_7314_ = crate::leanh::lean_apply_4(
        v_toBind_7306_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_7311_,
        v___f_7313_,
    );
    return v___x_7314_;
}
pub unsafe fn l_Lake_ELogT_replayLog_x3f___redArg___lam__2(
    mut v_toPure_7315_: *mut crate::leanh::LeanObject,
    mut v_x_7316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7317_ = crate::leanh::lean_box(0);
    v___x_7318_ =
        crate::leanh::lean_apply_2(v_toPure_7315_, crate::leanh::lean_box(0), v___x_7317_);
    return v___x_7318_;
}
pub unsafe fn l_Lake_ELogT_replayLog_x3f___redArg___lam__0(
    mut v_a_7319_: *mut crate::leanh::LeanObject,
    mut v_toPure_7320_: *mut crate::leanh::LeanObject,
    mut v_x_7321_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7322_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_7322_, 0, v_a_7319_);
    v___x_7323_ =
        crate::leanh::lean_apply_2(v_toPure_7320_, crate::leanh::lean_box(0), v___x_7322_);
    return v___x_7323_;
}
pub unsafe fn l_Lake_ELogT_replayLog_x3f___redArg___lam__1(
    mut v_toPure_7324_: *mut crate::leanh::LeanObject,
    mut v___x_7325_: *mut crate::leanh::LeanObject,
    mut v_toSeqRight_7326_: *mut crate::leanh::LeanObject,
    mut v_inst_7327_: *mut crate::leanh::LeanObject,
    mut v___f_7328_: *mut crate::leanh::LeanObject,
    mut v___f_7329_: *mut crate::leanh::LeanObject,
    mut v___f_7330_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_7331_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_7331_) == 0 {
        let mut v_a_7332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_7333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_7334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7337_: u8 = 0;
        crate::leanh::lean_dec(v___f_7330_);
        crate::leanh::lean_dec(v___f_7329_);
        v_a_7332_ = crate::leanh::lean_ctor_get(v_____do__lift_7331_, 0);
        crate::leanh::lean_inc(v_a_7332_);
        v_a_7333_ = crate::leanh::lean_ctor_get(v_____do__lift_7331_, 1);
        crate::leanh::lean_inc(v_a_7333_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_7331_, 2);
        crate::leanh::lean_inc(v_toPure_7324_);
        v___f_7334_ = crate::leanh::lean_alloc_closure(
            l_Lake_ELogT_replayLog_x3f___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            2,
        );
        crate::leanh::lean_closure_set(v___f_7334_, 0, v_a_7332_);
        crate::leanh::lean_closure_set(v___f_7334_, 1, v_toPure_7324_);
        v___x_7335_ = lean_array_get_size(v_a_7333_);
        v___x_7336_ = crate::leanh::lean_box(0);
        v___x_7337_ = lean_nat_dec_lt(v___x_7325_, v___x_7335_);
        if v___x_7337_ == 0 {
            let mut v___x_7338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_a_7333_);
            crate::leanh::lean_dec(v___f_7328_);
            crate::leanh::lean_dec_ref(v_inst_7327_);
            v___x_7338_ =
                crate::leanh::lean_apply_2(v_toPure_7324_, crate::leanh::lean_box(0), v___x_7336_);
            v___x_7339_ = crate::leanh::lean_apply_4(
                v_toSeqRight_7326_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_7338_,
                v___f_7334_,
            );
            return v___x_7339_;
        } else {
            let mut v___x_7340_: u8 = 0;
            v___x_7340_ = lean_nat_dec_le(v___x_7335_, v___x_7335_);
            if v___x_7340_ == 0 {
                if v___x_7337_ == 0 {
                    let mut v___x_7341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_7342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_a_7333_);
                    crate::leanh::lean_dec(v___f_7328_);
                    crate::leanh::lean_dec_ref(v_inst_7327_);
                    v___x_7341_ = crate::leanh::lean_apply_2(
                        v_toPure_7324_,
                        crate::leanh::lean_box(0),
                        v___x_7336_,
                    );
                    v___x_7342_ = crate::leanh::lean_apply_4(
                        v_toSeqRight_7326_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_7341_,
                        v___f_7334_,
                    );
                    return v___x_7342_;
                } else {
                    let mut v___x_7343_: usize = 0;
                    let mut v___x_7344_: usize = 0;
                    let mut v___x_7345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_7346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_toPure_7324_);
                    v___x_7343_ = 0usize;
                    v___x_7344_ = lean_usize_of_nat(v___x_7335_);
                    v___x_7345_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v_inst_7327_,
                        v___f_7328_,
                        v_a_7333_,
                        v___x_7343_,
                        v___x_7344_,
                        v___x_7336_,
                    );
                    v___x_7346_ = crate::leanh::lean_apply_4(
                        v_toSeqRight_7326_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_7345_,
                        v___f_7334_,
                    );
                    return v___x_7346_;
                }
            } else {
                let mut v___x_7347_: usize = 0;
                let mut v___x_7348_: usize = 0;
                let mut v___x_7349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_7350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_toPure_7324_);
                v___x_7347_ = 0usize;
                v___x_7348_ = lean_usize_of_nat(v___x_7335_);
                v___x_7349_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v_inst_7327_,
                    v___f_7328_,
                    v_a_7333_,
                    v___x_7347_,
                    v___x_7348_,
                    v___x_7336_,
                );
                v___x_7350_ = crate::leanh::lean_apply_4(
                    v_toSeqRight_7326_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_7349_,
                    v___f_7334_,
                );
                return v___x_7350_;
            }
        }
    } else {
        let mut v_a_7351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7354_: u8 = 0;
        crate::leanh::lean_dec(v___f_7328_);
        v_a_7351_ = crate::leanh::lean_ctor_get(v_____do__lift_7331_, 1);
        crate::leanh::lean_inc(v_a_7351_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_7331_, 2);
        v___x_7352_ = lean_array_get_size(v_a_7351_);
        v___x_7353_ = crate::leanh::lean_box(0);
        v___x_7354_ = lean_nat_dec_lt(v___x_7325_, v___x_7352_);
        if v___x_7354_ == 0 {
            let mut v___x_7355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_a_7351_);
            crate::leanh::lean_dec(v___f_7330_);
            crate::leanh::lean_dec_ref(v_inst_7327_);
            v___x_7355_ =
                crate::leanh::lean_apply_2(v_toPure_7324_, crate::leanh::lean_box(0), v___x_7353_);
            v___x_7356_ = crate::leanh::lean_apply_4(
                v_toSeqRight_7326_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_7355_,
                v___f_7329_,
            );
            return v___x_7356_;
        } else {
            let mut v___x_7357_: u8 = 0;
            v___x_7357_ = lean_nat_dec_le(v___x_7352_, v___x_7352_);
            if v___x_7357_ == 0 {
                if v___x_7354_ == 0 {
                    let mut v___x_7358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_7359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_a_7351_);
                    crate::leanh::lean_dec(v___f_7330_);
                    crate::leanh::lean_dec_ref(v_inst_7327_);
                    v___x_7358_ = crate::leanh::lean_apply_2(
                        v_toPure_7324_,
                        crate::leanh::lean_box(0),
                        v___x_7353_,
                    );
                    v___x_7359_ = crate::leanh::lean_apply_4(
                        v_toSeqRight_7326_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_7358_,
                        v___f_7329_,
                    );
                    return v___x_7359_;
                } else {
                    let mut v___x_7360_: usize = 0;
                    let mut v___x_7361_: usize = 0;
                    let mut v___x_7362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_7363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_toPure_7324_);
                    v___x_7360_ = 0usize;
                    v___x_7361_ = lean_usize_of_nat(v___x_7352_);
                    v___x_7362_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v_inst_7327_,
                        v___f_7330_,
                        v_a_7351_,
                        v___x_7360_,
                        v___x_7361_,
                        v___x_7353_,
                    );
                    v___x_7363_ = crate::leanh::lean_apply_4(
                        v_toSeqRight_7326_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_7362_,
                        v___f_7329_,
                    );
                    return v___x_7363_;
                }
            } else {
                let mut v___x_7364_: usize = 0;
                let mut v___x_7365_: usize = 0;
                let mut v___x_7366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_7367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_toPure_7324_);
                v___x_7364_ = 0usize;
                v___x_7365_ = lean_usize_of_nat(v___x_7352_);
                v___x_7366_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v_inst_7327_,
                    v___f_7330_,
                    v_a_7351_,
                    v___x_7364_,
                    v___x_7365_,
                    v___x_7353_,
                );
                v___x_7367_ = crate::leanh::lean_apply_4(
                    v_toSeqRight_7326_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_7366_,
                    v___f_7329_,
                );
                return v___x_7367_;
            }
        }
    }
}
pub unsafe fn l_Lake_ELogT_replayLog_x3f___redArg___lam__1___boxed(
    mut v_toPure_7368_: *mut crate::leanh::LeanObject,
    mut v___x_7369_: *mut crate::leanh::LeanObject,
    mut v_toSeqRight_7370_: *mut crate::leanh::LeanObject,
    mut v_inst_7371_: *mut crate::leanh::LeanObject,
    mut v___f_7372_: *mut crate::leanh::LeanObject,
    mut v___f_7373_: *mut crate::leanh::LeanObject,
    mut v___f_7374_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_7375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7376_ = l_Lake_ELogT_replayLog_x3f___redArg___lam__1(
        v_toPure_7368_,
        v___x_7369_,
        v_toSeqRight_7370_,
        v_inst_7371_,
        v___f_7372_,
        v___f_7373_,
        v___f_7374_,
        v_____do__lift_7375_,
    );
    crate::leanh::lean_dec(v___x_7369_);
    return v_res_7376_;
}
pub unsafe fn l_Lake_ELogT_replayLog_x3f___redArg(
    mut v_inst_7377_: *mut crate::leanh::LeanObject,
    mut v_logger_7378_: *mut crate::leanh::LeanObject,
    mut v_inst_7379_: *mut crate::leanh::LeanObject,
    mut v_self_7380_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_7381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_7382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_7383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_7384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_7381_ = crate::leanh::lean_ctor_get(v_inst_7377_, 0);
    v_toBind_7382_ = crate::leanh::lean_ctor_get(v_inst_7377_, 1);
    crate::leanh::lean_inc(v_toBind_7382_);
    v_toPure_7383_ = crate::leanh::lean_ctor_get(v_toApplicative_7381_, 1);
    crate::leanh::lean_inc_n(v_toPure_7383_, 2);
    v_toSeqRight_7384_ = crate::leanh::lean_ctor_get(v_toApplicative_7381_, 4);
    crate::leanh::lean_inc(v_toSeqRight_7384_);
    v___f_7385_ = crate::leanh::lean_alloc_closure(
        l_Lake_Log_replay___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_7385_, 0, v_logger_7378_);
    v___x_7386_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_7387_ = l_Lake_Log_empty___closed__0;
    v___x_7388_ = crate::leanh::lean_apply_1(v_self_7380_, v___x_7387_);
    v___x_7389_ = crate::leanh::lean_apply_2(v_inst_7379_, crate::leanh::lean_box(0), v___x_7388_);
    v___f_7390_ = crate::leanh::lean_alloc_closure(
        l_Lake_ELogT_replayLog_x3f___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_7390_, 0, v_toPure_7383_);
    crate::leanh::lean_inc_ref(v___f_7385_);
    v___f_7391_ = crate::leanh::lean_alloc_closure(
        l_Lake_ELogT_replayLog_x3f___redArg___lam__1___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    crate::leanh::lean_closure_set(v___f_7391_, 0, v_toPure_7383_);
    crate::leanh::lean_closure_set(v___f_7391_, 1, v___x_7386_);
    crate::leanh::lean_closure_set(v___f_7391_, 2, v_toSeqRight_7384_);
    crate::leanh::lean_closure_set(v___f_7391_, 3, v_inst_7377_);
    crate::leanh::lean_closure_set(v___f_7391_, 4, v___f_7385_);
    crate::leanh::lean_closure_set(v___f_7391_, 5, v___f_7390_);
    crate::leanh::lean_closure_set(v___f_7391_, 6, v___f_7385_);
    v___x_7392_ = crate::leanh::lean_apply_4(
        v_toBind_7382_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_7389_,
        v___f_7391_,
    );
    return v___x_7392_;
}
pub unsafe fn l_Lake_ELogT_replayLog_x3f(
    mut v_n_7393_: *mut crate::leanh::LeanObject,
    mut v_m_7394_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_7395_: *mut crate::leanh::LeanObject,
    mut v_inst_7396_: *mut crate::leanh::LeanObject,
    mut v_logger_7397_: *mut crate::leanh::LeanObject,
    mut v_inst_7398_: *mut crate::leanh::LeanObject,
    mut v_self_7399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_7400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_7401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_7402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_7403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_7400_ = crate::leanh::lean_ctor_get(v_inst_7396_, 0);
    v_toBind_7401_ = crate::leanh::lean_ctor_get(v_inst_7396_, 1);
    crate::leanh::lean_inc(v_toBind_7401_);
    v_toPure_7402_ = crate::leanh::lean_ctor_get(v_toApplicative_7400_, 1);
    crate::leanh::lean_inc_n(v_toPure_7402_, 2);
    v_toSeqRight_7403_ = crate::leanh::lean_ctor_get(v_toApplicative_7400_, 4);
    crate::leanh::lean_inc(v_toSeqRight_7403_);
    v___f_7404_ = crate::leanh::lean_alloc_closure(
        l_Lake_Log_replay___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_7404_, 0, v_logger_7397_);
    v___x_7405_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_7406_ = l_Lake_Log_empty___closed__0;
    v___x_7407_ = crate::leanh::lean_apply_1(v_self_7399_, v___x_7406_);
    v___x_7408_ = crate::leanh::lean_apply_2(v_inst_7398_, crate::leanh::lean_box(0), v___x_7407_);
    v___f_7409_ = crate::leanh::lean_alloc_closure(
        l_Lake_ELogT_replayLog_x3f___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_7409_, 0, v_toPure_7402_);
    crate::leanh::lean_inc_ref(v___f_7404_);
    v___f_7410_ = crate::leanh::lean_alloc_closure(
        l_Lake_ELogT_replayLog_x3f___redArg___lam__1___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    crate::leanh::lean_closure_set(v___f_7410_, 0, v_toPure_7402_);
    crate::leanh::lean_closure_set(v___f_7410_, 1, v___x_7405_);
    crate::leanh::lean_closure_set(v___f_7410_, 2, v_toSeqRight_7403_);
    crate::leanh::lean_closure_set(v___f_7410_, 3, v_inst_7396_);
    crate::leanh::lean_closure_set(v___f_7410_, 4, v___f_7404_);
    crate::leanh::lean_closure_set(v___f_7410_, 5, v___f_7409_);
    crate::leanh::lean_closure_set(v___f_7410_, 6, v___f_7404_);
    v___x_7411_ = crate::leanh::lean_apply_4(
        v_toBind_7401_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_7408_,
        v___f_7410_,
    );
    return v___x_7411_;
}
pub unsafe fn l_Lake_ELogT_replayLog___redArg___lam__3(
    mut v_toPure_7412_: *mut crate::leanh::LeanObject,
    mut v_a_7413_: *mut crate::leanh::LeanObject,
    mut v_x_7414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7415_ = crate::leanh::lean_apply_2(v_toPure_7412_, crate::leanh::lean_box(0), v_a_7413_);
    return v___x_7415_;
}
pub unsafe fn l_Lake_ELogT_replayLog___redArg___lam__0(
    mut v_toPure_7416_: *mut crate::leanh::LeanObject,
    mut v___x_7417_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_7418_: *mut crate::leanh::LeanObject,
    mut v_toSeqRight_7419_: *mut crate::leanh::LeanObject,
    mut v_inst_7420_: *mut crate::leanh::LeanObject,
    mut v___f_7421_: *mut crate::leanh::LeanObject,
    mut v___f_7422_: *mut crate::leanh::LeanObject,
    mut v___f_7423_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_7424_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_7424_) == 0 {
        let mut v_a_7425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_7426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_7427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7430_: u8 = 0;
        crate::leanh::lean_dec(v___f_7423_);
        crate::leanh::lean_dec(v___f_7422_);
        v_a_7425_ = crate::leanh::lean_ctor_get(v_____do__lift_7424_, 0);
        crate::leanh::lean_inc(v_a_7425_);
        v_a_7426_ = crate::leanh::lean_ctor_get(v_____do__lift_7424_, 1);
        crate::leanh::lean_inc(v_a_7426_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_7424_, 2);
        v___f_7427_ = crate::leanh::lean_alloc_closure(
            l_Lake_ELogT_replayLog___redArg___lam__3 as *mut core::ffi::c_void,
            3,
            2,
        );
        crate::leanh::lean_closure_set(v___f_7427_, 0, v_toPure_7416_);
        crate::leanh::lean_closure_set(v___f_7427_, 1, v_a_7425_);
        v___x_7428_ = lean_array_get_size(v_a_7426_);
        v___x_7429_ = crate::leanh::lean_box(0);
        v___x_7430_ = lean_nat_dec_lt(v___x_7417_, v___x_7428_);
        if v___x_7430_ == 0 {
            let mut v_toPure_7431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_a_7426_);
            crate::leanh::lean_dec(v___f_7421_);
            crate::leanh::lean_dec_ref(v_inst_7420_);
            v_toPure_7431_ = crate::leanh::lean_ctor_get(v_toApplicative_7418_, 1);
            crate::leanh::lean_inc(v_toPure_7431_);
            crate::leanh::lean_dec_ref(v_toApplicative_7418_);
            v___x_7432_ =
                crate::leanh::lean_apply_2(v_toPure_7431_, crate::leanh::lean_box(0), v___x_7429_);
            v___x_7433_ = crate::leanh::lean_apply_4(
                v_toSeqRight_7419_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_7432_,
                v___f_7427_,
            );
            return v___x_7433_;
        } else {
            let mut v___x_7434_: u8 = 0;
            v___x_7434_ = lean_nat_dec_le(v___x_7428_, v___x_7428_);
            if v___x_7434_ == 0 {
                if v___x_7430_ == 0 {
                    let mut v_toPure_7435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_7436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_7437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_a_7426_);
                    crate::leanh::lean_dec(v___f_7421_);
                    crate::leanh::lean_dec_ref(v_inst_7420_);
                    v_toPure_7435_ = crate::leanh::lean_ctor_get(v_toApplicative_7418_, 1);
                    crate::leanh::lean_inc(v_toPure_7435_);
                    crate::leanh::lean_dec_ref(v_toApplicative_7418_);
                    v___x_7436_ = crate::leanh::lean_apply_2(
                        v_toPure_7435_,
                        crate::leanh::lean_box(0),
                        v___x_7429_,
                    );
                    v___x_7437_ = crate::leanh::lean_apply_4(
                        v_toSeqRight_7419_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_7436_,
                        v___f_7427_,
                    );
                    return v___x_7437_;
                } else {
                    let mut v___x_7438_: usize = 0;
                    let mut v___x_7439_: usize = 0;
                    let mut v___x_7440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_7441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec_ref(v_toApplicative_7418_);
                    v___x_7438_ = 0usize;
                    v___x_7439_ = lean_usize_of_nat(v___x_7428_);
                    v___x_7440_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v_inst_7420_,
                        v___f_7421_,
                        v_a_7426_,
                        v___x_7438_,
                        v___x_7439_,
                        v___x_7429_,
                    );
                    v___x_7441_ = crate::leanh::lean_apply_4(
                        v_toSeqRight_7419_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_7440_,
                        v___f_7427_,
                    );
                    return v___x_7441_;
                }
            } else {
                let mut v___x_7442_: usize = 0;
                let mut v___x_7443_: usize = 0;
                let mut v___x_7444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_7445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v_toApplicative_7418_);
                v___x_7442_ = 0usize;
                v___x_7443_ = lean_usize_of_nat(v___x_7428_);
                v___x_7444_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v_inst_7420_,
                    v___f_7421_,
                    v_a_7426_,
                    v___x_7442_,
                    v___x_7443_,
                    v___x_7429_,
                );
                v___x_7445_ = crate::leanh::lean_apply_4(
                    v_toSeqRight_7419_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_7444_,
                    v___f_7427_,
                );
                return v___x_7445_;
            }
        }
    } else {
        let mut v_a_7446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7449_: u8 = 0;
        crate::leanh::lean_dec(v___f_7421_);
        crate::leanh::lean_dec(v_toPure_7416_);
        v_a_7446_ = crate::leanh::lean_ctor_get(v_____do__lift_7424_, 1);
        crate::leanh::lean_inc(v_a_7446_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_7424_, 2);
        v___x_7447_ = lean_array_get_size(v_a_7446_);
        v___x_7448_ = crate::leanh::lean_box(0);
        v___x_7449_ = lean_nat_dec_lt(v___x_7417_, v___x_7447_);
        if v___x_7449_ == 0 {
            let mut v_toPure_7450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_a_7446_);
            crate::leanh::lean_dec(v___f_7423_);
            crate::leanh::lean_dec_ref(v_inst_7420_);
            v_toPure_7450_ = crate::leanh::lean_ctor_get(v_toApplicative_7418_, 1);
            crate::leanh::lean_inc(v_toPure_7450_);
            crate::leanh::lean_dec_ref(v_toApplicative_7418_);
            v___x_7451_ =
                crate::leanh::lean_apply_2(v_toPure_7450_, crate::leanh::lean_box(0), v___x_7448_);
            v___x_7452_ = crate::leanh::lean_apply_4(
                v_toSeqRight_7419_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_7451_,
                v___f_7422_,
            );
            return v___x_7452_;
        } else {
            let mut v___x_7453_: u8 = 0;
            v___x_7453_ = lean_nat_dec_le(v___x_7447_, v___x_7447_);
            if v___x_7453_ == 0 {
                if v___x_7449_ == 0 {
                    let mut v_toPure_7454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_7455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_7456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_a_7446_);
                    crate::leanh::lean_dec(v___f_7423_);
                    crate::leanh::lean_dec_ref(v_inst_7420_);
                    v_toPure_7454_ = crate::leanh::lean_ctor_get(v_toApplicative_7418_, 1);
                    crate::leanh::lean_inc(v_toPure_7454_);
                    crate::leanh::lean_dec_ref(v_toApplicative_7418_);
                    v___x_7455_ = crate::leanh::lean_apply_2(
                        v_toPure_7454_,
                        crate::leanh::lean_box(0),
                        v___x_7448_,
                    );
                    v___x_7456_ = crate::leanh::lean_apply_4(
                        v_toSeqRight_7419_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_7455_,
                        v___f_7422_,
                    );
                    return v___x_7456_;
                } else {
                    let mut v___x_7457_: usize = 0;
                    let mut v___x_7458_: usize = 0;
                    let mut v___x_7459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_7460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec_ref(v_toApplicative_7418_);
                    v___x_7457_ = 0usize;
                    v___x_7458_ = lean_usize_of_nat(v___x_7447_);
                    v___x_7459_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v_inst_7420_,
                        v___f_7423_,
                        v_a_7446_,
                        v___x_7457_,
                        v___x_7458_,
                        v___x_7448_,
                    );
                    v___x_7460_ = crate::leanh::lean_apply_4(
                        v_toSeqRight_7419_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_7459_,
                        v___f_7422_,
                    );
                    return v___x_7460_;
                }
            } else {
                let mut v___x_7461_: usize = 0;
                let mut v___x_7462_: usize = 0;
                let mut v___x_7463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_7464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v_toApplicative_7418_);
                v___x_7461_ = 0usize;
                v___x_7462_ = lean_usize_of_nat(v___x_7447_);
                v___x_7463_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v_inst_7420_,
                    v___f_7423_,
                    v_a_7446_,
                    v___x_7461_,
                    v___x_7462_,
                    v___x_7448_,
                );
                v___x_7464_ = crate::leanh::lean_apply_4(
                    v_toSeqRight_7419_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_7463_,
                    v___f_7422_,
                );
                return v___x_7464_;
            }
        }
    }
}
pub unsafe fn l_Lake_ELogT_replayLog___redArg___lam__0___boxed(
    mut v_toPure_7465_: *mut crate::leanh::LeanObject,
    mut v___x_7466_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_7467_: *mut crate::leanh::LeanObject,
    mut v_toSeqRight_7468_: *mut crate::leanh::LeanObject,
    mut v_inst_7469_: *mut crate::leanh::LeanObject,
    mut v___f_7470_: *mut crate::leanh::LeanObject,
    mut v___f_7471_: *mut crate::leanh::LeanObject,
    mut v___f_7472_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_7473_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7474_ = l_Lake_ELogT_replayLog___redArg___lam__0(
        v_toPure_7465_,
        v___x_7466_,
        v_toApplicative_7467_,
        v_toSeqRight_7468_,
        v_inst_7469_,
        v___f_7470_,
        v___f_7471_,
        v___f_7472_,
        v_____do__lift_7473_,
    );
    crate::leanh::lean_dec(v___x_7466_);
    return v_res_7474_;
}
pub unsafe fn l_Lake_ELogT_replayLog___redArg(
    mut v_inst_7475_: *mut crate::leanh::LeanObject,
    mut v_inst_7476_: *mut crate::leanh::LeanObject,
    mut v_logger_7477_: *mut crate::leanh::LeanObject,
    mut v_inst_7478_: *mut crate::leanh::LeanObject,
    mut v_self_7479_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_7480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_7481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_7482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_failure_7483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_7484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_7485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_7480_ = crate::leanh::lean_ctor_get(v_inst_7475_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_7480_);
    v_toApplicative_7481_ = crate::leanh::lean_ctor_get(v_inst_7476_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_7481_);
    v_toBind_7482_ = crate::leanh::lean_ctor_get(v_inst_7476_, 1);
    crate::leanh::lean_inc(v_toBind_7482_);
    v_failure_7483_ = crate::leanh::lean_ctor_get(v_inst_7475_, 1);
    crate::leanh::lean_inc(v_failure_7483_);
    crate::leanh::lean_dec_ref(v_inst_7475_);
    v_toPure_7484_ = crate::leanh::lean_ctor_get(v_toApplicative_7480_, 1);
    crate::leanh::lean_inc(v_toPure_7484_);
    v_toSeqRight_7485_ = crate::leanh::lean_ctor_get(v_toApplicative_7480_, 4);
    crate::leanh::lean_inc(v_toSeqRight_7485_);
    crate::leanh::lean_dec_ref(v_toApplicative_7480_);
    v___f_7486_ = crate::leanh::lean_alloc_closure(
        l_Lake_Log_replay___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_7486_, 0, v_logger_7477_);
    v___f_7487_ = crate::leanh::lean_alloc_closure(
        l_Lake_MonadLog_error___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_7487_, 0, v_failure_7483_);
    v___x_7488_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_7489_ = l_Lake_Log_empty___closed__0;
    v___x_7490_ = crate::leanh::lean_apply_1(v_self_7479_, v___x_7489_);
    v___x_7491_ = crate::leanh::lean_apply_2(v_inst_7478_, crate::leanh::lean_box(0), v___x_7490_);
    crate::leanh::lean_inc_ref(v___f_7486_);
    v___f_7492_ = crate::leanh::lean_alloc_closure(
        l_Lake_ELogT_replayLog___redArg___lam__0___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    crate::leanh::lean_closure_set(v___f_7492_, 0, v_toPure_7484_);
    crate::leanh::lean_closure_set(v___f_7492_, 1, v___x_7488_);
    crate::leanh::lean_closure_set(v___f_7492_, 2, v_toApplicative_7481_);
    crate::leanh::lean_closure_set(v___f_7492_, 3, v_toSeqRight_7485_);
    crate::leanh::lean_closure_set(v___f_7492_, 4, v_inst_7476_);
    crate::leanh::lean_closure_set(v___f_7492_, 5, v___f_7486_);
    crate::leanh::lean_closure_set(v___f_7492_, 6, v___f_7487_);
    crate::leanh::lean_closure_set(v___f_7492_, 7, v___f_7486_);
    v___x_7493_ = crate::leanh::lean_apply_4(
        v_toBind_7482_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_7491_,
        v___f_7492_,
    );
    return v___x_7493_;
}
pub unsafe fn l_Lake_ELogT_replayLog(
    mut v_n_7494_: *mut crate::leanh::LeanObject,
    mut v_m_7495_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_7496_: *mut crate::leanh::LeanObject,
    mut v_inst_7497_: *mut crate::leanh::LeanObject,
    mut v_inst_7498_: *mut crate::leanh::LeanObject,
    mut v_logger_7499_: *mut crate::leanh::LeanObject,
    mut v_inst_7500_: *mut crate::leanh::LeanObject,
    mut v_self_7501_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_7502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_7503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_7504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_failure_7505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_7506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_7507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_7502_ = crate::leanh::lean_ctor_get(v_inst_7497_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_7502_);
    v_toApplicative_7503_ = crate::leanh::lean_ctor_get(v_inst_7498_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_7503_);
    v_toBind_7504_ = crate::leanh::lean_ctor_get(v_inst_7498_, 1);
    crate::leanh::lean_inc(v_toBind_7504_);
    v_failure_7505_ = crate::leanh::lean_ctor_get(v_inst_7497_, 1);
    crate::leanh::lean_inc(v_failure_7505_);
    crate::leanh::lean_dec_ref(v_inst_7497_);
    v_toPure_7506_ = crate::leanh::lean_ctor_get(v_toApplicative_7502_, 1);
    crate::leanh::lean_inc(v_toPure_7506_);
    v_toSeqRight_7507_ = crate::leanh::lean_ctor_get(v_toApplicative_7502_, 4);
    crate::leanh::lean_inc(v_toSeqRight_7507_);
    crate::leanh::lean_dec_ref(v_toApplicative_7502_);
    v___f_7508_ = crate::leanh::lean_alloc_closure(
        l_Lake_Log_replay___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_7508_, 0, v_logger_7499_);
    v___f_7509_ = crate::leanh::lean_alloc_closure(
        l_Lake_MonadLog_error___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_7509_, 0, v_failure_7505_);
    v___x_7510_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_7511_ = l_Lake_Log_empty___closed__0;
    v___x_7512_ = crate::leanh::lean_apply_1(v_self_7501_, v___x_7511_);
    v___x_7513_ = crate::leanh::lean_apply_2(v_inst_7500_, crate::leanh::lean_box(0), v___x_7512_);
    crate::leanh::lean_inc_ref(v___f_7508_);
    v___f_7514_ = crate::leanh::lean_alloc_closure(
        l_Lake_ELogT_replayLog___redArg___lam__0___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    crate::leanh::lean_closure_set(v___f_7514_, 0, v_toPure_7506_);
    crate::leanh::lean_closure_set(v___f_7514_, 1, v___x_7510_);
    crate::leanh::lean_closure_set(v___f_7514_, 2, v_toApplicative_7503_);
    crate::leanh::lean_closure_set(v___f_7514_, 3, v_toSeqRight_7507_);
    crate::leanh::lean_closure_set(v___f_7514_, 4, v_inst_7498_);
    crate::leanh::lean_closure_set(v___f_7514_, 5, v___f_7508_);
    crate::leanh::lean_closure_set(v___f_7514_, 6, v___f_7509_);
    crate::leanh::lean_closure_set(v___f_7514_, 7, v___f_7508_);
    v___x_7515_ = crate::leanh::lean_apply_4(
        v_toBind_7504_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_7513_,
        v___f_7514_,
    );
    return v___x_7515_;
}
pub unsafe fn l_Lake_LogConfig_getLogger___redArg___lam__0(
    mut v_val_7516_: *mut crate::leanh::LeanObject,
    mut v_outLv_7517_: u8,
    mut v_val_7518_: u8,
    mut v_inst_7519_: *mut crate::leanh::LeanObject,
    mut v_e_7520_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7521_ = crate::leanh::lean_box((v_outLv_7517_) as usize);
    v___x_7522_ = crate::leanh::lean_box((v_val_7518_) as usize);
    v___x_7523_ = crate::leanh::lean_alloc_closure(
        l_Lake_logToStream___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___x_7523_, 0, v_e_7520_);
    crate::leanh::lean_closure_set(v___x_7523_, 1, v_val_7516_);
    crate::leanh::lean_closure_set(v___x_7523_, 2, v___x_7521_);
    crate::leanh::lean_closure_set(v___x_7523_, 3, v___x_7522_);
    v___x_7524_ = crate::leanh::lean_apply_2(v_inst_7519_, crate::leanh::lean_box(0), v___x_7523_);
    return v___x_7524_;
}
pub unsafe fn l_Lake_LogConfig_getLogger___redArg___lam__0___boxed(
    mut v_val_7525_: *mut crate::leanh::LeanObject,
    mut v_outLv_7526_: *mut crate::leanh::LeanObject,
    mut v_val_7527_: *mut crate::leanh::LeanObject,
    mut v_inst_7528_: *mut crate::leanh::LeanObject,
    mut v_e_7529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_outLv_boxed_7530_: u8 = 0;
    let mut v_val_44__boxed_7531_: u8 = 0;
    let mut v_res_7532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_outLv_boxed_7530_ = (crate::leanh::lean_unbox(v_outLv_7526_) as u8);
    v_val_44__boxed_7531_ = (crate::leanh::lean_unbox(v_val_7527_) as u8);
    v_res_7532_ = l_Lake_LogConfig_getLogger___redArg___lam__0(
        v_val_7525_,
        v_outLv_boxed_7530_,
        v_val_44__boxed_7531_,
        v_inst_7528_,
        v_e_7529_,
    );
    return v_res_7532_;
}
pub unsafe fn l_Lake_LogConfig_getLogger___redArg(
    mut v_inst_7533_: *mut crate::leanh::LeanObject,
    mut v_self_7534_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_outLv_7536_: u8 = 0;
    let mut v_ansiMode_7537_: u8 = 0;
    let mut v_out_7538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7540_: u8 = 0;
    let mut v___x_7541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_outLv_7536_ = crate::leanh::lean_ctor_get_uint8(
        v_self_7534_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 1) as u32,
    );
    v_ansiMode_7537_ = crate::leanh::lean_ctor_get_uint8(
        v_self_7534_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 2) as u32,
    );
    v_out_7538_ = crate::leanh::lean_ctor_get(v_self_7534_, 0);
    v___x_7539_ = l_Lake_OutStream_get(v_out_7538_);
    crate::leanh::lean_inc_ref(v___x_7539_);
    v___x_7540_ = l_Lake_AnsiMode_isEnabled(v___x_7539_, v_ansiMode_7537_);
    v___x_7541_ = crate::leanh::lean_box((v_outLv_7536_) as usize);
    v___x_7542_ = crate::leanh::lean_box((v___x_7540_) as usize);
    v___f_7543_ = crate::leanh::lean_alloc_closure(
        l_Lake_LogConfig_getLogger___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_7543_, 0, v___x_7539_);
    crate::leanh::lean_closure_set(v___f_7543_, 1, v___x_7541_);
    crate::leanh::lean_closure_set(v___f_7543_, 2, v___x_7542_);
    crate::leanh::lean_closure_set(v___f_7543_, 3, v_inst_7533_);
    return v___f_7543_;
}
pub unsafe fn l_Lake_LogConfig_getLogger___redArg___boxed(
    mut v_inst_7544_: *mut crate::leanh::LeanObject,
    mut v_self_7545_: *mut crate::leanh::LeanObject,
    mut v_a_7546_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7547_ = l_Lake_LogConfig_getLogger___redArg(v_inst_7544_, v_self_7545_);
    crate::leanh::lean_dec_ref(v_self_7545_);
    return v_res_7547_;
}
pub unsafe fn l_Lake_LogConfig_getLogger(
    mut v_m_7548_: *mut crate::leanh::LeanObject,
    mut v_inst_7549_: *mut crate::leanh::LeanObject,
    mut v_self_7550_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_outLv_7552_: u8 = 0;
    let mut v_ansiMode_7553_: u8 = 0;
    let mut v_out_7554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7556_: u8 = 0;
    let mut v___x_7557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_outLv_7552_ = crate::leanh::lean_ctor_get_uint8(
        v_self_7550_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 1) as u32,
    );
    v_ansiMode_7553_ = crate::leanh::lean_ctor_get_uint8(
        v_self_7550_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 2) as u32,
    );
    v_out_7554_ = crate::leanh::lean_ctor_get(v_self_7550_, 0);
    v___x_7555_ = l_Lake_OutStream_get(v_out_7554_);
    crate::leanh::lean_inc_ref(v___x_7555_);
    v___x_7556_ = l_Lake_AnsiMode_isEnabled(v___x_7555_, v_ansiMode_7553_);
    v___x_7557_ = crate::leanh::lean_box((v_outLv_7552_) as usize);
    v___x_7558_ = crate::leanh::lean_box((v___x_7556_) as usize);
    v___f_7559_ = crate::leanh::lean_alloc_closure(
        l_Lake_LogConfig_getLogger___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_7559_, 0, v___x_7555_);
    crate::leanh::lean_closure_set(v___f_7559_, 1, v___x_7557_);
    crate::leanh::lean_closure_set(v___f_7559_, 2, v___x_7558_);
    crate::leanh::lean_closure_set(v___f_7559_, 3, v_inst_7549_);
    return v___f_7559_;
}
pub unsafe fn l_Lake_LogConfig_getLogger___boxed(
    mut v_m_7560_: *mut crate::leanh::LeanObject,
    mut v_inst_7561_: *mut crate::leanh::LeanObject,
    mut v_self_7562_: *mut crate::leanh::LeanObject,
    mut v_a_7563_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7564_ = l_Lake_LogConfig_getLogger(v_m_7560_, v_inst_7561_, v_self_7562_);
    crate::leanh::lean_dec_ref(v_self_7562_);
    return v_res_7564_;
}
pub unsafe fn l_Lake_LogIO_instMonadLiftIO___lam__0(
    mut v_00_u03b1_7565_: *mut crate::leanh::LeanObject,
    mut v___y_7566_: *mut crate::leanh::LeanObject,
    mut v___y_7567_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7569_ = crate::leanh::lean_apply_1(v___y_7566_, crate::leanh::lean_box(0));
    if crate::leanh::lean_obj_tag(v___x_7569_) == 0 {
        let mut v_a_7570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_7570_ = crate::leanh::lean_ctor_get(v___x_7569_, 0);
        crate::leanh::lean_inc(v_a_7570_);
        crate::leanh::lean_dec_ref_known(v___x_7569_, 1);
        v___x_7571_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_7571_, 0, v_a_7570_);
        crate::leanh::lean_ctor_set(v___x_7571_, 1, v___y_7567_);
        return v___x_7571_;
    } else {
        let mut v_a_7572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7574_: u8 = 0;
        let mut v___x_7575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_7572_ = crate::leanh::lean_ctor_get(v___x_7569_, 0);
        crate::leanh::lean_inc(v_a_7572_);
        crate::leanh::lean_dec_ref_known(v___x_7569_, 1);
        v___x_7573_ = lean_io_error_to_string(v_a_7572_);
        v___x_7574_ = 3;
        v___x_7575_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
        crate::leanh::lean_ctor_set(v___x_7575_, 0, v___x_7573_);
        crate::leanh::lean_ctor_set_uint8(
            v___x_7575_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
            v___x_7574_,
        );
        v___x_7576_ = lean_array_get_size(v___y_7567_);
        v___x_7577_ = lean_array_push(v___y_7567_, v___x_7575_);
        v___x_7578_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_7578_, 0, v___x_7576_);
        crate::leanh::lean_ctor_set(v___x_7578_, 1, v___x_7577_);
        return v___x_7578_;
    }
}
pub unsafe fn l_Lake_LogIO_instMonadLiftIO___lam__0___boxed(
    mut v_00_u03b1_7579_: *mut crate::leanh::LeanObject,
    mut v___y_7580_: *mut crate::leanh::LeanObject,
    mut v___y_7581_: *mut crate::leanh::LeanObject,
    mut v___y_7582_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7583_ = l_Lake_LogIO_instMonadLiftIO___lam__0(v_00_u03b1_7579_, v___y_7580_, v___y_7581_);
    return v_res_7583_;
}
pub unsafe fn l_Lake_LogIO_toBaseIO___redArg___lam__0(
    mut v_val_7586_: *mut crate::leanh::LeanObject,
    mut v___y_7587_: u8,
    mut v_val_7588_: u8,
    mut v_x_7589_: *mut crate::leanh::LeanObject,
    mut v___y_7590_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7592_ = l_Lake_logToStream(v___y_7590_, v_val_7586_, v___y_7587_, v_val_7588_);
    return v___x_7592_;
}
pub unsafe fn l_Lake_LogIO_toBaseIO___redArg___lam__0___boxed(
    mut v_val_7593_: *mut crate::leanh::LeanObject,
    mut v___y_7594_: *mut crate::leanh::LeanObject,
    mut v_val_7595_: *mut crate::leanh::LeanObject,
    mut v_x_7596_: *mut crate::leanh::LeanObject,
    mut v___y_7597_: *mut crate::leanh::LeanObject,
    mut v___y_7598_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_862__boxed_7599_: u8 = 0;
    let mut v_val_863__boxed_7600_: u8 = 0;
    let mut v_res_7601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_862__boxed_7599_ = (crate::leanh::lean_unbox(v___y_7594_) as u8);
    v_val_863__boxed_7600_ = (crate::leanh::lean_unbox(v_val_7595_) as u8);
    v_res_7601_ = l_Lake_LogIO_toBaseIO___redArg___lam__0(
        v_val_7593_,
        v___y_862__boxed_7599_,
        v_val_863__boxed_7600_,
        v_x_7596_,
        v___y_7597_,
    );
    crate::leanh::lean_dec_ref(v___y_7597_);
    return v_res_7601_;
}
pub unsafe fn l_Lake_LogIO_toBaseIO___redArg(
    mut v_self_7602_: *mut crate::leanh::LeanObject,
    mut v_cfg_7603_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_7606_: u8 = 0;
    let mut v___y_7607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7610_: u8 = 0;
    let mut v___y_7611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7615_: u8 = 0;
    let mut v___y_7616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7618_: u8 = 0;
    let mut v_ansiMode_7619_: u8 = 0;
    let mut v_out_7620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7622_: u8 = 0;
    let mut v___x_7623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7625_: u8 = 0;
    let mut v___x_7626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7630_: u8 = 0;
    let mut v___x_7631_: usize = 0;
    let mut v___x_7632_: usize = 0;
    let mut v___x_652__overap_7633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7635_: usize = 0;
    let mut v___x_7636_: usize = 0;
    let mut v___x_656__overap_7637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7642_: u8 = 0;
    let mut v___x_7643_: u8 = 0;
    let mut v___x_7644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_failLv_7648_: u8 = 0;
    let mut v_outLv_7649_: u8 = 0;
    let mut v___x_7650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7651_: u8 = 0;
    let mut v___x_7652_: u8 = 0;
    let mut v___x_7653_: u8 = 0;
    let mut v___x_7654_: u8 = 0;
    let mut v_a_7655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7657_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7613_ = l_instMonadBaseIO;
                v___x_7644_ = l_Lake_Log_empty___closed__0;
                v___x_7645_ = crate::leanh::lean_apply_2(
                    v_self_7602_,
                    v___x_7644_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_7645_) == 0 {
                    v_a_7646_ = crate::leanh::lean_ctor_get(v___x_7645_, 0);
                    crate::leanh::lean_inc(v_a_7646_);
                    v_a_7647_ = crate::leanh::lean_ctor_get(v___x_7645_, 1);
                    crate::leanh::lean_inc(v_a_7647_);
                    crate::leanh::lean_dec_ref_known(v___x_7645_, 2);
                    v_failLv_7648_ = crate::leanh::lean_ctor_get_uint8(
                        v_cfg_7603_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    v_outLv_7649_ = crate::leanh::lean_ctor_get_uint8(
                        v_cfg_7603_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 1) as u32,
                    );
                    v___x_7650_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7650_, 0, v_a_7646_);
                    v___x_7651_ = l_Lake_Log_maxLv(v_a_7647_);
                    v___x_7652_ = l_Lake_instOrdLogLevel_ord(v_failLv_7648_, v___x_7651_);
                    if v___x_7652_ == 2 {
                        v___x_7653_ = 0;
                        v___y_7615_ = v___x_7653_;
                        v___y_7616_ = v___x_7650_;
                        v___y_7617_ = v_a_7647_;
                        v___y_7618_ = v_outLv_7649_;
                        state = 3;
                        continue;
                    } else {
                        v___x_7654_ = 1;
                        v___y_7640_ = v_a_7647_;
                        v___y_7641_ = v___x_7650_;
                        v___y_7642_ = v___x_7654_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_7655_ = crate::leanh::lean_ctor_get(v___x_7645_, 1);
                    crate::leanh::lean_inc(v_a_7655_);
                    crate::leanh::lean_dec_ref_known(v___x_7645_, 2);
                    v___x_7656_ = crate::leanh::lean_box(0);
                    v___x_7657_ = 1;
                    v___y_7640_ = v_a_7655_;
                    v___y_7641_ = v___x_7656_;
                    v___y_7642_ = v___x_7657_;
                    state = 4;
                    continue;
                }
            }
            1 => {
                if v___y_7606_ == 0 {
                    return v___y_7607_;
                } else {
                    crate::leanh::lean_dec(v___y_7607_);
                    v___x_7608_ = crate::leanh::lean_box(0);
                    return v___x_7608_;
                }
            }
            2 => {
                v___y_7606_ = v___y_7610_;
                v___y_7607_ = v___y_7611_;
                state = 1;
                continue;
            }
            3 => {
                v_ansiMode_7619_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_7603_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 2) as u32,
                );
                v_out_7620_ = crate::leanh::lean_ctor_get(v_cfg_7603_, 0);
                v___x_7621_ = l_Lake_OutStream_get(v_out_7620_);
                crate::leanh::lean_inc_ref(v___x_7621_);
                v___x_7622_ = l_Lake_AnsiMode_isEnabled(v___x_7621_, v_ansiMode_7619_);
                v___x_7623_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_7624_ = lean_array_get_size(v___y_7617_);
                v___x_7625_ = lean_nat_dec_lt(v___x_7623_, v___x_7624_);
                if v___x_7625_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_7621_);
                    crate::leanh::lean_dec_ref(v___y_7617_);
                    v___y_7606_ = v___y_7615_;
                    v___y_7607_ = v___y_7616_;
                    state = 1;
                    continue;
                } else {
                    v___x_7626_ = crate::leanh::lean_box((v___y_7618_) as usize);
                    v___x_7627_ = crate::leanh::lean_box((v___x_7622_) as usize);
                    v___f_7628_ = crate::leanh::lean_alloc_closure(
                        l_Lake_LogIO_toBaseIO___redArg___lam__0___boxed as *mut core::ffi::c_void,
                        6,
                        3,
                    );
                    crate::leanh::lean_closure_set(v___f_7628_, 0, v___x_7621_);
                    crate::leanh::lean_closure_set(v___f_7628_, 1, v___x_7626_);
                    crate::leanh::lean_closure_set(v___f_7628_, 2, v___x_7627_);
                    v___x_7629_ = crate::leanh::lean_box(0);
                    v___x_7630_ = lean_nat_dec_le(v___x_7624_, v___x_7624_);
                    if v___x_7630_ == 0 {
                        if v___x_7625_ == 0 {
                            crate::leanh::lean_dec_ref(v___f_7628_);
                            crate::leanh::lean_dec_ref(v___y_7617_);
                            v___y_7606_ = v___y_7615_;
                            v___y_7607_ = v___y_7616_;
                            state = 1;
                            continue;
                        } else {
                            v___x_7631_ = 0usize;
                            v___x_7632_ = lean_usize_of_nat(v___x_7624_);
                            v___x_652__overap_7633_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    v___x_7613_,
                                    v___f_7628_,
                                    v___y_7617_,
                                    v___x_7631_,
                                    v___x_7632_,
                                    v___x_7629_,
                                );
                            v___x_7634_ = crate::leanh::lean_apply_1(
                                v___x_652__overap_7633_,
                                crate::leanh::lean_box(0),
                            );
                            v___y_7610_ = v___y_7615_;
                            v___y_7611_ = v___y_7616_;
                            v___y_7612_ = v___x_7634_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_7635_ = 0usize;
                        v___x_7636_ = lean_usize_of_nat(v___x_7624_);
                        v___x_656__overap_7637_ =
                            l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                crate::leanh::lean_box(0),
                                crate::leanh::lean_box(0),
                                crate::leanh::lean_box(0),
                                v___x_7613_,
                                v___f_7628_,
                                v___y_7617_,
                                v___x_7635_,
                                v___x_7636_,
                                v___x_7629_,
                            );
                        v___x_7638_ = crate::leanh::lean_apply_1(
                            v___x_656__overap_7637_,
                            crate::leanh::lean_box(0),
                        );
                        v___y_7610_ = v___y_7615_;
                        v___y_7611_ = v___y_7616_;
                        v___y_7612_ = v___x_7638_;
                        state = 2;
                        continue;
                    }
                }
            }
            4 => {
                v___x_7643_ = 0;
                v___y_7615_ = v___y_7642_;
                v___y_7616_ = v___y_7641_;
                v___y_7617_ = v___y_7640_;
                v___y_7618_ = v___x_7643_;
                state = 3;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LogIO_toBaseIO___redArg___boxed(
    mut v_self_7658_: *mut crate::leanh::LeanObject,
    mut v_cfg_7659_: *mut crate::leanh::LeanObject,
    mut v_a_7660_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7661_ = l_Lake_LogIO_toBaseIO___redArg(v_self_7658_, v_cfg_7659_);
    crate::leanh::lean_dec_ref(v_cfg_7659_);
    return v_res_7661_;
}
pub unsafe fn l_Lake_LogIO_toBaseIO(
    mut v_00_u03b1_7662_: *mut crate::leanh::LeanObject,
    mut v_self_7663_: *mut crate::leanh::LeanObject,
    mut v_cfg_7664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_7667_: u8 = 0;
    let mut v___y_7668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7671_: u8 = 0;
    let mut v___y_7672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7676_: u8 = 0;
    let mut v___y_7677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7679_: u8 = 0;
    let mut v_ansiMode_7680_: u8 = 0;
    let mut v_out_7681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7683_: u8 = 0;
    let mut v___x_7684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7686_: u8 = 0;
    let mut v___x_7687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7691_: u8 = 0;
    let mut v___x_7692_: usize = 0;
    let mut v___x_7693_: usize = 0;
    let mut v___x_791__overap_7694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7696_: usize = 0;
    let mut v___x_7697_: usize = 0;
    let mut v___x_794__overap_7698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7703_: u8 = 0;
    let mut v___x_7704_: u8 = 0;
    let mut v___x_7705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_failLv_7709_: u8 = 0;
    let mut v_outLv_7710_: u8 = 0;
    let mut v___x_7711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7712_: u8 = 0;
    let mut v___x_7713_: u8 = 0;
    let mut v___x_7714_: u8 = 0;
    let mut v___x_7715_: u8 = 0;
    let mut v_a_7716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7718_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7674_ = l_instMonadBaseIO;
                v___x_7705_ = l_Lake_Log_empty___closed__0;
                v___x_7706_ = crate::leanh::lean_apply_2(
                    v_self_7663_,
                    v___x_7705_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_7706_) == 0 {
                    v_a_7707_ = crate::leanh::lean_ctor_get(v___x_7706_, 0);
                    crate::leanh::lean_inc(v_a_7707_);
                    v_a_7708_ = crate::leanh::lean_ctor_get(v___x_7706_, 1);
                    crate::leanh::lean_inc(v_a_7708_);
                    crate::leanh::lean_dec_ref_known(v___x_7706_, 2);
                    v_failLv_7709_ = crate::leanh::lean_ctor_get_uint8(
                        v_cfg_7664_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    v_outLv_7710_ = crate::leanh::lean_ctor_get_uint8(
                        v_cfg_7664_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 1) as u32,
                    );
                    v___x_7711_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7711_, 0, v_a_7707_);
                    v___x_7712_ = l_Lake_Log_maxLv(v_a_7708_);
                    v___x_7713_ = l_Lake_instOrdLogLevel_ord(v_failLv_7709_, v___x_7712_);
                    if v___x_7713_ == 2 {
                        v___x_7714_ = 0;
                        v___y_7676_ = v___x_7714_;
                        v___y_7677_ = v___x_7711_;
                        v___y_7678_ = v_a_7708_;
                        v___y_7679_ = v_outLv_7710_;
                        state = 3;
                        continue;
                    } else {
                        v___x_7715_ = 1;
                        v___y_7701_ = v_a_7708_;
                        v___y_7702_ = v___x_7711_;
                        v___y_7703_ = v___x_7715_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_7716_ = crate::leanh::lean_ctor_get(v___x_7706_, 1);
                    crate::leanh::lean_inc(v_a_7716_);
                    crate::leanh::lean_dec_ref_known(v___x_7706_, 2);
                    v___x_7717_ = crate::leanh::lean_box(0);
                    v___x_7718_ = 1;
                    v___y_7701_ = v_a_7716_;
                    v___y_7702_ = v___x_7717_;
                    v___y_7703_ = v___x_7718_;
                    state = 4;
                    continue;
                }
            }
            1 => {
                if v___y_7667_ == 0 {
                    return v___y_7668_;
                } else {
                    crate::leanh::lean_dec(v___y_7668_);
                    v___x_7669_ = crate::leanh::lean_box(0);
                    return v___x_7669_;
                }
            }
            2 => {
                v___y_7667_ = v___y_7671_;
                v___y_7668_ = v___y_7672_;
                state = 1;
                continue;
            }
            3 => {
                v_ansiMode_7680_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_7664_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 2) as u32,
                );
                v_out_7681_ = crate::leanh::lean_ctor_get(v_cfg_7664_, 0);
                v___x_7682_ = l_Lake_OutStream_get(v_out_7681_);
                crate::leanh::lean_inc_ref(v___x_7682_);
                v___x_7683_ = l_Lake_AnsiMode_isEnabled(v___x_7682_, v_ansiMode_7680_);
                v___x_7684_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_7685_ = lean_array_get_size(v___y_7678_);
                v___x_7686_ = lean_nat_dec_lt(v___x_7684_, v___x_7685_);
                if v___x_7686_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_7682_);
                    crate::leanh::lean_dec_ref(v___y_7678_);
                    v___y_7667_ = v___y_7676_;
                    v___y_7668_ = v___y_7677_;
                    state = 1;
                    continue;
                } else {
                    v___x_7687_ = crate::leanh::lean_box((v___y_7679_) as usize);
                    v___x_7688_ = crate::leanh::lean_box((v___x_7683_) as usize);
                    v___f_7689_ = crate::leanh::lean_alloc_closure(
                        l_Lake_LogIO_toBaseIO___redArg___lam__0___boxed as *mut core::ffi::c_void,
                        6,
                        3,
                    );
                    crate::leanh::lean_closure_set(v___f_7689_, 0, v___x_7682_);
                    crate::leanh::lean_closure_set(v___f_7689_, 1, v___x_7687_);
                    crate::leanh::lean_closure_set(v___f_7689_, 2, v___x_7688_);
                    v___x_7690_ = crate::leanh::lean_box(0);
                    v___x_7691_ = lean_nat_dec_le(v___x_7685_, v___x_7685_);
                    if v___x_7691_ == 0 {
                        if v___x_7686_ == 0 {
                            crate::leanh::lean_dec_ref(v___f_7689_);
                            crate::leanh::lean_dec_ref(v___y_7678_);
                            v___y_7667_ = v___y_7676_;
                            v___y_7668_ = v___y_7677_;
                            state = 1;
                            continue;
                        } else {
                            v___x_7692_ = 0usize;
                            v___x_7693_ = lean_usize_of_nat(v___x_7685_);
                            v___x_791__overap_7694_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    v___x_7674_,
                                    v___f_7689_,
                                    v___y_7678_,
                                    v___x_7692_,
                                    v___x_7693_,
                                    v___x_7690_,
                                );
                            v___x_7695_ = crate::leanh::lean_apply_1(
                                v___x_791__overap_7694_,
                                crate::leanh::lean_box(0),
                            );
                            v___y_7671_ = v___y_7676_;
                            v___y_7672_ = v___y_7677_;
                            v___y_7673_ = v___x_7695_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_7696_ = 0usize;
                        v___x_7697_ = lean_usize_of_nat(v___x_7685_);
                        v___x_794__overap_7698_ =
                            l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                crate::leanh::lean_box(0),
                                crate::leanh::lean_box(0),
                                crate::leanh::lean_box(0),
                                v___x_7674_,
                                v___f_7689_,
                                v___y_7678_,
                                v___x_7696_,
                                v___x_7697_,
                                v___x_7690_,
                            );
                        v___x_7699_ = crate::leanh::lean_apply_1(
                            v___x_794__overap_7698_,
                            crate::leanh::lean_box(0),
                        );
                        v___y_7671_ = v___y_7676_;
                        v___y_7672_ = v___y_7677_;
                        v___y_7673_ = v___x_7699_;
                        state = 2;
                        continue;
                    }
                }
            }
            4 => {
                v___x_7704_ = 0;
                v___y_7676_ = v___y_7703_;
                v___y_7677_ = v___y_7702_;
                v___y_7678_ = v___y_7701_;
                v___y_7679_ = v___x_7704_;
                state = 3;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LogIO_toBaseIO___boxed(
    mut v_00_u03b1_7719_: *mut crate::leanh::LeanObject,
    mut v_self_7720_: *mut crate::leanh::LeanObject,
    mut v_cfg_7721_: *mut crate::leanh::LeanObject,
    mut v_a_7722_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7723_ = l_Lake_LogIO_toBaseIO(v_00_u03b1_7719_, v_self_7720_, v_cfg_7721_);
    crate::leanh::lean_dec_ref(v_cfg_7721_);
    return v_res_7723_;
}
pub unsafe fn l_Lake_LogIO_captureLog___redArg(
    mut v_inst_7724_: *mut crate::leanh::LeanObject,
    mut v_self_7725_: *mut crate::leanh::LeanObject,
    mut v_log_7726_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_7727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_7727_ = crate::leanh::lean_ctor_get(v_inst_7724_, 0);
    crate::leanh::lean_inc(v_map_7727_);
    crate::leanh::lean_dec_ref(v_inst_7724_);
    v___x_7728_ = l_Lake_ELogT_toLogT_x3f___redArg___closed__0;
    v___x_7729_ = crate::leanh::lean_apply_1(v_self_7725_, v_log_7726_);
    v___x_7730_ = crate::leanh::lean_apply_4(
        v_map_7727_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_7728_,
        v___x_7729_,
    );
    return v___x_7730_;
}
pub unsafe fn l_Lake_LogIO_captureLog(
    mut v_m_7731_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_7732_: *mut crate::leanh::LeanObject,
    mut v_inst_7733_: *mut crate::leanh::LeanObject,
    mut v_self_7734_: *mut crate::leanh::LeanObject,
    mut v_log_7735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_7736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_7736_ = crate::leanh::lean_ctor_get(v_inst_7733_, 0);
    crate::leanh::lean_inc(v_map_7736_);
    crate::leanh::lean_dec_ref(v_inst_7733_);
    v___x_7737_ = l_Lake_ELogT_toLogT_x3f___redArg___closed__0;
    v___x_7738_ = crate::leanh::lean_apply_1(v_self_7734_, v_log_7735_);
    v___x_7739_ = crate::leanh::lean_apply_4(
        v_map_7736_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_7737_,
        v___x_7738_,
    );
    return v___x_7739_;
}
pub unsafe fn l_Lake_LoggerIO_instMonadError___lam__0(
    mut v_00_u03b1_7740_: *mut crate::leanh::LeanObject,
    mut v___y_7741_: *mut crate::leanh::LeanObject,
    mut v___y_7742_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7744_: u8 = 0;
    let mut v___x_7745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7744_ = 3;
    v___x_7745_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_7745_, 0, v___y_7741_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_7745_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_7744_,
    );
    crate::leanh::lean_inc_ref(v___y_7742_);
    v___x_7746_ = crate::leanh::lean_apply_2(v___y_7742_, v___x_7745_, crate::leanh::lean_box(0));
    v___x_7747_ = crate::leanh::lean_box(0);
    v___x_7748_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_7748_, 0, v___x_7747_);
    return v___x_7748_;
}
pub unsafe fn l_Lake_LoggerIO_instMonadError___lam__0___boxed(
    mut v_00_u03b1_7749_: *mut crate::leanh::LeanObject,
    mut v___y_7750_: *mut crate::leanh::LeanObject,
    mut v___y_7751_: *mut crate::leanh::LeanObject,
    mut v___y_7752_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7753_ =
        l_Lake_LoggerIO_instMonadError___lam__0(v_00_u03b1_7749_, v___y_7750_, v___y_7751_);
    crate::leanh::lean_dec_ref(v___y_7751_);
    return v_res_7753_;
}
pub unsafe fn l_Lake_LoggerIO_instMonadLiftIO___lam__0(
    mut v_00_u03b1_7756_: *mut crate::leanh::LeanObject,
    mut v___y_7757_: *mut crate::leanh::LeanObject,
    mut v___y_7758_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7764_: u8 = 0;
    let mut v___x_7766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7768_: u8 = 0;
    let mut v_a_7769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7772_: u8 = 0;
    let mut v___x_7773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7774_: u8 = 0;
    let mut v___x_7775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7781_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7760_ = crate::leanh::lean_apply_1(v___y_7757_, crate::leanh::lean_box(0));
                if crate::leanh::lean_obj_tag(v___x_7760_) == 0 {
                    v_a_7761_ = crate::leanh::lean_ctor_get(v___x_7760_, 0);
                    v_isSharedCheck_7768_ = (!crate::leanh::lean_is_exclusive(v___x_7760_)) as u8;
                    if v_isSharedCheck_7768_ == 0 {
                        v___x_7763_ = v___x_7760_;
                        v_isShared_7764_ = v_isSharedCheck_7768_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7761_);
                        crate::leanh::lean_dec(v___x_7760_);
                        v___x_7763_ = crate::leanh::lean_box(0);
                        v_isShared_7764_ = v_isSharedCheck_7768_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7769_ = crate::leanh::lean_ctor_get(v___x_7760_, 0);
                    v_isSharedCheck_7781_ = (!crate::leanh::lean_is_exclusive(v___x_7760_)) as u8;
                    if v_isSharedCheck_7781_ == 0 {
                        v___x_7771_ = v___x_7760_;
                        v_isShared_7772_ = v_isSharedCheck_7781_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7769_);
                        crate::leanh::lean_dec(v___x_7760_);
                        v___x_7771_ = crate::leanh::lean_box(0);
                        v_isShared_7772_ = v_isSharedCheck_7781_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7764_ == 0 {
                    v___x_7766_ = v___x_7763_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7767_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7767_, 0, v_a_7761_);
                    v___x_7766_ = v_reuseFailAlloc_7767_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7766_;
            }
            3 => {
                v___x_7773_ = lean_io_error_to_string(v_a_7769_);
                v___x_7774_ = 3;
                v___x_7775_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_7775_, 0, v___x_7773_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_7775_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_7774_,
                );
                crate::leanh::lean_inc_ref(v___y_7758_);
                v___x_7776_ =
                    crate::leanh::lean_apply_2(v___y_7758_, v___x_7775_, crate::leanh::lean_box(0));
                v___x_7777_ = crate::leanh::lean_box(0);
                if v_isShared_7772_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7771_, 0, v___x_7777_);
                    v___x_7779_ = v___x_7771_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7780_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7780_, 0, v___x_7777_);
                    v___x_7779_ = v_reuseFailAlloc_7780_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7779_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LoggerIO_instMonadLiftIO___lam__0___boxed(
    mut v_00_u03b1_7782_: *mut crate::leanh::LeanObject,
    mut v___y_7783_: *mut crate::leanh::LeanObject,
    mut v___y_7784_: *mut crate::leanh::LeanObject,
    mut v___y_7785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7786_ =
        l_Lake_LoggerIO_instMonadLiftIO___lam__0(v_00_u03b1_7782_, v___y_7783_, v___y_7784_);
    crate::leanh::lean_dec_ref(v___y_7784_);
    return v_res_7786_;
}
pub unsafe fn l_Lake_LoggerIO_instMonadLiftLogIO___lam__0(
    mut v_x_7789_: *mut crate::leanh::LeanObject,
    mut v___y_7790_: *mut crate::leanh::LeanObject,
    mut v___y_7791_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v___y_7791_);
    v___x_7793_ = crate::leanh::lean_apply_2(v___y_7791_, v___y_7790_, crate::leanh::lean_box(0));
    v___x_7794_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_7794_, 0, v___x_7793_);
    return v___x_7794_;
}
pub unsafe fn l_Lake_LoggerIO_instMonadLiftLogIO___lam__0___boxed(
    mut v_x_7795_: *mut crate::leanh::LeanObject,
    mut v___y_7796_: *mut crate::leanh::LeanObject,
    mut v___y_7797_: *mut crate::leanh::LeanObject,
    mut v___y_7798_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7799_ = l_Lake_LoggerIO_instMonadLiftLogIO___lam__0(v_x_7795_, v___y_7796_, v___y_7797_);
    crate::leanh::lean_dec_ref(v___y_7797_);
    return v_res_7799_;
}
pub unsafe fn l_Lake_LoggerIO_instMonadLiftLogIO___lam__2(
    mut v___x_7800_: *mut crate::leanh::LeanObject,
    mut v___f_7801_: *mut crate::leanh::LeanObject,
    mut v___f_7802_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_7803_: *mut crate::leanh::LeanObject,
    mut v___y_7804_: *mut crate::leanh::LeanObject,
    mut v___y_7805_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7816_: u8 = 0;
    let mut v___x_7817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7819_: u8 = 0;
    let mut v___x_7820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7821_: usize = 0;
    let mut v___x_7822_: usize = 0;
    let mut v___x_1796__overap_7823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7827_: u8 = 0;
    let mut v___x_7829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7831_: u8 = 0;
    let mut v_unused_7832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7836_: u8 = 0;
    let mut v___x_7838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7840_: u8 = 0;
    let mut v___x_7841_: usize = 0;
    let mut v___x_7842_: usize = 0;
    let mut v___x_1805__overap_7843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7847_: u8 = 0;
    let mut v___x_7849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7851_: u8 = 0;
    let mut v_unused_7852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7856_: u8 = 0;
    let mut v___x_7858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7860_: u8 = 0;
    let mut v_a_7861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7863_: u8 = 0;
    let mut v___x_7864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7867_: u8 = 0;
    let mut v___x_7868_: usize = 0;
    let mut v___x_7869_: usize = 0;
    let mut v___x_1826__overap_7870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7875_: u8 = 0;
    let mut v___x_7877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7879_: u8 = 0;
    let mut v___x_7880_: usize = 0;
    let mut v___x_7881_: usize = 0;
    let mut v___x_1834__overap_7882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7887_: u8 = 0;
    let mut v___x_7889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7891_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7810_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_7811_ = l_Lake_Log_empty___closed__0;
                v___x_7812_ =
                    crate::leanh::lean_apply_2(v___y_7804_, v___x_7811_, crate::leanh::lean_box(0));
                if crate::leanh::lean_obj_tag(v___x_7812_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_7802_);
                    v_a_7813_ = crate::leanh::lean_ctor_get(v___x_7812_, 0);
                    crate::leanh::lean_inc(v_a_7813_);
                    v_a_7814_ = crate::leanh::lean_ctor_get(v___x_7812_, 1);
                    crate::leanh::lean_inc(v_a_7814_);
                    crate::leanh::lean_dec_ref_known(v___x_7812_, 2);
                    v___x_7815_ = lean_array_get_size(v_a_7814_);
                    v___x_7816_ = lean_nat_dec_lt(v___x_7810_, v___x_7815_);
                    if v___x_7816_ == 0 {
                        crate::leanh::lean_dec(v_a_7814_);
                        crate::leanh::lean_dec_ref(v___f_7801_);
                        crate::leanh::lean_dec_ref(v___x_7800_);
                        v___x_7817_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_7817_, 0, v_a_7813_);
                        return v___x_7817_;
                    } else {
                        v___x_7818_ = crate::leanh::lean_box(0);
                        v___x_7819_ = lean_nat_dec_le(v___x_7815_, v___x_7815_);
                        if v___x_7819_ == 0 {
                            if v___x_7816_ == 0 {
                                crate::leanh::lean_dec(v_a_7814_);
                                crate::leanh::lean_dec_ref(v___f_7801_);
                                crate::leanh::lean_dec_ref(v___x_7800_);
                                v___x_7820_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_7820_, 0, v_a_7813_);
                                return v___x_7820_;
                            } else {
                                v___x_7821_ = 0usize;
                                v___x_7822_ = lean_usize_of_nat(v___x_7815_);
                                v___x_1796__overap_7823_ =
                                    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                        crate::leanh::lean_box(0),
                                        crate::leanh::lean_box(0),
                                        crate::leanh::lean_box(0),
                                        v___x_7800_,
                                        v___f_7801_,
                                        v_a_7814_,
                                        v___x_7821_,
                                        v___x_7822_,
                                        v___x_7818_,
                                    );
                                crate::leanh::lean_inc_ref(v___y_7805_);
                                v___x_7824_ = crate::leanh::lean_apply_2(
                                    v___x_1796__overap_7823_,
                                    v___y_7805_,
                                    crate::leanh::lean_box(0),
                                );
                                if crate::leanh::lean_obj_tag(v___x_7824_) == 0 {
                                    v_isSharedCheck_7831_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_7824_)) as u8;
                                    if v_isSharedCheck_7831_ == 0 {
                                        v_unused_7832_ =
                                            crate::leanh::lean_ctor_get(v___x_7824_, 0);
                                        crate::leanh::lean_dec(v_unused_7832_);
                                        v___x_7826_ = v___x_7824_;
                                        v_isShared_7827_ = v_isSharedCheck_7831_;
                                        state = 2;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v___x_7824_);
                                        v___x_7826_ = crate::leanh::lean_box(0);
                                        v_isShared_7827_ = v_isSharedCheck_7831_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_7813_);
                                    v_a_7833_ = crate::leanh::lean_ctor_get(v___x_7824_, 0);
                                    v_isSharedCheck_7840_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_7824_)) as u8;
                                    if v_isSharedCheck_7840_ == 0 {
                                        v___x_7835_ = v___x_7824_;
                                        v_isShared_7836_ = v_isSharedCheck_7840_;
                                        state = 4;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_7833_);
                                        crate::leanh::lean_dec(v___x_7824_);
                                        v___x_7835_ = crate::leanh::lean_box(0);
                                        v_isShared_7836_ = v_isSharedCheck_7840_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            v___x_7841_ = 0usize;
                            v___x_7842_ = lean_usize_of_nat(v___x_7815_);
                            v___x_1805__overap_7843_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    v___x_7800_,
                                    v___f_7801_,
                                    v_a_7814_,
                                    v___x_7841_,
                                    v___x_7842_,
                                    v___x_7818_,
                                );
                            crate::leanh::lean_inc_ref(v___y_7805_);
                            v___x_7844_ = crate::leanh::lean_apply_2(
                                v___x_1805__overap_7843_,
                                v___y_7805_,
                                crate::leanh::lean_box(0),
                            );
                            if crate::leanh::lean_obj_tag(v___x_7844_) == 0 {
                                v_isSharedCheck_7851_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_7844_)) as u8;
                                if v_isSharedCheck_7851_ == 0 {
                                    v_unused_7852_ = crate::leanh::lean_ctor_get(v___x_7844_, 0);
                                    crate::leanh::lean_dec(v_unused_7852_);
                                    v___x_7846_ = v___x_7844_;
                                    v_isShared_7847_ = v_isSharedCheck_7851_;
                                    state = 6;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v___x_7844_);
                                    v___x_7846_ = crate::leanh::lean_box(0);
                                    v_isShared_7847_ = v_isSharedCheck_7851_;
                                    state = 6;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_7813_);
                                v_a_7853_ = crate::leanh::lean_ctor_get(v___x_7844_, 0);
                                v_isSharedCheck_7860_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_7844_)) as u8;
                                if v_isSharedCheck_7860_ == 0 {
                                    v___x_7855_ = v___x_7844_;
                                    v_isShared_7856_ = v_isSharedCheck_7860_;
                                    state = 8;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_7853_);
                                    crate::leanh::lean_dec(v___x_7844_);
                                    v___x_7855_ = crate::leanh::lean_box(0);
                                    v_isShared_7856_ = v_isSharedCheck_7860_;
                                    state = 8;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___f_7801_);
                    v_a_7861_ = crate::leanh::lean_ctor_get(v___x_7812_, 1);
                    crate::leanh::lean_inc(v_a_7861_);
                    crate::leanh::lean_dec_ref_known(v___x_7812_, 2);
                    v___x_7862_ = lean_array_get_size(v_a_7861_);
                    v___x_7863_ = lean_nat_dec_lt(v___x_7810_, v___x_7862_);
                    if v___x_7863_ == 0 {
                        crate::leanh::lean_dec(v_a_7861_);
                        crate::leanh::lean_dec_ref(v___f_7802_);
                        crate::leanh::lean_dec_ref(v___x_7800_);
                        v___x_7864_ = crate::leanh::lean_box(0);
                        v___x_7865_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_7865_, 0, v___x_7864_);
                        return v___x_7865_;
                    } else {
                        v___x_7866_ = crate::leanh::lean_box(0);
                        v___x_7867_ = lean_nat_dec_le(v___x_7862_, v___x_7862_);
                        if v___x_7867_ == 0 {
                            if v___x_7863_ == 0 {
                                crate::leanh::lean_dec(v_a_7861_);
                                crate::leanh::lean_dec_ref(v___f_7802_);
                                crate::leanh::lean_dec_ref(v___x_7800_);
                                state = 1;
                                continue;
                            } else {
                                v___x_7868_ = 0usize;
                                v___x_7869_ = lean_usize_of_nat(v___x_7862_);
                                v___x_1826__overap_7870_ =
                                    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                        crate::leanh::lean_box(0),
                                        crate::leanh::lean_box(0),
                                        crate::leanh::lean_box(0),
                                        v___x_7800_,
                                        v___f_7802_,
                                        v_a_7861_,
                                        v___x_7868_,
                                        v___x_7869_,
                                        v___x_7866_,
                                    );
                                crate::leanh::lean_inc_ref(v___y_7805_);
                                v___x_7871_ = crate::leanh::lean_apply_2(
                                    v___x_1826__overap_7870_,
                                    v___y_7805_,
                                    crate::leanh::lean_box(0),
                                );
                                if crate::leanh::lean_obj_tag(v___x_7871_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_7871_, 1);
                                    state = 1;
                                    continue;
                                } else {
                                    v_a_7872_ = crate::leanh::lean_ctor_get(v___x_7871_, 0);
                                    v_isSharedCheck_7879_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_7871_)) as u8;
                                    if v_isSharedCheck_7879_ == 0 {
                                        v___x_7874_ = v___x_7871_;
                                        v_isShared_7875_ = v_isSharedCheck_7879_;
                                        state = 10;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_7872_);
                                        crate::leanh::lean_dec(v___x_7871_);
                                        v___x_7874_ = crate::leanh::lean_box(0);
                                        v_isShared_7875_ = v_isSharedCheck_7879_;
                                        state = 10;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            v___x_7880_ = 0usize;
                            v___x_7881_ = lean_usize_of_nat(v___x_7862_);
                            v___x_1834__overap_7882_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    v___x_7800_,
                                    v___f_7802_,
                                    v_a_7861_,
                                    v___x_7880_,
                                    v___x_7881_,
                                    v___x_7866_,
                                );
                            crate::leanh::lean_inc_ref(v___y_7805_);
                            v___x_7883_ = crate::leanh::lean_apply_2(
                                v___x_1834__overap_7882_,
                                v___y_7805_,
                                crate::leanh::lean_box(0),
                            );
                            if crate::leanh::lean_obj_tag(v___x_7883_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_7883_, 1);
                                state = 1;
                                continue;
                            } else {
                                v_a_7884_ = crate::leanh::lean_ctor_get(v___x_7883_, 0);
                                v_isSharedCheck_7891_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_7883_)) as u8;
                                if v_isSharedCheck_7891_ == 0 {
                                    v___x_7886_ = v___x_7883_;
                                    v_isShared_7887_ = v_isSharedCheck_7891_;
                                    state = 12;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_7884_);
                                    crate::leanh::lean_dec(v___x_7883_);
                                    v___x_7886_ = crate::leanh::lean_box(0);
                                    v_isShared_7887_ = v_isSharedCheck_7891_;
                                    state = 12;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_7808_ = crate::leanh::lean_box(0);
                v___x_7809_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7809_, 0, v___x_7808_);
                return v___x_7809_;
            }
            2 => {
                if v_isShared_7827_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7826_, 0, v_a_7813_);
                    v___x_7829_ = v___x_7826_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7830_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7830_, 0, v_a_7813_);
                    v___x_7829_ = v_reuseFailAlloc_7830_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_7829_;
            }
            4 => {
                if v_isShared_7836_ == 0 {
                    v___x_7838_ = v___x_7835_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7839_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7839_, 0, v_a_7833_);
                    v___x_7838_ = v_reuseFailAlloc_7839_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_7838_;
            }
            6 => {
                if v_isShared_7847_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7846_, 0, v_a_7813_);
                    v___x_7849_ = v___x_7846_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7850_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7850_, 0, v_a_7813_);
                    v___x_7849_ = v_reuseFailAlloc_7850_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_7849_;
            }
            8 => {
                if v_isShared_7856_ == 0 {
                    v___x_7858_ = v___x_7855_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_7859_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7859_, 0, v_a_7853_);
                    v___x_7858_ = v_reuseFailAlloc_7859_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_7858_;
            }
            10 => {
                if v_isShared_7875_ == 0 {
                    v___x_7877_ = v___x_7874_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_7878_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7878_, 0, v_a_7872_);
                    v___x_7877_ = v_reuseFailAlloc_7878_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_7877_;
            }
            12 => {
                if v_isShared_7887_ == 0 {
                    v___x_7889_ = v___x_7886_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_7890_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7890_, 0, v_a_7884_);
                    v___x_7889_ = v_reuseFailAlloc_7890_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_7889_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LoggerIO_instMonadLiftLogIO___lam__2___boxed(
    mut v___x_7892_: *mut crate::leanh::LeanObject,
    mut v___f_7893_: *mut crate::leanh::LeanObject,
    mut v___f_7894_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_7895_: *mut crate::leanh::LeanObject,
    mut v___y_7896_: *mut crate::leanh::LeanObject,
    mut v___y_7897_: *mut crate::leanh::LeanObject,
    mut v___y_7898_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7899_ = l_Lake_LoggerIO_instMonadLiftLogIO___lam__2(
        v___x_7892_,
        v___f_7893_,
        v___f_7894_,
        v_00_u03b1_7895_,
        v___y_7896_,
        v___y_7897_,
    );
    crate::leanh::lean_dec_ref(v___y_7897_);
    return v_res_7899_;
}
pub unsafe fn _init_l_Lake_LoggerIO_instMonadLiftLogIO___closed__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_7901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7901_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_7901_;
}
pub unsafe fn _init_l_Lake_LoggerIO_instMonadLiftLogIO___closed__2() -> *mut crate::leanh::LeanObject
{
    let mut v___x_7902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7902_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LoggerIO_instMonadLiftLogIO___closed__1),
        core::ptr::addr_of_mut!(l_Lake_LoggerIO_instMonadLiftLogIO___closed__1_once),
        _init_l_Lake_LoggerIO_instMonadLiftLogIO___closed__1,
    );
    v___x_7903_ = l_ReaderT_instMonad___redArg(v___x_7902_);
    return v___x_7903_;
}
pub unsafe fn _init_l_Lake_LoggerIO_instMonadLiftLogIO___closed__3() -> *mut crate::leanh::LeanObject
{
    let mut v___f_7904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_7904_ = l_Lake_LoggerIO_instMonadLiftLogIO___closed__0;
    v___x_7905_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LoggerIO_instMonadLiftLogIO___closed__2),
        core::ptr::addr_of_mut!(l_Lake_LoggerIO_instMonadLiftLogIO___closed__2_once),
        _init_l_Lake_LoggerIO_instMonadLiftLogIO___closed__2,
    );
    v___f_7906_ = crate::leanh::lean_alloc_closure(
        l_Lake_LoggerIO_instMonadLiftLogIO___lam__2___boxed as *mut core::ffi::c_void,
        7,
        3,
    );
    crate::leanh::lean_closure_set(v___f_7906_, 0, v___x_7905_);
    crate::leanh::lean_closure_set(v___f_7906_, 1, v___f_7904_);
    crate::leanh::lean_closure_set(v___f_7906_, 2, v___f_7904_);
    return v___f_7906_;
}
pub unsafe fn _init_l_Lake_LoggerIO_instMonadLiftLogIO() -> *mut crate::leanh::LeanObject {
    let mut v___f_7907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_7907_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LoggerIO_instMonadLiftLogIO___closed__3),
        core::ptr::addr_of_mut!(l_Lake_LoggerIO_instMonadLiftLogIO___closed__3_once),
        _init_l_Lake_LoggerIO_instMonadLiftLogIO___closed__3,
    );
    return v___f_7907_;
}
pub unsafe fn l_Lake_LoggerIO_toBaseIO___redArg___lam__0(
    mut v_val_7908_: *mut crate::leanh::LeanObject,
    mut v_outLv_7909_: u8,
    mut v_val_7910_: u8,
    mut v_e_7911_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7913_ = l_Lake_logToStream(v_e_7911_, v_val_7908_, v_outLv_7909_, v_val_7910_);
    return v___x_7913_;
}
pub unsafe fn l_Lake_LoggerIO_toBaseIO___redArg___lam__0___boxed(
    mut v_val_7914_: *mut crate::leanh::LeanObject,
    mut v_outLv_7915_: *mut crate::leanh::LeanObject,
    mut v_val_7916_: *mut crate::leanh::LeanObject,
    mut v_e_7917_: *mut crate::leanh::LeanObject,
    mut v___y_7918_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_outLv_boxed_7919_: u8 = 0;
    let mut v_val_178__boxed_7920_: u8 = 0;
    let mut v_res_7921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_outLv_boxed_7919_ = (crate::leanh::lean_unbox(v_outLv_7915_) as u8);
    v_val_178__boxed_7920_ = (crate::leanh::lean_unbox(v_val_7916_) as u8);
    v_res_7921_ = l_Lake_LoggerIO_toBaseIO___redArg___lam__0(
        v_val_7914_,
        v_outLv_boxed_7919_,
        v_val_178__boxed_7920_,
        v_e_7917_,
    );
    crate::leanh::lean_dec_ref(v_e_7917_);
    return v_res_7921_;
}
pub unsafe fn l_Lake_LoggerIO_toBaseIO___redArg(
    mut v_self_7922_: *mut crate::leanh::LeanObject,
    mut v_cfg_7923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_outLv_7925_: u8 = 0;
    let mut v_ansiMode_7926_: u8 = 0;
    let mut v_out_7927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7929_: u8 = 0;
    let mut v___x_7930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7937_: u8 = 0;
    let mut v___x_7939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7941_: u8 = 0;
    let mut v___x_7942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_outLv_7925_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_7923_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 1) as u32,
                );
                v_ansiMode_7926_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_7923_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 2) as u32,
                );
                v_out_7927_ = crate::leanh::lean_ctor_get(v_cfg_7923_, 0);
                v___x_7928_ = l_Lake_OutStream_get(v_out_7927_);
                crate::leanh::lean_inc_ref(v___x_7928_);
                v___x_7929_ = l_Lake_AnsiMode_isEnabled(v___x_7928_, v_ansiMode_7926_);
                v___x_7930_ = crate::leanh::lean_box((v_outLv_7925_) as usize);
                v___x_7931_ = crate::leanh::lean_box((v___x_7929_) as usize);
                v___f_7932_ = crate::leanh::lean_alloc_closure(
                    l_Lake_LoggerIO_toBaseIO___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_7932_, 0, v___x_7928_);
                crate::leanh::lean_closure_set(v___f_7932_, 1, v___x_7930_);
                crate::leanh::lean_closure_set(v___f_7932_, 2, v___x_7931_);
                v___x_7933_ = crate::leanh::lean_apply_2(
                    v_self_7922_,
                    v___f_7932_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_7933_) == 0 {
                    v_a_7934_ = crate::leanh::lean_ctor_get(v___x_7933_, 0);
                    v_isSharedCheck_7941_ = (!crate::leanh::lean_is_exclusive(v___x_7933_)) as u8;
                    if v_isSharedCheck_7941_ == 0 {
                        v___x_7936_ = v___x_7933_;
                        v_isShared_7937_ = v_isSharedCheck_7941_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7934_);
                        crate::leanh::lean_dec(v___x_7933_);
                        v___x_7936_ = crate::leanh::lean_box(0);
                        v_isShared_7937_ = v_isSharedCheck_7941_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_7933_, 1);
                    v___x_7942_ = crate::leanh::lean_box(0);
                    return v___x_7942_;
                }
            }
            1 => {
                if v_isShared_7937_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_7936_, 1);
                    v___x_7939_ = v___x_7936_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7940_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7940_, 0, v_a_7934_);
                    v___x_7939_ = v_reuseFailAlloc_7940_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7939_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LoggerIO_toBaseIO___redArg___boxed(
    mut v_self_7943_: *mut crate::leanh::LeanObject,
    mut v_cfg_7944_: *mut crate::leanh::LeanObject,
    mut v_a_7945_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7946_ = l_Lake_LoggerIO_toBaseIO___redArg(v_self_7943_, v_cfg_7944_);
    crate::leanh::lean_dec_ref(v_cfg_7944_);
    return v_res_7946_;
}
pub unsafe fn l_Lake_LoggerIO_toBaseIO(
    mut v_00_u03b1_7947_: *mut crate::leanh::LeanObject,
    mut v_self_7948_: *mut crate::leanh::LeanObject,
    mut v_cfg_7949_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_outLv_7951_: u8 = 0;
    let mut v_ansiMode_7952_: u8 = 0;
    let mut v_out_7953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7955_: u8 = 0;
    let mut v___x_7956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7963_: u8 = 0;
    let mut v___x_7965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7967_: u8 = 0;
    let mut v___x_7968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_outLv_7951_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_7949_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 1) as u32,
                );
                v_ansiMode_7952_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_7949_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 2) as u32,
                );
                v_out_7953_ = crate::leanh::lean_ctor_get(v_cfg_7949_, 0);
                v___x_7954_ = l_Lake_OutStream_get(v_out_7953_);
                crate::leanh::lean_inc_ref(v___x_7954_);
                v___x_7955_ = l_Lake_AnsiMode_isEnabled(v___x_7954_, v_ansiMode_7952_);
                v___x_7956_ = crate::leanh::lean_box((v_outLv_7951_) as usize);
                v___x_7957_ = crate::leanh::lean_box((v___x_7955_) as usize);
                v___f_7958_ = crate::leanh::lean_alloc_closure(
                    l_Lake_LoggerIO_toBaseIO___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_7958_, 0, v___x_7954_);
                crate::leanh::lean_closure_set(v___f_7958_, 1, v___x_7956_);
                crate::leanh::lean_closure_set(v___f_7958_, 2, v___x_7957_);
                v___x_7959_ = crate::leanh::lean_apply_2(
                    v_self_7948_,
                    v___f_7958_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_7959_) == 0 {
                    v_a_7960_ = crate::leanh::lean_ctor_get(v___x_7959_, 0);
                    v_isSharedCheck_7967_ = (!crate::leanh::lean_is_exclusive(v___x_7959_)) as u8;
                    if v_isSharedCheck_7967_ == 0 {
                        v___x_7962_ = v___x_7959_;
                        v_isShared_7963_ = v_isSharedCheck_7967_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7960_);
                        crate::leanh::lean_dec(v___x_7959_);
                        v___x_7962_ = crate::leanh::lean_box(0);
                        v_isShared_7963_ = v_isSharedCheck_7967_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_7959_, 1);
                    v___x_7968_ = crate::leanh::lean_box(0);
                    return v___x_7968_;
                }
            }
            1 => {
                if v_isShared_7963_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_7962_, 1);
                    v___x_7965_ = v___x_7962_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7966_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7966_, 0, v_a_7960_);
                    v___x_7965_ = v_reuseFailAlloc_7966_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7965_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LoggerIO_toBaseIO___boxed(
    mut v_00_u03b1_7969_: *mut crate::leanh::LeanObject,
    mut v_self_7970_: *mut crate::leanh::LeanObject,
    mut v_cfg_7971_: *mut crate::leanh::LeanObject,
    mut v_a_7972_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7973_ = l_Lake_LoggerIO_toBaseIO(v_00_u03b1_7969_, v_self_7970_, v_cfg_7971_);
    crate::leanh::lean_dec_ref(v_cfg_7971_);
    return v_res_7973_;
}
pub unsafe fn l_Lake_LoggerIO_captureLog___redArg___lam__0(
    mut v_val_7974_: *mut crate::leanh::LeanObject,
    mut v_e_7975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7977_ = lean_st_ref_take(v_val_7974_);
    v___x_7978_ = lean_array_push(v___x_7977_, v_e_7975_);
    v___x_7979_ = lean_st_ref_set(v_val_7974_, v___x_7978_);
    return v___x_7979_;
}
pub unsafe fn l_Lake_LoggerIO_captureLog___redArg___lam__0___boxed(
    mut v_val_7980_: *mut crate::leanh::LeanObject,
    mut v_e_7981_: *mut crate::leanh::LeanObject,
    mut v___y_7982_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7983_ = l_Lake_LoggerIO_captureLog___redArg___lam__0(v_val_7980_, v_e_7981_);
    crate::leanh::lean_dec(v_val_7980_);
    return v_res_7983_;
}
pub unsafe fn l_Lake_LoggerIO_captureLog___redArg(
    mut v_self_7984_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_7987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7999_: u8 = 0;
    let mut v___x_8001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8003_: u8 = 0;
    let mut v___f_8004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8009_: u8 = 0;
    let mut v___x_8011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8013_: u8 = 0;
    let mut v_a_8014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8017_: u8 = 0;
    let mut v___x_8019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8021_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7990_ = l_Lake_Log_empty___closed__0;
                v___x_7991_ = lean_st_mk_ref(v___x_7990_);
                crate::leanh::lean_inc(v___x_7991_);
                v___f_8004_ = crate::leanh::lean_alloc_closure(
                    l_Lake_LoggerIO_captureLog___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    3,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_8004_, 0, v___x_7991_);
                v___x_8005_ = crate::leanh::lean_apply_2(
                    v_self_7984_,
                    v___f_8004_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_8005_) == 0 {
                    v_a_8006_ = crate::leanh::lean_ctor_get(v___x_8005_, 0);
                    v_isSharedCheck_8013_ = (!crate::leanh::lean_is_exclusive(v___x_8005_)) as u8;
                    if v_isSharedCheck_8013_ == 0 {
                        v___x_8008_ = v___x_8005_;
                        v_isShared_8009_ = v_isSharedCheck_8013_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_8006_);
                        crate::leanh::lean_dec(v___x_8005_);
                        v___x_8008_ = crate::leanh::lean_box(0);
                        v_isShared_8009_ = v_isSharedCheck_8013_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_a_8014_ = crate::leanh::lean_ctor_get(v___x_8005_, 0);
                    v_isSharedCheck_8021_ = (!crate::leanh::lean_is_exclusive(v___x_8005_)) as u8;
                    if v_isSharedCheck_8021_ == 0 {
                        v___x_8016_ = v___x_8005_;
                        v_isShared_8017_ = v_isSharedCheck_8021_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_8014_);
                        crate::leanh::lean_dec(v___x_8005_);
                        v___x_8016_ = crate::leanh::lean_box(0);
                        v_isShared_8017_ = v_isSharedCheck_8021_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7989_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7989_, 0, v___y_7988_);
                crate::leanh::lean_ctor_set(v___x_7989_, 1, v___y_7987_);
                return v___x_7989_;
            }
            2 => {
                v___x_7994_ = lean_st_ref_get(v___x_7991_);
                crate::leanh::lean_dec(v___x_7991_);
                if crate::leanh::lean_obj_tag(v_val_7993_) == 0 {
                    crate::leanh::lean_dec_ref_known(v_val_7993_, 1);
                    v___x_7995_ = crate::leanh::lean_box(0);
                    v___y_7987_ = v___x_7994_;
                    v___y_7988_ = v___x_7995_;
                    state = 1;
                    continue;
                } else {
                    v_a_7996_ = crate::leanh::lean_ctor_get(v_val_7993_, 0);
                    v_isSharedCheck_8003_ = (!crate::leanh::lean_is_exclusive(v_val_7993_)) as u8;
                    if v_isSharedCheck_8003_ == 0 {
                        v___x_7998_ = v_val_7993_;
                        v_isShared_7999_ = v_isSharedCheck_8003_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7996_);
                        crate::leanh::lean_dec(v_val_7993_);
                        v___x_7998_ = crate::leanh::lean_box(0);
                        v_isShared_7999_ = v_isSharedCheck_8003_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_7999_ == 0 {
                    v___x_8001_ = v___x_7998_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8002_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8002_, 0, v_a_7996_);
                    v___x_8001_ = v_reuseFailAlloc_8002_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___y_7987_ = v___x_7994_;
                v___y_7988_ = v___x_8001_;
                state = 1;
                continue;
            }
            5 => {
                if v_isShared_8009_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_8008_, 1);
                    v___x_8011_ = v___x_8008_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_8012_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8012_, 0, v_a_8006_);
                    v___x_8011_ = v_reuseFailAlloc_8012_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v_val_7993_ = v___x_8011_;
                state = 2;
                continue;
            }
            7 => {
                if v_isShared_8017_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_8016_, 0);
                    v___x_8019_ = v___x_8016_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_8020_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8020_, 0, v_a_8014_);
                    v___x_8019_ = v_reuseFailAlloc_8020_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v_val_7993_ = v___x_8019_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LoggerIO_captureLog___redArg___boxed(
    mut v_self_8022_: *mut crate::leanh::LeanObject,
    mut v_a_8023_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8024_ = l_Lake_LoggerIO_captureLog___redArg(v_self_8022_);
    return v_res_8024_;
}
pub unsafe fn l_Lake_LoggerIO_captureLog(
    mut v_00_u03b1_8025_: *mut crate::leanh::LeanObject,
    mut v_self_8026_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8028_ = l_Lake_LoggerIO_captureLog___redArg(v_self_8026_);
    return v___x_8028_;
}
pub unsafe fn l_Lake_LoggerIO_captureLog___boxed(
    mut v_00_u03b1_8029_: *mut crate::leanh::LeanObject,
    mut v_self_8030_: *mut crate::leanh::LeanObject,
    mut v_a_8031_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8032_ = l_Lake_LoggerIO_captureLog(v_00_u03b1_8029_, v_self_8030_);
    return v_res_8032_;
}
pub unsafe fn l_Lake_LoggerIO_run_x3f___redArg(
    mut v_self_8033_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8035_ = l_Lake_LoggerIO_captureLog___redArg(v_self_8033_);
    return v___x_8035_;
}
pub unsafe fn l_Lake_LoggerIO_run_x3f___redArg___boxed(
    mut v_self_8036_: *mut crate::leanh::LeanObject,
    mut v_a_8037_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8038_ = l_Lake_LoggerIO_run_x3f___redArg(v_self_8036_);
    return v_res_8038_;
}
pub unsafe fn l_Lake_LoggerIO_run_x3f(
    mut v_00_u03b1_8039_: *mut crate::leanh::LeanObject,
    mut v_self_8040_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8042_ = l_Lake_LoggerIO_captureLog___redArg(v_self_8040_);
    return v___x_8042_;
}
pub unsafe fn l_Lake_LoggerIO_run_x3f___boxed(
    mut v_00_u03b1_8043_: *mut crate::leanh::LeanObject,
    mut v_self_8044_: *mut crate::leanh::LeanObject,
    mut v_a_8045_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8046_ = l_Lake_LoggerIO_run_x3f(v_00_u03b1_8043_, v_self_8044_);
    return v_res_8046_;
}
pub unsafe fn l_Lake_LoggerIO_run_x3f_x27___redArg(
    mut v_self_8047_: *mut crate::leanh::LeanObject,
    mut v_logger_8048_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8054_: u8 = 0;
    let mut v___x_8056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8058_: u8 = 0;
    let mut v___x_8059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8050_ = crate::leanh::lean_apply_2(
                    v_self_8047_,
                    v_logger_8048_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_8050_) == 0 {
                    v_a_8051_ = crate::leanh::lean_ctor_get(v___x_8050_, 0);
                    v_isSharedCheck_8058_ = (!crate::leanh::lean_is_exclusive(v___x_8050_)) as u8;
                    if v_isSharedCheck_8058_ == 0 {
                        v___x_8053_ = v___x_8050_;
                        v_isShared_8054_ = v_isSharedCheck_8058_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_8051_);
                        crate::leanh::lean_dec(v___x_8050_);
                        v___x_8053_ = crate::leanh::lean_box(0);
                        v_isShared_8054_ = v_isSharedCheck_8058_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_8050_, 1);
                    v___x_8059_ = crate::leanh::lean_box(0);
                    return v___x_8059_;
                }
            }
            1 => {
                if v_isShared_8054_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_8053_, 1);
                    v___x_8056_ = v___x_8053_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8057_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8057_, 0, v_a_8051_);
                    v___x_8056_ = v_reuseFailAlloc_8057_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8056_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LoggerIO_run_x3f_x27___redArg___boxed(
    mut v_self_8060_: *mut crate::leanh::LeanObject,
    mut v_logger_8061_: *mut crate::leanh::LeanObject,
    mut v_a_8062_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8063_ = l_Lake_LoggerIO_run_x3f_x27___redArg(v_self_8060_, v_logger_8061_);
    return v_res_8063_;
}
pub unsafe fn l_Lake_LoggerIO_run_x3f_x27(
    mut v_00_u03b1_8064_: *mut crate::leanh::LeanObject,
    mut v_self_8065_: *mut crate::leanh::LeanObject,
    mut v_logger_8066_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8072_: u8 = 0;
    let mut v___x_8074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8076_: u8 = 0;
    let mut v___x_8077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8068_ = crate::leanh::lean_apply_2(
                    v_self_8065_,
                    v_logger_8066_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_8068_) == 0 {
                    v_a_8069_ = crate::leanh::lean_ctor_get(v___x_8068_, 0);
                    v_isSharedCheck_8076_ = (!crate::leanh::lean_is_exclusive(v___x_8068_)) as u8;
                    if v_isSharedCheck_8076_ == 0 {
                        v___x_8071_ = v___x_8068_;
                        v_isShared_8072_ = v_isSharedCheck_8076_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_8069_);
                        crate::leanh::lean_dec(v___x_8068_);
                        v___x_8071_ = crate::leanh::lean_box(0);
                        v_isShared_8072_ = v_isSharedCheck_8076_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_8068_, 1);
                    v___x_8077_ = crate::leanh::lean_box(0);
                    return v___x_8077_;
                }
            }
            1 => {
                if v_isShared_8072_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_8071_, 1);
                    v___x_8074_ = v___x_8071_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8075_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8075_, 0, v_a_8069_);
                    v___x_8074_ = v_reuseFailAlloc_8075_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8074_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LoggerIO_run_x3f_x27___boxed(
    mut v_00_u03b1_8078_: *mut crate::leanh::LeanObject,
    mut v_self_8079_: *mut crate::leanh::LeanObject,
    mut v_logger_8080_: *mut crate::leanh::LeanObject,
    mut v_a_8081_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8082_ = l_Lake_LoggerIO_run_x3f_x27(v_00_u03b1_8078_, v_self_8079_, v_logger_8080_);
    return v_res_8082_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Util_Log(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_Json(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Error(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_EStateT(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Message(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Lift(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Modify(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lake_instLTVerbosity = _init_l_Lake_instLTVerbosity();
    crate::leanh::lean_mark_persistent(l_Lake_instLTVerbosity);
    l_Lake_instLEVerbosity = _init_l_Lake_instLEVerbosity();
    crate::leanh::lean_mark_persistent(l_Lake_instLEVerbosity);
    l_Lake_instInhabitedVerbosity = _init_l_Lake_instInhabitedVerbosity();
    l_Lake_instInhabitedLogLevel_default = _init_l_Lake_instInhabitedLogLevel_default();
    l_Lake_instInhabitedLogLevel = _init_l_Lake_instInhabitedLogLevel();
    l_Lake_instLTLogLevel = _init_l_Lake_instLTLogLevel();
    crate::leanh::lean_mark_persistent(l_Lake_instLTLogLevel);
    l_Lake_instLELogLevel = _init_l_Lake_instLELogLevel();
    crate::leanh::lean_mark_persistent(l_Lake_instLELogLevel);
    l_Lake_Log_instInhabitedPos_default = _init_l_Lake_Log_instInhabitedPos_default();
    crate::leanh::lean_mark_persistent(l_Lake_Log_instInhabitedPos_default);
    l_Lake_Log_instInhabitedPos = _init_l_Lake_Log_instInhabitedPos();
    crate::leanh::lean_mark_persistent(l_Lake_Log_instInhabitedPos);
    l_Lake_instOfNatPos = _init_l_Lake_instOfNatPos();
    crate::leanh::lean_mark_persistent(l_Lake_instOfNatPos);
    l_Lake_instLTPos = _init_l_Lake_instLTPos();
    crate::leanh::lean_mark_persistent(l_Lake_instLTPos);
    l_Lake_instLEPos = _init_l_Lake_instLEPos();
    crate::leanh::lean_mark_persistent(l_Lake_instLEPos);
    l_Lake_LoggerIO_instMonadLiftLogIO = _init_l_Lake_LoggerIO_instMonadLiftLogIO();
    crate::leanh::lean_mark_persistent(l_Lake_LoggerIO_instMonadLiftLogIO);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Util_Log(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Util_Log(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_Json(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_Error(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_EStateT(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Message(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_Lift(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Modify(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Log(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Util_Log(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Util_Log(builtin);
}
