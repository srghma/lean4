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
    l_Array_extract___redArg, l_ByteArray_empty, l_Char_utf8Size, l_Lean_Name_mkStr1,
    l_Lean_Name_mkStr2, l_ReaderT_instMonad___redArg, l_panic___redArg,
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
    lean_array_get_size, lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub,
    lean_string_dec_eq, lean_string_from_utf8_unchecked, lean_string_utf8_byte_size,
    lean_uint32_dec_le, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::IO::{lean_get_stderr, lean_get_stdout};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_box, lean_box_uint32, lean_closure_set,
    lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_Lake_instReprVerbosity_repr___closed__0_value: LeanStringObject<21> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instReprVerbosity_repr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprVerbosity_repr___closed__0_value) as *mut LeanObject;
pub static l_Lake_instReprVerbosity_repr___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprVerbosity_repr___closed__0_value) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprVerbosity_repr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprVerbosity_repr___closed__1_value) as *mut LeanObject;
pub static l_Lake_instReprVerbosity_repr___closed__2_value: LeanStringObject<22> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instReprVerbosity_repr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprVerbosity_repr___closed__2_value) as *mut LeanObject;
pub static l_Lake_instReprVerbosity_repr___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprVerbosity_repr___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprVerbosity_repr___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprVerbosity_repr___closed__3_value) as *mut LeanObject;
pub static l_Lake_instReprVerbosity_repr___closed__4_value: LeanStringObject<23> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instReprVerbosity_repr___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprVerbosity_repr___closed__4_value) as *mut LeanObject;
pub static l_Lake_instReprVerbosity_repr___closed__5_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprVerbosity_repr___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprVerbosity_repr___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprVerbosity_repr___closed__5_value) as *mut LeanObject;
static mut l_Lake_instReprVerbosity_repr___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instReprVerbosity_repr___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_instReprVerbosity_repr___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instReprVerbosity_repr___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_instReprVerbosity___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_instReprVerbosity_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instReprVerbosity___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprVerbosity___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instReprVerbosity: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprVerbosity___closed__0_value) as *mut LeanObject;
pub static l_Lake_instOrdVerbosity___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_instOrdVerbosity_ord___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instOrdVerbosity___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instOrdVerbosity___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instOrdVerbosity: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instOrdVerbosity___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instLTVerbosity: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_instLEVerbosity: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_instMinVerbosity___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_instMinVerbosity___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instMinVerbosity___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instMinVerbosity___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instMinVerbosity: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instMinVerbosity___closed__0_value) as *mut LeanObject;
pub static l_Lake_instMaxVerbosity___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_instMaxVerbosity___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instMaxVerbosity___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instMaxVerbosity___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instMaxVerbosity: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instMaxVerbosity___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instInhabitedVerbosity: u8 = 0;
pub static l_Lake_instReprAnsiMode_repr___closed__0_value: LeanStringObject<19> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instReprAnsiMode_repr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprAnsiMode_repr___closed__0_value) as *mut LeanObject;
pub static l_Lake_instReprAnsiMode_repr___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprAnsiMode_repr___closed__0_value) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprAnsiMode_repr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprAnsiMode_repr___closed__1_value) as *mut LeanObject;
pub static l_Lake_instReprAnsiMode_repr___closed__2_value: LeanStringObject<19> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instReprAnsiMode_repr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprAnsiMode_repr___closed__2_value) as *mut LeanObject;
pub static l_Lake_instReprAnsiMode_repr___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprAnsiMode_repr___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprAnsiMode_repr___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprAnsiMode_repr___closed__3_value) as *mut LeanObject;
pub static l_Lake_instReprAnsiMode_repr___closed__4_value: LeanStringObject<21> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instReprAnsiMode_repr___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprAnsiMode_repr___closed__4_value) as *mut LeanObject;
pub static l_Lake_instReprAnsiMode_repr___closed__5_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprAnsiMode_repr___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprAnsiMode_repr___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprAnsiMode_repr___closed__5_value) as *mut LeanObject;
pub static l_Lake_instReprAnsiMode___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_instReprAnsiMode_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instReprAnsiMode___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprAnsiMode___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instReprAnsiMode: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprAnsiMode___closed__0_value) as *mut LeanObject;
pub static l_Lake_Ansi_chalk___closed__0_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_Ansi_chalk___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Ansi_chalk___closed__0_value) as *mut LeanObject;
pub static l_Lake_Ansi_chalk___closed__1_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_Ansi_chalk___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Ansi_chalk___closed__1_value) as *mut LeanObject;
pub static l_Lake_Ansi_chalk___closed__2_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_Ansi_chalk___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Ansi_chalk___closed__2_value) as *mut LeanObject;
pub static l_Lake_instCoeStreamOutStream___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_instCoeStreamOutStream___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instCoeStreamOutStream___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instCoeStreamOutStream___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instCoeStreamOutStream: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instCoeStreamOutStream___closed__0_value) as *mut LeanObject;
pub static l_Lake_instCoeHandleOutStream___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_instCoeHandleOutStream___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instCoeHandleOutStream___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instCoeHandleOutStream___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instCoeHandleOutStream: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instCoeHandleOutStream___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instInhabitedLogLevel_default: u8 = 0;
pub static mut l_Lake_instInhabitedLogLevel: u8 = 0;
pub static l_Lake_instReprLogLevel_repr___closed__0_value: LeanStringObject<20> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instReprLogLevel_repr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLogLevel_repr___closed__0_value) as *mut LeanObject;
pub static l_Lake_instReprLogLevel_repr___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprLogLevel_repr___closed__0_value) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprLogLevel_repr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLogLevel_repr___closed__1_value) as *mut LeanObject;
pub static l_Lake_instReprLogLevel_repr___closed__2_value: LeanStringObject<19> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instReprLogLevel_repr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLogLevel_repr___closed__2_value) as *mut LeanObject;
pub static l_Lake_instReprLogLevel_repr___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprLogLevel_repr___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprLogLevel_repr___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLogLevel_repr___closed__3_value) as *mut LeanObject;
pub static l_Lake_instReprLogLevel_repr___closed__4_value: LeanStringObject<22> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instReprLogLevel_repr___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLogLevel_repr___closed__4_value) as *mut LeanObject;
pub static l_Lake_instReprLogLevel_repr___closed__5_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprLogLevel_repr___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprLogLevel_repr___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLogLevel_repr___closed__5_value) as *mut LeanObject;
pub static l_Lake_instReprLogLevel_repr___closed__6_value: LeanStringObject<20> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instReprLogLevel_repr___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLogLevel_repr___closed__6_value) as *mut LeanObject;
pub static l_Lake_instReprLogLevel_repr___closed__7_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprLogLevel_repr___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprLogLevel_repr___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLogLevel_repr___closed__7_value) as *mut LeanObject;
pub static l_Lake_instReprLogLevel___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_instReprLogLevel_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instReprLogLevel___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLogLevel___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instReprLogLevel: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLogLevel___closed__0_value) as *mut LeanObject;
pub static l_Lake_instOrdLogLevel___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_instOrdLogLevel_ord___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instOrdLogLevel___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instOrdLogLevel___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instOrdLogLevel: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instOrdLogLevel___closed__0_value) as *mut LeanObject;
pub static l_Lake_instToJsonLogLevel_toJson___closed__0_value: LeanStringObject<6> =
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
        m_data: [116, 114, 97, 99, 101, 0],
    };
static mut l_Lake_instToJsonLogLevel_toJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instToJsonLogLevel_toJson___closed__0_value) as *mut LeanObject;
pub static l_Lake_instToJsonLogLevel_toJson___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instToJsonLogLevel_toJson___closed__0_value) as *mut LeanObject,
    ],
};
static mut l_Lake_instToJsonLogLevel_toJson___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instToJsonLogLevel_toJson___closed__1_value) as *mut LeanObject;
pub static l_Lake_instToJsonLogLevel_toJson___closed__2_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instToJsonLogLevel_toJson___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instToJsonLogLevel_toJson___closed__2_value) as *mut LeanObject;
pub static l_Lake_instToJsonLogLevel_toJson___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instToJsonLogLevel_toJson___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lake_instToJsonLogLevel_toJson___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instToJsonLogLevel_toJson___closed__3_value) as *mut LeanObject;
pub static l_Lake_instToJsonLogLevel_toJson___closed__4_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instToJsonLogLevel_toJson___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instToJsonLogLevel_toJson___closed__4_value) as *mut LeanObject;
pub static l_Lake_instToJsonLogLevel_toJson___closed__5_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instToJsonLogLevel_toJson___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lake_instToJsonLogLevel_toJson___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instToJsonLogLevel_toJson___closed__5_value) as *mut LeanObject;
pub static l_Lake_instToJsonLogLevel_toJson___closed__6_value: LeanStringObject<6> =
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
        m_data: [101, 114, 114, 111, 114, 0],
    };
static mut l_Lake_instToJsonLogLevel_toJson___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instToJsonLogLevel_toJson___closed__6_value) as *mut LeanObject;
pub static l_Lake_instToJsonLogLevel_toJson___closed__7_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instToJsonLogLevel_toJson___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lake_instToJsonLogLevel_toJson___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instToJsonLogLevel_toJson___closed__7_value) as *mut LeanObject;
pub static l_Lake_instToJsonLogLevel___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_instToJsonLogLevel_toJson___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instToJsonLogLevel___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instToJsonLogLevel___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instToJsonLogLevel: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instToJsonLogLevel___closed__0_value) as *mut LeanObject;
pub static l_Lake_instFromJsonLogLevel_fromJson___closed__0_value: LeanStringObject<23> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 23,
        m_capacity: 23,
        m_length: 22,
        m_data: [
            110, 111, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 116, 97, 103, 32, 102,
            111, 117, 110, 100, 0,
        ],
    };
static mut l_Lake_instFromJsonLogLevel_fromJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instFromJsonLogLevel_fromJson___closed__0_value) as *mut LeanObject;
pub static l_Lake_instFromJsonLogLevel_fromJson___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instFromJsonLogLevel_fromJson___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instFromJsonLogLevel_fromJson___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instFromJsonLogLevel_fromJson___closed__1_value) as *mut LeanObject;
pub static l_Lake_instFromJsonLogLevel_fromJson___closed__2_value: LeanStringObject<33> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 33,
        m_capacity: 33,
        m_length: 32,
        m_data: [
            110, 111, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 99, 111, 110, 115, 116,
            114, 117, 99, 116, 111, 114, 32, 109, 97, 116, 99, 104, 101, 100, 0,
        ],
    };
static mut l_Lake_instFromJsonLogLevel_fromJson___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instFromJsonLogLevel_fromJson___closed__2_value) as *mut LeanObject;
pub static l_Lake_instFromJsonLogLevel_fromJson___closed__3_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instFromJsonLogLevel_fromJson___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instFromJsonLogLevel_fromJson___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instFromJsonLogLevel_fromJson___closed__3_value) as *mut LeanObject;
pub static l_Lake_instFromJsonLogLevel_fromJson___closed__4_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((2 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lake_instFromJsonLogLevel_fromJson___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instFromJsonLogLevel_fromJson___closed__4_value) as *mut LeanObject;
pub static l_Lake_instFromJsonLogLevel_fromJson___closed__5_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((1 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lake_instFromJsonLogLevel_fromJson___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instFromJsonLogLevel_fromJson___closed__5_value) as *mut LeanObject;
pub static l_Lake_instFromJsonLogLevel_fromJson___closed__6_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lake_instFromJsonLogLevel_fromJson___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instFromJsonLogLevel_fromJson___closed__6_value) as *mut LeanObject;
pub static l_Lake_instFromJsonLogLevel_fromJson___closed__7_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((3 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lake_instFromJsonLogLevel_fromJson___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instFromJsonLogLevel_fromJson___closed__7_value) as *mut LeanObject;
pub static l_Lake_instFromJsonLogLevel___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_instFromJsonLogLevel_fromJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instFromJsonLogLevel___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instFromJsonLogLevel___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instFromJsonLogLevel: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instFromJsonLogLevel___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instLTLogLevel: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_instLELogLevel: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_instMinLogLevel___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_instMinLogLevel___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instMinLogLevel___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instMinLogLevel___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instMinLogLevel: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instMinLogLevel___closed__0_value) as *mut LeanObject;
pub static l_Lake_instMaxLogLevel___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_instMaxLogLevel___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instMaxLogLevel___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instMaxLogLevel___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instMaxLogLevel: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instMaxLogLevel___closed__0_value) as *mut LeanObject;
pub static l_Lake_LogLevel_ansiColor___closed__0_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_LogLevel_ansiColor___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LogLevel_ansiColor___closed__0_value) as *mut LeanObject;
pub static l_Lake_LogLevel_ansiColor___closed__1_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_LogLevel_ansiColor___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LogLevel_ansiColor___closed__1_value) as *mut LeanObject;
pub static l_Lake_LogLevel_ansiColor___closed__2_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_LogLevel_ansiColor___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LogLevel_ansiColor___closed__2_value) as *mut LeanObject;
pub static l_Lake_LogLevel_ofString_x3f___closed__0_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((1 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Lake_LogLevel_ofString_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LogLevel_ofString_x3f___closed__0_value) as *mut LeanObject;
pub static l_Lake_LogLevel_ofString_x3f___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((2 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Lake_LogLevel_ofString_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LogLevel_ofString_x3f___closed__1_value) as *mut LeanObject;
pub static l_Lake_LogLevel_ofString_x3f___closed__2_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_LogLevel_ofString_x3f___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LogLevel_ofString_x3f___closed__2_value) as *mut LeanObject;
pub static l_Lake_LogLevel_ofString_x3f___closed__3_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_LogLevel_ofString_x3f___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LogLevel_ofString_x3f___closed__3_value) as *mut LeanObject;
pub static l_Lake_LogLevel_ofString_x3f___closed__4_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((3 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Lake_LogLevel_ofString_x3f___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LogLevel_ofString_x3f___closed__4_value) as *mut LeanObject;
pub static l_Lake_LogLevel_ofString_x3f___closed__5_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Lake_LogLevel_ofString_x3f___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LogLevel_ofString_x3f___closed__5_value) as *mut LeanObject;
pub static l___private_Lake_Util_Log_0__Lake_instToStringLogLevel___closed__0_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_LogLevel_toString___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lake_Util_Log_0__Lake_instToStringLogLevel___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Util_Log_0__Lake_instToStringLogLevel___closed__0_value)
        as *mut LeanObject;
pub static mut l___private_Lake_Util_Log_0__Lake_instToStringLogLevel: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Util_Log_0__Lake_instToStringLogLevel___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_instInhabitedLogEntry_default___closed__0_value: LeanStringObject<1> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instInhabitedLogEntry_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedLogEntry_default___closed__0_value) as *mut LeanObject;
pub static l_Lake_instInhabitedLogEntry_default___closed__1_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instInhabitedLogEntry_default___closed__0_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lake_instInhabitedLogEntry_default___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedLogEntry_default___closed__1_value) as *mut LeanObject;
pub static mut l_Lake_instInhabitedLogEntry_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedLogEntry_default___closed__1_value) as *mut LeanObject;
pub static mut l_Lake_instInhabitedLogEntry: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedLogEntry_default___closed__1_value) as *mut LeanObject;
pub static l_Lake_instToJsonLogEntry_toJson___closed__0_value: LeanStringObject<6> =
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
        m_data: [108, 101, 118, 101, 108, 0],
    };
static mut l_Lake_instToJsonLogEntry_toJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instToJsonLogEntry_toJson___closed__0_value) as *mut LeanObject;
pub static l_Lake_instToJsonLogEntry_toJson___closed__1_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instToJsonLogEntry_toJson___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instToJsonLogEntry_toJson___closed__1_value) as *mut LeanObject;
pub static l_Lake_instToJsonLogEntry_toJson___closed__2_value: LeanArrayObject<0> =
    LeanArrayObject {
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
static mut l_Lake_instToJsonLogEntry_toJson___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instToJsonLogEntry_toJson___closed__2_value) as *mut LeanObject;
pub static l_Lake_instToJsonLogEntry___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_instToJsonLogEntry_toJson___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instToJsonLogEntry___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instToJsonLogEntry___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instToJsonLogEntry: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instToJsonLogEntry___closed__0_value) as *mut LeanObject;
pub static l_Lake_instFromJsonLogEntry_fromJson___closed__0_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instFromJsonLogEntry_fromJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instFromJsonLogEntry_fromJson___closed__0_value) as *mut LeanObject;
pub static l_Lake_instFromJsonLogEntry_fromJson___closed__1_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instFromJsonLogEntry_fromJson___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instFromJsonLogEntry_fromJson___closed__1_value) as *mut LeanObject;
static l_Lake_instFromJsonLogEntry_fromJson___closed__2_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_instFromJsonLogEntry_fromJson___closed__0_value)
                as *mut LeanObject,
            13012506173997729135 as *mut LeanObject,
        ],
    };
pub static l_Lake_instFromJsonLogEntry_fromJson___closed__2_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instFromJsonLogEntry_fromJson___closed__2_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_instFromJsonLogEntry_fromJson___closed__1_value)
                as *mut LeanObject,
            4218417399028539424 as *mut LeanObject,
        ],
    };
static mut l_Lake_instFromJsonLogEntry_fromJson___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instFromJsonLogEntry_fromJson___closed__2_value) as *mut LeanObject;
static mut l_Lake_instFromJsonLogEntry_fromJson___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instFromJsonLogEntry_fromJson___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instFromJsonLogEntry_fromJson___closed__4_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instFromJsonLogEntry_fromJson___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instFromJsonLogEntry_fromJson___closed__4_value) as *mut LeanObject;
static mut l_Lake_instFromJsonLogEntry_fromJson___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instFromJsonLogEntry_fromJson___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instFromJsonLogEntry_fromJson___closed__6_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_instToJsonLogEntry_toJson___closed__0_value)
                as *mut LeanObject,
            18250387975948097528 as *mut LeanObject,
        ],
    };
static mut l_Lake_instFromJsonLogEntry_fromJson___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instFromJsonLogEntry_fromJson___closed__6_value) as *mut LeanObject;
static mut l_Lake_instFromJsonLogEntry_fromJson___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instFromJsonLogEntry_fromJson___closed__7: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instFromJsonLogEntry_fromJson___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instFromJsonLogEntry_fromJson___closed__8: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instFromJsonLogEntry_fromJson___closed__9_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instFromJsonLogEntry_fromJson___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instFromJsonLogEntry_fromJson___closed__9_value) as *mut LeanObject;
static mut l_Lake_instFromJsonLogEntry_fromJson___closed__10_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instFromJsonLogEntry_fromJson___closed__10: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instFromJsonLogEntry_fromJson___closed__11_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_instToJsonLogEntry_toJson___closed__1_value)
                as *mut LeanObject,
            982637797389909653 as *mut LeanObject,
        ],
    };
static mut l_Lake_instFromJsonLogEntry_fromJson___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instFromJsonLogEntry_fromJson___closed__11_value) as *mut LeanObject;
static mut l_Lake_instFromJsonLogEntry_fromJson___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instFromJsonLogEntry_fromJson___closed__12: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instFromJsonLogEntry_fromJson___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instFromJsonLogEntry_fromJson___closed__13: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instFromJsonLogEntry_fromJson___closed__14_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instFromJsonLogEntry_fromJson___closed__14: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instFromJsonLogEntry___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_instFromJsonLogEntry_fromJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instFromJsonLogEntry___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instFromJsonLogEntry___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instFromJsonLogEntry: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instFromJsonLogEntry___closed__0_value) as *mut LeanObject;
pub static l_Lake_LogEntry_toString___closed__0_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_LogEntry_toString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LogEntry_toString___closed__0_value) as *mut LeanObject;
pub static l_Lake_LogEntry_toString___closed__1_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_LogEntry_toString___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LogEntry_toString___closed__1_value) as *mut LeanObject;
pub static l_Lake_instToStringLogEntry___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_instToStringLogEntry___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instToStringLogEntry___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instToStringLogEntry___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instToStringLogEntry: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instToStringLogEntry___closed__0_value) as *mut LeanObject;
pub static l_Lake_LogEntry_ofSerialMessage___closed__0_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_LogEntry_ofSerialMessage___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LogEntry_ofSerialMessage___closed__0_value) as *mut LeanObject;
pub static l_Lake_instInhabitedLog_default___closed__0_value: LeanArrayObject<0> =
    LeanArrayObject {
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
static mut l_Lake_instInhabitedLog_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedLog_default___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instInhabitedLog_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedLog_default___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instInhabitedLog: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedLog_default___closed__0_value) as *mut LeanObject;
pub static l_Lake_instToJsonLog___closed__0_value: LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_instToJsonLog___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(l_Lake_instToJsonLogEntry___closed__0_value) as *mut LeanObject],
};
static mut l_Lake_instToJsonLog___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instToJsonLog___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instToJsonLog: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instToJsonLog___closed__0_value) as *mut LeanObject;
pub static l_Lake_instFromJsonLog___closed__0_value: LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_instFromJsonLog___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(l_Lake_instFromJsonLogEntry___closed__0_value) as *mut LeanObject],
};
static mut l_Lake_instFromJsonLog___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instFromJsonLog___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instFromJsonLog: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instFromJsonLog___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_Log_instInhabitedPos_default: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Log_instInhabitedPos: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_instOfNatPos: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_instOrdPos___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_instOrdPos___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instOrdPos___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instOrdPos___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instOrdPos: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instOrdPos___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instLTPos: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_instLEPos: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_instMinPos___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_instMinPos___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instMinPos___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instMinPos___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instMinPos: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instMinPos___closed__0_value) as *mut LeanObject;
pub static l_Lake_instMaxPos___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_instMaxPos___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instMaxPos___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instMaxPos___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instMaxPos: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instMaxPos___closed__0_value) as *mut LeanObject;
pub static l_Lake_Log_empty___closed__0_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Lake_Log_empty___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Log_empty___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_Log_empty: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Log_empty___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_Log_instEmptyCollection: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Log_empty___closed__0_value) as *mut LeanObject;
pub static l_Lake_Log_instAppend___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_Log_append___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_Log_instAppend___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Log_instAppend___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_Log_instAppend: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Log_instAppend___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_toString_spec__0___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [10, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_toString_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_toString_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Lake_Log_instToString___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_Log_toString___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_Log_instToString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Log_instToString___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_Log_instToString: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Log_instToString___closed__0_value) as *mut LeanObject;
pub static l_Lake_Log_filter___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
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
static mut l_Lake_Log_filter___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Log_filter___closed__0_value) as *mut LeanObject;
pub static l_Lake_Log_filter___closed__1_value: LeanClosureObject<0> = LeanClosureObject {
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
static mut l_Lake_Log_filter___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Log_filter___closed__1_value) as *mut LeanObject;
pub static l_Lake_Log_filter___closed__2_value: LeanClosureObject<0> = LeanClosureObject {
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
static mut l_Lake_Log_filter___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Log_filter___closed__2_value) as *mut LeanObject;
pub static l_Lake_Log_filter___closed__3_value: LeanClosureObject<0> = LeanClosureObject {
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
static mut l_Lake_Log_filter___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Log_filter___closed__3_value) as *mut LeanObject;
pub static l_Lake_Log_filter___closed__4_value: LeanClosureObject<0> = LeanClosureObject {
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
static mut l_Lake_Log_filter___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Log_filter___closed__4_value) as *mut LeanObject;
pub static l_Lake_Log_filter___closed__5_value: LeanClosureObject<0> = LeanClosureObject {
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
static mut l_Lake_Log_filter___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Log_filter___closed__5_value) as *mut LeanObject;
pub static l_Lake_Log_filter___closed__6_value: LeanClosureObject<0> = LeanClosureObject {
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
static mut l_Lake_Log_filter___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Log_filter___closed__6_value) as *mut LeanObject;
pub static l_Lake_Log_filter___closed__7_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Log_filter___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Log_filter___closed__1_value) as *mut LeanObject,
    ],
};
static mut l_Lake_Log_filter___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Log_filter___closed__7_value) as *mut LeanObject;
pub static l_Lake_Log_filter___closed__8_value: LeanCtorObject<5> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Log_filter___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Log_filter___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Log_filter___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Log_filter___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Log_filter___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lake_Log_filter___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Log_filter___closed__8_value) as *mut LeanObject;
pub static l_Lake_Log_filter___closed__9_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Log_filter___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Log_filter___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lake_Log_filter___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Log_filter___closed__9_value) as *mut LeanObject;
pub static l_Lake_getLogPos___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_getLogPos___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_getLogPos___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_getLogPos___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lake_takeLog___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_takeLog___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_takeLog___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_takeLog___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lake_withLoggedIO___redArg___lam__3___closed__0_value: LeanStringObject<16> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_withLoggedIO___redArg___lam__3___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_withLoggedIO___redArg___lam__3___closed__0_value) as *mut LeanObject;
pub static l_Lake_withLoggedIO___redArg___lam__3___closed__1_value: LeanStringObject<23> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_withLoggedIO___redArg___lam__3___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_withLoggedIO___redArg___lam__3___closed__1_value) as *mut LeanObject;
pub static l_Lake_withLoggedIO___redArg___lam__3___closed__2_value: LeanStringObject<17> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_withLoggedIO___redArg___lam__3___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_withLoggedIO___redArg___lam__3___closed__2_value) as *mut LeanObject;
pub static l_Lake_withLoggedIO___redArg___lam__3___closed__3_value: LeanStringObject<21> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_withLoggedIO___redArg___lam__3___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_withLoggedIO___redArg___lam__3___closed__3_value) as *mut LeanObject;
static mut l_Lake_withLoggedIO___redArg___lam__3___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_withLoggedIO___redArg___lam__3___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_withLoggedIO___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_withLoggedIO___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_withLoggedIO___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_withLoggedIO___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lake_withLoggedIO___redArg___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_withLoggedIO___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_withLoggedIO___redArg___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_withLoggedIO___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_LogT_run_x27___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_LogT_run_x27___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LogT_run_x27___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LogT_run_x27___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lake_instMonadErrorELogTOfMonad___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_instMonadErrorELogTOfMonad___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instMonadErrorELogTOfMonad___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadErrorELogTOfMonad___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_ELogT_run_x27___redArg___closed__0_value: LeanClosureObject<3> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 3) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_EResult_toExcept___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 3,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lake_ELogT_run_x27___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ELogT_run_x27___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lake_ELogT_toLogT___redArg___closed__0_value: LeanClosureObject<3> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 3) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_EResult_toProd as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 3,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lake_ELogT_toLogT___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ELogT_toLogT___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lake_ELogT_toLogT_x3f___redArg___closed__0_value: LeanClosureObject<3> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 3) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_EResult_toProd_x3f as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 3,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lake_ELogT_toLogT_x3f___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ELogT_toLogT_x3f___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lake_ELogT_run_x3f_x27___redArg___closed__0_value: LeanClosureObject<3> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 3) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_EResult_result_x3f___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 3,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lake_ELogT_run_x3f_x27___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ELogT_run_x3f_x27___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lake_LogIO_instMonadLiftIO___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_LogIO_instMonadLiftIO___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LogIO_instMonadLiftIO___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LogIO_instMonadLiftIO___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_LogIO_instMonadLiftIO: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LogIO_instMonadLiftIO___closed__0_value) as *mut LeanObject;
pub static l_Lake_LoggerIO_instMonadError___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_LoggerIO_instMonadError___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LoggerIO_instMonadError___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LoggerIO_instMonadError___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_LoggerIO_instMonadError: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LoggerIO_instMonadError___closed__0_value) as *mut LeanObject;
pub static l_Lake_LoggerIO_instMonadLiftIO___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_LoggerIO_instMonadLiftIO___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LoggerIO_instMonadLiftIO___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LoggerIO_instMonadLiftIO___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_LoggerIO_instMonadLiftIO: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LoggerIO_instMonadLiftIO___closed__0_value) as *mut LeanObject;
pub static l_Lake_LoggerIO_instMonadLiftLogIO___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_LoggerIO_instMonadLiftLogIO___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LoggerIO_instMonadLiftLogIO___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LoggerIO_instMonadLiftLogIO___closed__0_value) as *mut LeanObject;
static mut l_Lake_LoggerIO_instMonadLiftLogIO___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_LoggerIO_instMonadLiftLogIO___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_LoggerIO_instMonadLiftLogIO___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_LoggerIO_instMonadLiftLogIO___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_LoggerIO_instMonadLiftLogIO___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_LoggerIO_instMonadLiftLogIO___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_LoggerIO_instMonadLiftLogIO: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lake_Verbosity_ctorIdx(mut v_x_4042_: u8) -> *mut LeanObject {
    match v_x_4042_ {
        0 => {
            let mut v___x_4043_: *mut LeanObject = core::ptr::null_mut();
            v___x_4043_ = lean_unsigned_to_nat(0);
            return v___x_4043_;
        }
        1 => {
            let mut v___x_4044_: *mut LeanObject = core::ptr::null_mut();
            v___x_4044_ = lean_unsigned_to_nat(1);
            return v___x_4044_;
        }
        _ => {
            let mut v___x_4045_: *mut LeanObject = core::ptr::null_mut();
            v___x_4045_ = lean_unsigned_to_nat(2);
            return v___x_4045_;
        }
    }
}
pub unsafe fn l_Lake_Verbosity_ctorIdx___boxed(mut v_x_4046_: *mut LeanObject) -> *mut LeanObject {
    let mut v_x_boxed_4047_: u8 = 0;
    let mut v_res_4048_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_4047_ = (lean_unbox(v_x_4046_) as u8);
    v_res_4048_ = l_Lake_Verbosity_ctorIdx(v_x_boxed_4047_);
    return v_res_4048_;
}
pub unsafe fn l_Lake_Verbosity_toCtorIdx(mut v_x_4049_: u8) -> *mut LeanObject {
    let mut v___x_4050_: *mut LeanObject = core::ptr::null_mut();
    v___x_4050_ = l_Lake_Verbosity_ctorIdx(v_x_4049_);
    return v___x_4050_;
}
pub unsafe fn l_Lake_Verbosity_toCtorIdx___boxed(
    mut v_x_4051_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4__boxed_4052_: u8 = 0;
    let mut v_res_4053_: *mut LeanObject = core::ptr::null_mut();
    v_x_4__boxed_4052_ = (lean_unbox(v_x_4051_) as u8);
    v_res_4053_ = l_Lake_Verbosity_toCtorIdx(v_x_4__boxed_4052_);
    return v_res_4053_;
}
pub unsafe fn l_Lake_Verbosity_ctorElim___redArg(
    mut v_k_4054_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_4054_);
    return v_k_4054_;
}
pub unsafe fn l_Lake_Verbosity_ctorElim___redArg___boxed(
    mut v_k_4055_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4056_: *mut LeanObject = core::ptr::null_mut();
    v_res_4056_ = l_Lake_Verbosity_ctorElim___redArg(v_k_4055_);
    lean_dec(v_k_4055_);
    return v_res_4056_;
}
pub unsafe fn l_Lake_Verbosity_ctorElim(
    mut v_motive_4057_: *mut LeanObject,
    mut v_ctorIdx_4058_: *mut LeanObject,
    mut v_t_4059_: u8,
    mut v_h_4060_: *mut LeanObject,
    mut v_k_4061_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_4061_);
    return v_k_4061_;
}
pub unsafe fn l_Lake_Verbosity_ctorElim___boxed(
    mut v_motive_4062_: *mut LeanObject,
    mut v_ctorIdx_4063_: *mut LeanObject,
    mut v_t_4064_: *mut LeanObject,
    mut v_h_4065_: *mut LeanObject,
    mut v_k_4066_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_4067_: u8 = 0;
    let mut v_res_4068_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_4067_ = (lean_unbox(v_t_4064_) as u8);
    v_res_4068_ = l_Lake_Verbosity_ctorElim(
        v_motive_4062_,
        v_ctorIdx_4063_,
        v_t_boxed_4067_,
        v_h_4065_,
        v_k_4066_,
    );
    lean_dec(v_k_4066_);
    lean_dec(v_ctorIdx_4063_);
    return v_res_4068_;
}
pub unsafe fn l_Lake_Verbosity_quiet_elim___redArg(
    mut v_quiet_4069_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_quiet_4069_);
    return v_quiet_4069_;
}
pub unsafe fn l_Lake_Verbosity_quiet_elim___redArg___boxed(
    mut v_quiet_4070_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4071_: *mut LeanObject = core::ptr::null_mut();
    v_res_4071_ = l_Lake_Verbosity_quiet_elim___redArg(v_quiet_4070_);
    lean_dec(v_quiet_4070_);
    return v_res_4071_;
}
pub unsafe fn l_Lake_Verbosity_quiet_elim(
    mut v_motive_4072_: *mut LeanObject,
    mut v_t_4073_: u8,
    mut v_h_4074_: *mut LeanObject,
    mut v_quiet_4075_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_quiet_4075_);
    return v_quiet_4075_;
}
pub unsafe fn l_Lake_Verbosity_quiet_elim___boxed(
    mut v_motive_4076_: *mut LeanObject,
    mut v_t_4077_: *mut LeanObject,
    mut v_h_4078_: *mut LeanObject,
    mut v_quiet_4079_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_4080_: u8 = 0;
    let mut v_res_4081_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_4080_ = (lean_unbox(v_t_4077_) as u8);
    v_res_4081_ =
        l_Lake_Verbosity_quiet_elim(v_motive_4076_, v_t_boxed_4080_, v_h_4078_, v_quiet_4079_);
    lean_dec(v_quiet_4079_);
    return v_res_4081_;
}
pub unsafe fn l_Lake_Verbosity_normal_elim___redArg(
    mut v_normal_4082_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_normal_4082_);
    return v_normal_4082_;
}
pub unsafe fn l_Lake_Verbosity_normal_elim___redArg___boxed(
    mut v_normal_4083_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4084_: *mut LeanObject = core::ptr::null_mut();
    v_res_4084_ = l_Lake_Verbosity_normal_elim___redArg(v_normal_4083_);
    lean_dec(v_normal_4083_);
    return v_res_4084_;
}
pub unsafe fn l_Lake_Verbosity_normal_elim(
    mut v_motive_4085_: *mut LeanObject,
    mut v_t_4086_: u8,
    mut v_h_4087_: *mut LeanObject,
    mut v_normal_4088_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_normal_4088_);
    return v_normal_4088_;
}
pub unsafe fn l_Lake_Verbosity_normal_elim___boxed(
    mut v_motive_4089_: *mut LeanObject,
    mut v_t_4090_: *mut LeanObject,
    mut v_h_4091_: *mut LeanObject,
    mut v_normal_4092_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_4093_: u8 = 0;
    let mut v_res_4094_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_4093_ = (lean_unbox(v_t_4090_) as u8);
    v_res_4094_ =
        l_Lake_Verbosity_normal_elim(v_motive_4089_, v_t_boxed_4093_, v_h_4091_, v_normal_4092_);
    lean_dec(v_normal_4092_);
    return v_res_4094_;
}
pub unsafe fn l_Lake_Verbosity_verbose_elim___redArg(
    mut v_verbose_4095_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_verbose_4095_);
    return v_verbose_4095_;
}
pub unsafe fn l_Lake_Verbosity_verbose_elim___redArg___boxed(
    mut v_verbose_4096_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4097_: *mut LeanObject = core::ptr::null_mut();
    v_res_4097_ = l_Lake_Verbosity_verbose_elim___redArg(v_verbose_4096_);
    lean_dec(v_verbose_4096_);
    return v_res_4097_;
}
pub unsafe fn l_Lake_Verbosity_verbose_elim(
    mut v_motive_4098_: *mut LeanObject,
    mut v_t_4099_: u8,
    mut v_h_4100_: *mut LeanObject,
    mut v_verbose_4101_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_verbose_4101_);
    return v_verbose_4101_;
}
pub unsafe fn l_Lake_Verbosity_verbose_elim___boxed(
    mut v_motive_4102_: *mut LeanObject,
    mut v_t_4103_: *mut LeanObject,
    mut v_h_4104_: *mut LeanObject,
    mut v_verbose_4105_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_4106_: u8 = 0;
    let mut v_res_4107_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_4106_ = (lean_unbox(v_t_4103_) as u8);
    v_res_4107_ =
        l_Lake_Verbosity_verbose_elim(v_motive_4102_, v_t_boxed_4106_, v_h_4104_, v_verbose_4105_);
    lean_dec(v_verbose_4105_);
    return v_res_4107_;
}
pub unsafe fn _init_l_Lake_instReprVerbosity_repr___closed__6() -> *mut LeanObject {
    let mut v___x_4117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: *mut LeanObject = core::ptr::null_mut();
    v___x_4117_ = lean_unsigned_to_nat(2);
    v___x_4118_ = lean_nat_to_int(v___x_4117_);
    return v___x_4118_;
}
pub unsafe fn _init_l_Lake_instReprVerbosity_repr___closed__7() -> *mut LeanObject {
    let mut v___x_4119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut LeanObject = core::ptr::null_mut();
    v___x_4119_ = lean_unsigned_to_nat(1);
    v___x_4120_ = lean_nat_to_int(v___x_4119_);
    return v___x_4120_;
}
pub unsafe fn l_Lake_instReprVerbosity_repr(
    mut v_x_4121_: u8,
    mut v_prec_4122_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: u8 = 0;
    let mut v___x_4128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4134_: u8 = 0;
    let mut v___x_4135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4141_: u8 = 0;
    let mut v___x_4142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4145_: u8 = 0;
    let mut v___x_4146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: u8 = 0;
    let mut v___x_4150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4153_: u8 = 0;
    let mut v___x_4154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match v_x_4121_ {
                0 => {
                    v___x_4144_ = lean_unsigned_to_nat(1024);
                    v___x_4145_ = lean_nat_dec_le(v___x_4144_, v_prec_4122_);
                    if v___x_4145_ == 0 {
                        v___x_4146_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprVerbosity_repr___closed__6),
                            core::ptr::addr_of_mut!(l_Lake_instReprVerbosity_repr___closed__6_once),
                            _init_l_Lake_instReprVerbosity_repr___closed__6,
                        );
                        v___y_4124_ = v___x_4146_;
                        state = 1;
                        continue;
                    } else {
                        v___x_4147_ = lean_obj_once(
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
                    v___x_4148_ = lean_unsigned_to_nat(1024);
                    v___x_4149_ = lean_nat_dec_le(v___x_4148_, v_prec_4122_);
                    if v___x_4149_ == 0 {
                        v___x_4150_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprVerbosity_repr___closed__6),
                            core::ptr::addr_of_mut!(l_Lake_instReprVerbosity_repr___closed__6_once),
                            _init_l_Lake_instReprVerbosity_repr___closed__6,
                        );
                        v___y_4131_ = v___x_4150_;
                        state = 2;
                        continue;
                    } else {
                        v___x_4151_ = lean_obj_once(
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
                    v___x_4152_ = lean_unsigned_to_nat(1024);
                    v___x_4153_ = lean_nat_dec_le(v___x_4152_, v_prec_4122_);
                    if v___x_4153_ == 0 {
                        v___x_4154_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprVerbosity_repr___closed__6),
                            core::ptr::addr_of_mut!(l_Lake_instReprVerbosity_repr___closed__6_once),
                            _init_l_Lake_instReprVerbosity_repr___closed__6,
                        );
                        v___y_4138_ = v___x_4154_;
                        state = 3;
                        continue;
                    } else {
                        v___x_4155_ = lean_obj_once(
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
                lean_inc(v___y_4124_);
                v___x_4126_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4126_, 0, v___y_4124_);
                lean_ctor_set(v___x_4126_, 1, v___x_4125_);
                v___x_4127_ = 0;
                v___x_4128_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_4128_, 0, v___x_4126_);
                lean_ctor_set_uint8(
                    v___x_4128_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4127_,
                );
                v___x_4129_ = l_Repr_addAppParen(v___x_4128_, v_prec_4122_);
                return v___x_4129_;
            }
            2 => {
                v___x_4132_ = l_Lake_instReprVerbosity_repr___closed__3;
                lean_inc(v___y_4131_);
                v___x_4133_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4133_, 0, v___y_4131_);
                lean_ctor_set(v___x_4133_, 1, v___x_4132_);
                v___x_4134_ = 0;
                v___x_4135_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_4135_, 0, v___x_4133_);
                lean_ctor_set_uint8(
                    v___x_4135_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4134_,
                );
                v___x_4136_ = l_Repr_addAppParen(v___x_4135_, v_prec_4122_);
                return v___x_4136_;
            }
            3 => {
                v___x_4139_ = l_Lake_instReprVerbosity_repr___closed__5;
                lean_inc(v___y_4138_);
                v___x_4140_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4140_, 0, v___y_4138_);
                lean_ctor_set(v___x_4140_, 1, v___x_4139_);
                v___x_4141_ = 0;
                v___x_4142_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_4142_, 0, v___x_4140_);
                lean_ctor_set_uint8(
                    v___x_4142_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
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
    mut v_x_4156_: *mut LeanObject,
    mut v_prec_4157_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_177__boxed_4158_: u8 = 0;
    let mut v_res_4159_: *mut LeanObject = core::ptr::null_mut();
    v_x_177__boxed_4158_ = (lean_unbox(v_x_4156_) as u8);
    v_res_4159_ = l_Lake_instReprVerbosity_repr(v_x_177__boxed_4158_, v_prec_4157_);
    lean_dec(v_prec_4157_);
    return v_res_4159_;
}
pub unsafe fn l_Lake_Verbosity_ofNat(mut v_n_4162_: *mut LeanObject) -> u8 {
    let mut v___x_4163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: u8 = 0;
    v___x_4163_ = lean_unsigned_to_nat(0);
    v___x_4164_ = lean_nat_dec_le(v_n_4162_, v___x_4163_);
    if v___x_4164_ == 0 {
        let mut v___x_4165_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4166_: u8 = 0;
        v___x_4165_ = lean_unsigned_to_nat(1);
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
pub unsafe fn l_Lake_Verbosity_ofNat___boxed(mut v_n_4170_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_4171_: u8 = 0;
    let mut v_r_4172_: *mut LeanObject = core::ptr::null_mut();
    v_res_4171_ = l_Lake_Verbosity_ofNat(v_n_4170_);
    lean_dec(v_n_4170_);
    v_r_4172_ = lean_box((v_res_4171_) as usize);
    return v_r_4172_;
}
pub unsafe fn l_Lake_instDecidableEqVerbosity(mut v_x_4173_: u8, mut v_y_4174_: u8) -> u8 {
    let mut v___x_4175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: u8 = 0;
    v___x_4175_ = l_Lake_Verbosity_ctorIdx(v_x_4173_);
    v___x_4176_ = l_Lake_Verbosity_ctorIdx(v_y_4174_);
    v___x_4177_ = lean_nat_dec_eq(v___x_4175_, v___x_4176_);
    lean_dec(v___x_4176_);
    lean_dec(v___x_4175_);
    return v___x_4177_;
}
pub unsafe fn l_Lake_instDecidableEqVerbosity___boxed(
    mut v_x_4178_: *mut LeanObject,
    mut v_y_4179_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_13__boxed_4180_: u8 = 0;
    let mut v_y_14__boxed_4181_: u8 = 0;
    let mut v_res_4182_: u8 = 0;
    let mut v_r_4183_: *mut LeanObject = core::ptr::null_mut();
    v_x_13__boxed_4180_ = (lean_unbox(v_x_4178_) as u8);
    v_y_14__boxed_4181_ = (lean_unbox(v_y_4179_) as u8);
    v_res_4182_ = l_Lake_instDecidableEqVerbosity(v_x_13__boxed_4180_, v_y_14__boxed_4181_);
    v_r_4183_ = lean_box((v_res_4182_) as usize);
    return v_r_4183_;
}
pub unsafe fn l_Lake_instOrdVerbosity_ord(mut v_x_4184_: u8, mut v_y_4185_: u8) -> u8 {
    let mut v___x_4186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: u8 = 0;
    v___x_4186_ = l_Lake_Verbosity_ctorIdx(v_x_4184_);
    v___x_4187_ = l_Lake_Verbosity_ctorIdx(v_y_4185_);
    v___x_4188_ = lean_nat_dec_lt(v___x_4186_, v___x_4187_);
    if v___x_4188_ == 0 {
        let mut v___x_4189_: u8 = 0;
        v___x_4189_ = lean_nat_dec_eq(v___x_4186_, v___x_4187_);
        lean_dec(v___x_4187_);
        lean_dec(v___x_4186_);
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
        lean_dec(v___x_4187_);
        lean_dec(v___x_4186_);
        v___x_4192_ = 0;
        return v___x_4192_;
    }
}
pub unsafe fn l_Lake_instOrdVerbosity_ord___boxed(
    mut v_x_4193_: *mut LeanObject,
    mut v_y_4194_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_30__boxed_4195_: u8 = 0;
    let mut v_y_31__boxed_4196_: u8 = 0;
    let mut v_res_4197_: u8 = 0;
    let mut v_r_4198_: *mut LeanObject = core::ptr::null_mut();
    v_x_30__boxed_4195_ = (lean_unbox(v_x_4193_) as u8);
    v_y_31__boxed_4196_ = (lean_unbox(v_y_4194_) as u8);
    v_res_4197_ = l_Lake_instOrdVerbosity_ord(v_x_30__boxed_4195_, v_y_31__boxed_4196_);
    v_r_4198_ = lean_box((v_res_4197_) as usize);
    return v_r_4198_;
}
pub unsafe fn _init_l_Lake_instLTVerbosity() -> *mut LeanObject {
    let mut v___x_4201_: *mut LeanObject = core::ptr::null_mut();
    v___x_4201_ = lean_box(0);
    return v___x_4201_;
}
pub unsafe fn _init_l_Lake_instLEVerbosity() -> *mut LeanObject {
    let mut v___x_4202_: *mut LeanObject = core::ptr::null_mut();
    v___x_4202_ = lean_box(0);
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
    mut v_x_4206_: *mut LeanObject,
    mut v_y_4207_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_4208_: u8 = 0;
    let mut v_y_boxed_4209_: u8 = 0;
    let mut v_res_4210_: u8 = 0;
    let mut v_r_4211_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_4208_ = (lean_unbox(v_x_4206_) as u8);
    v_y_boxed_4209_ = (lean_unbox(v_y_4207_) as u8);
    v_res_4210_ = l_Lake_instMinVerbosity___lam__0(v_x_boxed_4208_, v_y_boxed_4209_);
    v_r_4211_ = lean_box((v_res_4210_) as usize);
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
    mut v_x_4217_: *mut LeanObject,
    mut v_y_4218_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_4219_: u8 = 0;
    let mut v_y_boxed_4220_: u8 = 0;
    let mut v_res_4221_: u8 = 0;
    let mut v_r_4222_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_4219_ = (lean_unbox(v_x_4217_) as u8);
    v_y_boxed_4220_ = (lean_unbox(v_y_4218_) as u8);
    v_res_4221_ = l_Lake_instMaxVerbosity___lam__0(v_x_boxed_4219_, v_y_boxed_4220_);
    v_r_4222_ = lean_box((v_res_4221_) as usize);
    return v_r_4222_;
}
pub unsafe fn _init_l_Lake_instInhabitedVerbosity() -> u8 {
    let mut v___x_4225_: u8 = 0;
    v___x_4225_ = 1;
    return v___x_4225_;
}
pub unsafe fn l_Lake_AnsiMode_ctorIdx(mut v_x_4226_: u8) -> *mut LeanObject {
    match v_x_4226_ {
        0 => {
            let mut v___x_4227_: *mut LeanObject = core::ptr::null_mut();
            v___x_4227_ = lean_unsigned_to_nat(0);
            return v___x_4227_;
        }
        1 => {
            let mut v___x_4228_: *mut LeanObject = core::ptr::null_mut();
            v___x_4228_ = lean_unsigned_to_nat(1);
            return v___x_4228_;
        }
        _ => {
            let mut v___x_4229_: *mut LeanObject = core::ptr::null_mut();
            v___x_4229_ = lean_unsigned_to_nat(2);
            return v___x_4229_;
        }
    }
}
pub unsafe fn l_Lake_AnsiMode_ctorIdx___boxed(mut v_x_4230_: *mut LeanObject) -> *mut LeanObject {
    let mut v_x_boxed_4231_: u8 = 0;
    let mut v_res_4232_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_4231_ = (lean_unbox(v_x_4230_) as u8);
    v_res_4232_ = l_Lake_AnsiMode_ctorIdx(v_x_boxed_4231_);
    return v_res_4232_;
}
pub unsafe fn l_Lake_AnsiMode_toCtorIdx(mut v_x_4233_: u8) -> *mut LeanObject {
    let mut v___x_4234_: *mut LeanObject = core::ptr::null_mut();
    v___x_4234_ = l_Lake_AnsiMode_ctorIdx(v_x_4233_);
    return v___x_4234_;
}
pub unsafe fn l_Lake_AnsiMode_toCtorIdx___boxed(mut v_x_4235_: *mut LeanObject) -> *mut LeanObject {
    let mut v_x_4__boxed_4236_: u8 = 0;
    let mut v_res_4237_: *mut LeanObject = core::ptr::null_mut();
    v_x_4__boxed_4236_ = (lean_unbox(v_x_4235_) as u8);
    v_res_4237_ = l_Lake_AnsiMode_toCtorIdx(v_x_4__boxed_4236_);
    return v_res_4237_;
}
pub unsafe fn l_Lake_AnsiMode_ctorElim___redArg(mut v_k_4238_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_k_4238_);
    return v_k_4238_;
}
pub unsafe fn l_Lake_AnsiMode_ctorElim___redArg___boxed(
    mut v_k_4239_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4240_: *mut LeanObject = core::ptr::null_mut();
    v_res_4240_ = l_Lake_AnsiMode_ctorElim___redArg(v_k_4239_);
    lean_dec(v_k_4239_);
    return v_res_4240_;
}
pub unsafe fn l_Lake_AnsiMode_ctorElim(
    mut v_motive_4241_: *mut LeanObject,
    mut v_ctorIdx_4242_: *mut LeanObject,
    mut v_t_4243_: u8,
    mut v_h_4244_: *mut LeanObject,
    mut v_k_4245_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_4245_);
    return v_k_4245_;
}
pub unsafe fn l_Lake_AnsiMode_ctorElim___boxed(
    mut v_motive_4246_: *mut LeanObject,
    mut v_ctorIdx_4247_: *mut LeanObject,
    mut v_t_4248_: *mut LeanObject,
    mut v_h_4249_: *mut LeanObject,
    mut v_k_4250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_4251_: u8 = 0;
    let mut v_res_4252_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_4251_ = (lean_unbox(v_t_4248_) as u8);
    v_res_4252_ = l_Lake_AnsiMode_ctorElim(
        v_motive_4246_,
        v_ctorIdx_4247_,
        v_t_boxed_4251_,
        v_h_4249_,
        v_k_4250_,
    );
    lean_dec(v_k_4250_);
    lean_dec(v_ctorIdx_4247_);
    return v_res_4252_;
}
pub unsafe fn l_Lake_AnsiMode_auto_elim___redArg(
    mut v_auto_4253_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_auto_4253_);
    return v_auto_4253_;
}
pub unsafe fn l_Lake_AnsiMode_auto_elim___redArg___boxed(
    mut v_auto_4254_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4255_: *mut LeanObject = core::ptr::null_mut();
    v_res_4255_ = l_Lake_AnsiMode_auto_elim___redArg(v_auto_4254_);
    lean_dec(v_auto_4254_);
    return v_res_4255_;
}
pub unsafe fn l_Lake_AnsiMode_auto_elim(
    mut v_motive_4256_: *mut LeanObject,
    mut v_t_4257_: u8,
    mut v_h_4258_: *mut LeanObject,
    mut v_auto_4259_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_auto_4259_);
    return v_auto_4259_;
}
pub unsafe fn l_Lake_AnsiMode_auto_elim___boxed(
    mut v_motive_4260_: *mut LeanObject,
    mut v_t_4261_: *mut LeanObject,
    mut v_h_4262_: *mut LeanObject,
    mut v_auto_4263_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_4264_: u8 = 0;
    let mut v_res_4265_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_4264_ = (lean_unbox(v_t_4261_) as u8);
    v_res_4265_ =
        l_Lake_AnsiMode_auto_elim(v_motive_4260_, v_t_boxed_4264_, v_h_4262_, v_auto_4263_);
    lean_dec(v_auto_4263_);
    return v_res_4265_;
}
pub unsafe fn l_Lake_AnsiMode_ansi_elim___redArg(
    mut v_ansi_4266_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_ansi_4266_);
    return v_ansi_4266_;
}
pub unsafe fn l_Lake_AnsiMode_ansi_elim___redArg___boxed(
    mut v_ansi_4267_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4268_: *mut LeanObject = core::ptr::null_mut();
    v_res_4268_ = l_Lake_AnsiMode_ansi_elim___redArg(v_ansi_4267_);
    lean_dec(v_ansi_4267_);
    return v_res_4268_;
}
pub unsafe fn l_Lake_AnsiMode_ansi_elim(
    mut v_motive_4269_: *mut LeanObject,
    mut v_t_4270_: u8,
    mut v_h_4271_: *mut LeanObject,
    mut v_ansi_4272_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_ansi_4272_);
    return v_ansi_4272_;
}
pub unsafe fn l_Lake_AnsiMode_ansi_elim___boxed(
    mut v_motive_4273_: *mut LeanObject,
    mut v_t_4274_: *mut LeanObject,
    mut v_h_4275_: *mut LeanObject,
    mut v_ansi_4276_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_4277_: u8 = 0;
    let mut v_res_4278_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_4277_ = (lean_unbox(v_t_4274_) as u8);
    v_res_4278_ =
        l_Lake_AnsiMode_ansi_elim(v_motive_4273_, v_t_boxed_4277_, v_h_4275_, v_ansi_4276_);
    lean_dec(v_ansi_4276_);
    return v_res_4278_;
}
pub unsafe fn l_Lake_AnsiMode_noAnsi_elim___redArg(
    mut v_noAnsi_4279_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_noAnsi_4279_);
    return v_noAnsi_4279_;
}
pub unsafe fn l_Lake_AnsiMode_noAnsi_elim___redArg___boxed(
    mut v_noAnsi_4280_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4281_: *mut LeanObject = core::ptr::null_mut();
    v_res_4281_ = l_Lake_AnsiMode_noAnsi_elim___redArg(v_noAnsi_4280_);
    lean_dec(v_noAnsi_4280_);
    return v_res_4281_;
}
pub unsafe fn l_Lake_AnsiMode_noAnsi_elim(
    mut v_motive_4282_: *mut LeanObject,
    mut v_t_4283_: u8,
    mut v_h_4284_: *mut LeanObject,
    mut v_noAnsi_4285_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_noAnsi_4285_);
    return v_noAnsi_4285_;
}
pub unsafe fn l_Lake_AnsiMode_noAnsi_elim___boxed(
    mut v_motive_4286_: *mut LeanObject,
    mut v_t_4287_: *mut LeanObject,
    mut v_h_4288_: *mut LeanObject,
    mut v_noAnsi_4289_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_4290_: u8 = 0;
    let mut v_res_4291_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_4290_ = (lean_unbox(v_t_4287_) as u8);
    v_res_4291_ =
        l_Lake_AnsiMode_noAnsi_elim(v_motive_4286_, v_t_boxed_4290_, v_h_4288_, v_noAnsi_4289_);
    lean_dec(v_noAnsi_4289_);
    return v_res_4291_;
}
pub unsafe fn l_Lake_instReprAnsiMode_repr(
    mut v_x_4301_: u8,
    mut v_prec_4302_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4307_: u8 = 0;
    let mut v___x_4308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4314_: u8 = 0;
    let mut v___x_4315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: u8 = 0;
    let mut v___x_4322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4325_: u8 = 0;
    let mut v___x_4326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: u8 = 0;
    let mut v___x_4330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: u8 = 0;
    let mut v___x_4334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match v_x_4301_ {
                0 => {
                    v___x_4324_ = lean_unsigned_to_nat(1024);
                    v___x_4325_ = lean_nat_dec_le(v___x_4324_, v_prec_4302_);
                    if v___x_4325_ == 0 {
                        v___x_4326_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprVerbosity_repr___closed__6),
                            core::ptr::addr_of_mut!(l_Lake_instReprVerbosity_repr___closed__6_once),
                            _init_l_Lake_instReprVerbosity_repr___closed__6,
                        );
                        v___y_4304_ = v___x_4326_;
                        state = 1;
                        continue;
                    } else {
                        v___x_4327_ = lean_obj_once(
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
                    v___x_4328_ = lean_unsigned_to_nat(1024);
                    v___x_4329_ = lean_nat_dec_le(v___x_4328_, v_prec_4302_);
                    if v___x_4329_ == 0 {
                        v___x_4330_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprVerbosity_repr___closed__6),
                            core::ptr::addr_of_mut!(l_Lake_instReprVerbosity_repr___closed__6_once),
                            _init_l_Lake_instReprVerbosity_repr___closed__6,
                        );
                        v___y_4311_ = v___x_4330_;
                        state = 2;
                        continue;
                    } else {
                        v___x_4331_ = lean_obj_once(
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
                    v___x_4332_ = lean_unsigned_to_nat(1024);
                    v___x_4333_ = lean_nat_dec_le(v___x_4332_, v_prec_4302_);
                    if v___x_4333_ == 0 {
                        v___x_4334_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprVerbosity_repr___closed__6),
                            core::ptr::addr_of_mut!(l_Lake_instReprVerbosity_repr___closed__6_once),
                            _init_l_Lake_instReprVerbosity_repr___closed__6,
                        );
                        v___y_4318_ = v___x_4334_;
                        state = 3;
                        continue;
                    } else {
                        v___x_4335_ = lean_obj_once(
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
                lean_inc(v___y_4304_);
                v___x_4306_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4306_, 0, v___y_4304_);
                lean_ctor_set(v___x_4306_, 1, v___x_4305_);
                v___x_4307_ = 0;
                v___x_4308_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_4308_, 0, v___x_4306_);
                lean_ctor_set_uint8(
                    v___x_4308_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4307_,
                );
                v___x_4309_ = l_Repr_addAppParen(v___x_4308_, v_prec_4302_);
                return v___x_4309_;
            }
            2 => {
                v___x_4312_ = l_Lake_instReprAnsiMode_repr___closed__3;
                lean_inc(v___y_4311_);
                v___x_4313_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4313_, 0, v___y_4311_);
                lean_ctor_set(v___x_4313_, 1, v___x_4312_);
                v___x_4314_ = 0;
                v___x_4315_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_4315_, 0, v___x_4313_);
                lean_ctor_set_uint8(
                    v___x_4315_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4314_,
                );
                v___x_4316_ = l_Repr_addAppParen(v___x_4315_, v_prec_4302_);
                return v___x_4316_;
            }
            3 => {
                v___x_4319_ = l_Lake_instReprAnsiMode_repr___closed__5;
                lean_inc(v___y_4318_);
                v___x_4320_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4320_, 0, v___y_4318_);
                lean_ctor_set(v___x_4320_, 1, v___x_4319_);
                v___x_4321_ = 0;
                v___x_4322_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_4322_, 0, v___x_4320_);
                lean_ctor_set_uint8(
                    v___x_4322_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
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
    mut v_x_4336_: *mut LeanObject,
    mut v_prec_4337_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_173__boxed_4338_: u8 = 0;
    let mut v_res_4339_: *mut LeanObject = core::ptr::null_mut();
    v_x_173__boxed_4338_ = (lean_unbox(v_x_4336_) as u8);
    v_res_4339_ = l_Lake_instReprAnsiMode_repr(v_x_173__boxed_4338_, v_prec_4337_);
    lean_dec(v_prec_4337_);
    return v_res_4339_;
}
pub unsafe fn l_Lake_AnsiMode_isEnabled(mut v_out_4342_: *mut LeanObject, mut v_x_4343_: u8) -> u8 {
    match v_x_4343_ {
        0 => {
            let mut v_isTty_4345_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4346_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4347_: u8 = 0;
            v_isTty_4345_ = lean_ctor_get(v_out_4342_, 5);
            lean_inc_ref(v_isTty_4345_);
            lean_dec_ref(v_out_4342_);
            v___x_4346_ = lean_apply_1(v_isTty_4345_, lean_box(0));
            v___x_4347_ = (lean_unbox(v___x_4346_) as u8);
            return v___x_4347_;
        }
        1 => {
            let mut v___x_4348_: u8 = 0;
            lean_dec_ref(v_out_4342_);
            v___x_4348_ = 1;
            return v___x_4348_;
        }
        _ => {
            let mut v___x_4349_: u8 = 0;
            lean_dec_ref(v_out_4342_);
            v___x_4349_ = 0;
            return v___x_4349_;
        }
    }
}
pub unsafe fn l_Lake_AnsiMode_isEnabled___boxed(
    mut v_out_4350_: *mut LeanObject,
    mut v_x_4351_: *mut LeanObject,
    mut v_a_4352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_146__boxed_4353_: u8 = 0;
    let mut v_res_4354_: u8 = 0;
    let mut v_r_4355_: *mut LeanObject = core::ptr::null_mut();
    v_x_146__boxed_4353_ = (lean_unbox(v_x_4351_) as u8);
    v_res_4354_ = l_Lake_AnsiMode_isEnabled(v_out_4350_, v_x_146__boxed_4353_);
    v_r_4355_ = lean_box((v_res_4354_) as usize);
    return v_r_4355_;
}
pub unsafe fn l_Lake_Ansi_chalk(
    mut v_colorCode_4359_: *mut LeanObject,
    mut v_text_4360_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4367_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_colorCode_4368_: *mut LeanObject,
    mut v_text_4369_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4370_: *mut LeanObject = core::ptr::null_mut();
    v_res_4370_ = l_Lake_Ansi_chalk(v_colorCode_4368_, v_text_4369_);
    lean_dec_ref(v_text_4369_);
    lean_dec_ref(v_colorCode_4368_);
    return v_res_4370_;
}
pub unsafe fn l_Lake_OutStream_ctorIdx(mut v_x_4371_: *mut LeanObject) -> *mut LeanObject {
    match lean_obj_tag(v_x_4371_) {
        0 => {
            let mut v___x_4372_: *mut LeanObject = core::ptr::null_mut();
            v___x_4372_ = lean_unsigned_to_nat(0);
            return v___x_4372_;
        }
        1 => {
            let mut v___x_4373_: *mut LeanObject = core::ptr::null_mut();
            v___x_4373_ = lean_unsigned_to_nat(1);
            return v___x_4373_;
        }
        _ => {
            let mut v___x_4374_: *mut LeanObject = core::ptr::null_mut();
            v___x_4374_ = lean_unsigned_to_nat(2);
            return v___x_4374_;
        }
    }
}
pub unsafe fn l_Lake_OutStream_ctorIdx___boxed(mut v_x_4375_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_4376_: *mut LeanObject = core::ptr::null_mut();
    v_res_4376_ = l_Lake_OutStream_ctorIdx(v_x_4375_);
    lean_dec(v_x_4375_);
    return v_res_4376_;
}
pub unsafe fn l_Lake_OutStream_ctorElim___redArg(
    mut v_t_4377_: *mut LeanObject,
    mut v_k_4378_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_4377_) == 2 {
        let mut v_s_4379_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4380_: *mut LeanObject = core::ptr::null_mut();
        v_s_4379_ = lean_ctor_get(v_t_4377_, 0);
        lean_inc_ref(v_s_4379_);
        lean_dec_ref_known(v_t_4377_, 1);
        v___x_4380_ = lean_apply_1(v_k_4378_, v_s_4379_);
        return v___x_4380_;
    } else {
        lean_dec(v_t_4377_);
        return v_k_4378_;
    }
}
pub unsafe fn l_Lake_OutStream_ctorElim(
    mut v_motive_4381_: *mut LeanObject,
    mut v_ctorIdx_4382_: *mut LeanObject,
    mut v_t_4383_: *mut LeanObject,
    mut v_h_4384_: *mut LeanObject,
    mut v_k_4385_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4386_: *mut LeanObject = core::ptr::null_mut();
    v___x_4386_ = l_Lake_OutStream_ctorElim___redArg(v_t_4383_, v_k_4385_);
    return v___x_4386_;
}
pub unsafe fn l_Lake_OutStream_ctorElim___boxed(
    mut v_motive_4387_: *mut LeanObject,
    mut v_ctorIdx_4388_: *mut LeanObject,
    mut v_t_4389_: *mut LeanObject,
    mut v_h_4390_: *mut LeanObject,
    mut v_k_4391_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4392_: *mut LeanObject = core::ptr::null_mut();
    v_res_4392_ = l_Lake_OutStream_ctorElim(
        v_motive_4387_,
        v_ctorIdx_4388_,
        v_t_4389_,
        v_h_4390_,
        v_k_4391_,
    );
    lean_dec(v_ctorIdx_4388_);
    return v_res_4392_;
}
pub unsafe fn l_Lake_OutStream_stdout_elim___redArg(
    mut v_t_4393_: *mut LeanObject,
    mut v_stdout_4394_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4395_: *mut LeanObject = core::ptr::null_mut();
    v___x_4395_ = l_Lake_OutStream_ctorElim___redArg(v_t_4393_, v_stdout_4394_);
    return v___x_4395_;
}
pub unsafe fn l_Lake_OutStream_stdout_elim(
    mut v_motive_4396_: *mut LeanObject,
    mut v_t_4397_: *mut LeanObject,
    mut v_h_4398_: *mut LeanObject,
    mut v_stdout_4399_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4400_: *mut LeanObject = core::ptr::null_mut();
    v___x_4400_ = l_Lake_OutStream_ctorElim___redArg(v_t_4397_, v_stdout_4399_);
    return v___x_4400_;
}
pub unsafe fn l_Lake_OutStream_stderr_elim___redArg(
    mut v_t_4401_: *mut LeanObject,
    mut v_stderr_4402_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4403_: *mut LeanObject = core::ptr::null_mut();
    v___x_4403_ = l_Lake_OutStream_ctorElim___redArg(v_t_4401_, v_stderr_4402_);
    return v___x_4403_;
}
pub unsafe fn l_Lake_OutStream_stderr_elim(
    mut v_motive_4404_: *mut LeanObject,
    mut v_t_4405_: *mut LeanObject,
    mut v_h_4406_: *mut LeanObject,
    mut v_stderr_4407_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4408_: *mut LeanObject = core::ptr::null_mut();
    v___x_4408_ = l_Lake_OutStream_ctorElim___redArg(v_t_4405_, v_stderr_4407_);
    return v___x_4408_;
}
pub unsafe fn l_Lake_OutStream_stream_elim___redArg(
    mut v_t_4409_: *mut LeanObject,
    mut v_stream_4410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4411_: *mut LeanObject = core::ptr::null_mut();
    v___x_4411_ = l_Lake_OutStream_ctorElim___redArg(v_t_4409_, v_stream_4410_);
    return v___x_4411_;
}
pub unsafe fn l_Lake_OutStream_stream_elim(
    mut v_motive_4412_: *mut LeanObject,
    mut v_t_4413_: *mut LeanObject,
    mut v_h_4414_: *mut LeanObject,
    mut v_stream_4415_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4416_: *mut LeanObject = core::ptr::null_mut();
    v___x_4416_ = l_Lake_OutStream_ctorElim___redArg(v_t_4413_, v_stream_4415_);
    return v___x_4416_;
}
pub unsafe fn l_Lake_OutStream_get(mut v_x_4417_: *mut LeanObject) -> *mut LeanObject {
    match lean_obj_tag(v_x_4417_) {
        0 => {
            let mut v___x_4419_: *mut LeanObject = core::ptr::null_mut();
            v___x_4419_ = lean_get_stdout();
            return v___x_4419_;
        }
        1 => {
            let mut v___x_4420_: *mut LeanObject = core::ptr::null_mut();
            v___x_4420_ = lean_get_stderr();
            return v___x_4420_;
        }
        _ => {
            let mut v_s_4421_: *mut LeanObject = core::ptr::null_mut();
            v_s_4421_ = lean_ctor_get(v_x_4417_, 0);
            lean_inc_ref(v_s_4421_);
            return v_s_4421_;
        }
    }
}
pub unsafe fn l_Lake_OutStream_get___boxed(
    mut v_x_4422_: *mut LeanObject,
    mut v_a_4423_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4424_: *mut LeanObject = core::ptr::null_mut();
    v_res_4424_ = l_Lake_OutStream_get(v_x_4422_);
    lean_dec(v_x_4422_);
    return v_res_4424_;
}
pub unsafe fn l_Lake_instCoeStreamOutStream___lam__0(
    mut v_s_4425_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4426_: *mut LeanObject = core::ptr::null_mut();
    v___x_4426_ = lean_alloc_ctor(2, 1, (0) as u32);
    lean_ctor_set(v___x_4426_, 0, v_s_4425_);
    return v___x_4426_;
}
pub unsafe fn l_Lake_instCoeHandleOutStream___lam__0(
    mut v_h_4429_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut LeanObject = core::ptr::null_mut();
    v___x_4430_ = lean_stream_of_handle(v_h_4429_);
    v___x_4431_ = lean_alloc_ctor(2, 1, (0) as u32);
    lean_ctor_set(v___x_4431_, 0, v___x_4430_);
    return v___x_4431_;
}
pub unsafe fn l_Lake_LogLevel_ctorIdx(mut v_x_4434_: u8) -> *mut LeanObject {
    match v_x_4434_ {
        0 => {
            let mut v___x_4435_: *mut LeanObject = core::ptr::null_mut();
            v___x_4435_ = lean_unsigned_to_nat(0);
            return v___x_4435_;
        }
        1 => {
            let mut v___x_4436_: *mut LeanObject = core::ptr::null_mut();
            v___x_4436_ = lean_unsigned_to_nat(1);
            return v___x_4436_;
        }
        2 => {
            let mut v___x_4437_: *mut LeanObject = core::ptr::null_mut();
            v___x_4437_ = lean_unsigned_to_nat(2);
            return v___x_4437_;
        }
        _ => {
            let mut v___x_4438_: *mut LeanObject = core::ptr::null_mut();
            v___x_4438_ = lean_unsigned_to_nat(3);
            return v___x_4438_;
        }
    }
}
pub unsafe fn l_Lake_LogLevel_ctorIdx___boxed(mut v_x_4439_: *mut LeanObject) -> *mut LeanObject {
    let mut v_x_boxed_4440_: u8 = 0;
    let mut v_res_4441_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_4440_ = (lean_unbox(v_x_4439_) as u8);
    v_res_4441_ = l_Lake_LogLevel_ctorIdx(v_x_boxed_4440_);
    return v_res_4441_;
}
pub unsafe fn l_Lake_LogLevel_toCtorIdx(mut v_x_4442_: u8) -> *mut LeanObject {
    let mut v___x_4443_: *mut LeanObject = core::ptr::null_mut();
    v___x_4443_ = l_Lake_LogLevel_ctorIdx(v_x_4442_);
    return v___x_4443_;
}
pub unsafe fn l_Lake_LogLevel_toCtorIdx___boxed(mut v_x_4444_: *mut LeanObject) -> *mut LeanObject {
    let mut v_x_4__boxed_4445_: u8 = 0;
    let mut v_res_4446_: *mut LeanObject = core::ptr::null_mut();
    v_x_4__boxed_4445_ = (lean_unbox(v_x_4444_) as u8);
    v_res_4446_ = l_Lake_LogLevel_toCtorIdx(v_x_4__boxed_4445_);
    return v_res_4446_;
}
pub unsafe fn l_Lake_LogLevel_ctorElim___redArg(mut v_k_4447_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_k_4447_);
    return v_k_4447_;
}
pub unsafe fn l_Lake_LogLevel_ctorElim___redArg___boxed(
    mut v_k_4448_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4449_: *mut LeanObject = core::ptr::null_mut();
    v_res_4449_ = l_Lake_LogLevel_ctorElim___redArg(v_k_4448_);
    lean_dec(v_k_4448_);
    return v_res_4449_;
}
pub unsafe fn l_Lake_LogLevel_ctorElim(
    mut v_motive_4450_: *mut LeanObject,
    mut v_ctorIdx_4451_: *mut LeanObject,
    mut v_t_4452_: u8,
    mut v_h_4453_: *mut LeanObject,
    mut v_k_4454_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_4454_);
    return v_k_4454_;
}
pub unsafe fn l_Lake_LogLevel_ctorElim___boxed(
    mut v_motive_4455_: *mut LeanObject,
    mut v_ctorIdx_4456_: *mut LeanObject,
    mut v_t_4457_: *mut LeanObject,
    mut v_h_4458_: *mut LeanObject,
    mut v_k_4459_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_4460_: u8 = 0;
    let mut v_res_4461_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_4460_ = (lean_unbox(v_t_4457_) as u8);
    v_res_4461_ = l_Lake_LogLevel_ctorElim(
        v_motive_4455_,
        v_ctorIdx_4456_,
        v_t_boxed_4460_,
        v_h_4458_,
        v_k_4459_,
    );
    lean_dec(v_k_4459_);
    lean_dec(v_ctorIdx_4456_);
    return v_res_4461_;
}
pub unsafe fn l_Lake_LogLevel_trace_elim___redArg(
    mut v_trace_4462_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_trace_4462_);
    return v_trace_4462_;
}
pub unsafe fn l_Lake_LogLevel_trace_elim___redArg___boxed(
    mut v_trace_4463_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4464_: *mut LeanObject = core::ptr::null_mut();
    v_res_4464_ = l_Lake_LogLevel_trace_elim___redArg(v_trace_4463_);
    lean_dec(v_trace_4463_);
    return v_res_4464_;
}
pub unsafe fn l_Lake_LogLevel_trace_elim(
    mut v_motive_4465_: *mut LeanObject,
    mut v_t_4466_: u8,
    mut v_h_4467_: *mut LeanObject,
    mut v_trace_4468_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_trace_4468_);
    return v_trace_4468_;
}
pub unsafe fn l_Lake_LogLevel_trace_elim___boxed(
    mut v_motive_4469_: *mut LeanObject,
    mut v_t_4470_: *mut LeanObject,
    mut v_h_4471_: *mut LeanObject,
    mut v_trace_4472_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_4473_: u8 = 0;
    let mut v_res_4474_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_4473_ = (lean_unbox(v_t_4470_) as u8);
    v_res_4474_ =
        l_Lake_LogLevel_trace_elim(v_motive_4469_, v_t_boxed_4473_, v_h_4471_, v_trace_4472_);
    lean_dec(v_trace_4472_);
    return v_res_4474_;
}
pub unsafe fn l_Lake_LogLevel_info_elim___redArg(
    mut v_info_4475_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_info_4475_);
    return v_info_4475_;
}
pub unsafe fn l_Lake_LogLevel_info_elim___redArg___boxed(
    mut v_info_4476_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4477_: *mut LeanObject = core::ptr::null_mut();
    v_res_4477_ = l_Lake_LogLevel_info_elim___redArg(v_info_4476_);
    lean_dec(v_info_4476_);
    return v_res_4477_;
}
pub unsafe fn l_Lake_LogLevel_info_elim(
    mut v_motive_4478_: *mut LeanObject,
    mut v_t_4479_: u8,
    mut v_h_4480_: *mut LeanObject,
    mut v_info_4481_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_info_4481_);
    return v_info_4481_;
}
pub unsafe fn l_Lake_LogLevel_info_elim___boxed(
    mut v_motive_4482_: *mut LeanObject,
    mut v_t_4483_: *mut LeanObject,
    mut v_h_4484_: *mut LeanObject,
    mut v_info_4485_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_4486_: u8 = 0;
    let mut v_res_4487_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_4486_ = (lean_unbox(v_t_4483_) as u8);
    v_res_4487_ =
        l_Lake_LogLevel_info_elim(v_motive_4482_, v_t_boxed_4486_, v_h_4484_, v_info_4485_);
    lean_dec(v_info_4485_);
    return v_res_4487_;
}
pub unsafe fn l_Lake_LogLevel_warning_elim___redArg(
    mut v_warning_4488_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_warning_4488_);
    return v_warning_4488_;
}
pub unsafe fn l_Lake_LogLevel_warning_elim___redArg___boxed(
    mut v_warning_4489_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4490_: *mut LeanObject = core::ptr::null_mut();
    v_res_4490_ = l_Lake_LogLevel_warning_elim___redArg(v_warning_4489_);
    lean_dec(v_warning_4489_);
    return v_res_4490_;
}
pub unsafe fn l_Lake_LogLevel_warning_elim(
    mut v_motive_4491_: *mut LeanObject,
    mut v_t_4492_: u8,
    mut v_h_4493_: *mut LeanObject,
    mut v_warning_4494_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_warning_4494_);
    return v_warning_4494_;
}
pub unsafe fn l_Lake_LogLevel_warning_elim___boxed(
    mut v_motive_4495_: *mut LeanObject,
    mut v_t_4496_: *mut LeanObject,
    mut v_h_4497_: *mut LeanObject,
    mut v_warning_4498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_4499_: u8 = 0;
    let mut v_res_4500_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_4499_ = (lean_unbox(v_t_4496_) as u8);
    v_res_4500_ =
        l_Lake_LogLevel_warning_elim(v_motive_4495_, v_t_boxed_4499_, v_h_4497_, v_warning_4498_);
    lean_dec(v_warning_4498_);
    return v_res_4500_;
}
pub unsafe fn l_Lake_LogLevel_error_elim___redArg(
    mut v_error_4501_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_error_4501_);
    return v_error_4501_;
}
pub unsafe fn l_Lake_LogLevel_error_elim___redArg___boxed(
    mut v_error_4502_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4503_: *mut LeanObject = core::ptr::null_mut();
    v_res_4503_ = l_Lake_LogLevel_error_elim___redArg(v_error_4502_);
    lean_dec(v_error_4502_);
    return v_res_4503_;
}
pub unsafe fn l_Lake_LogLevel_error_elim(
    mut v_motive_4504_: *mut LeanObject,
    mut v_t_4505_: u8,
    mut v_h_4506_: *mut LeanObject,
    mut v_error_4507_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_error_4507_);
    return v_error_4507_;
}
pub unsafe fn l_Lake_LogLevel_error_elim___boxed(
    mut v_motive_4508_: *mut LeanObject,
    mut v_t_4509_: *mut LeanObject,
    mut v_h_4510_: *mut LeanObject,
    mut v_error_4511_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_4512_: u8 = 0;
    let mut v_res_4513_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_4512_ = (lean_unbox(v_t_4509_) as u8);
    v_res_4513_ =
        l_Lake_LogLevel_error_elim(v_motive_4508_, v_t_boxed_4512_, v_h_4510_, v_error_4511_);
    lean_dec(v_error_4511_);
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
    mut v_prec_4529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4534_: u8 = 0;
    let mut v___x_4535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: u8 = 0;
    let mut v___x_4542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4548_: u8 = 0;
    let mut v___x_4549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: u8 = 0;
    let mut v___x_4556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4559_: u8 = 0;
    let mut v___x_4560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: u8 = 0;
    let mut v___x_4564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4567_: u8 = 0;
    let mut v___x_4568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4571_: u8 = 0;
    let mut v___x_4572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4573_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match v_x_4528_ {
                0 => {
                    v___x_4558_ = lean_unsigned_to_nat(1024);
                    v___x_4559_ = lean_nat_dec_le(v___x_4558_, v_prec_4529_);
                    if v___x_4559_ == 0 {
                        v___x_4560_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprVerbosity_repr___closed__6),
                            core::ptr::addr_of_mut!(l_Lake_instReprVerbosity_repr___closed__6_once),
                            _init_l_Lake_instReprVerbosity_repr___closed__6,
                        );
                        v___y_4531_ = v___x_4560_;
                        state = 1;
                        continue;
                    } else {
                        v___x_4561_ = lean_obj_once(
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
                    v___x_4562_ = lean_unsigned_to_nat(1024);
                    v___x_4563_ = lean_nat_dec_le(v___x_4562_, v_prec_4529_);
                    if v___x_4563_ == 0 {
                        v___x_4564_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprVerbosity_repr___closed__6),
                            core::ptr::addr_of_mut!(l_Lake_instReprVerbosity_repr___closed__6_once),
                            _init_l_Lake_instReprVerbosity_repr___closed__6,
                        );
                        v___y_4538_ = v___x_4564_;
                        state = 2;
                        continue;
                    } else {
                        v___x_4565_ = lean_obj_once(
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
                    v___x_4566_ = lean_unsigned_to_nat(1024);
                    v___x_4567_ = lean_nat_dec_le(v___x_4566_, v_prec_4529_);
                    if v___x_4567_ == 0 {
                        v___x_4568_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprVerbosity_repr___closed__6),
                            core::ptr::addr_of_mut!(l_Lake_instReprVerbosity_repr___closed__6_once),
                            _init_l_Lake_instReprVerbosity_repr___closed__6,
                        );
                        v___y_4545_ = v___x_4568_;
                        state = 3;
                        continue;
                    } else {
                        v___x_4569_ = lean_obj_once(
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
                    v___x_4570_ = lean_unsigned_to_nat(1024);
                    v___x_4571_ = lean_nat_dec_le(v___x_4570_, v_prec_4529_);
                    if v___x_4571_ == 0 {
                        v___x_4572_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprVerbosity_repr___closed__6),
                            core::ptr::addr_of_mut!(l_Lake_instReprVerbosity_repr___closed__6_once),
                            _init_l_Lake_instReprVerbosity_repr___closed__6,
                        );
                        v___y_4552_ = v___x_4572_;
                        state = 4;
                        continue;
                    } else {
                        v___x_4573_ = lean_obj_once(
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
                lean_inc(v___y_4531_);
                v___x_4533_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4533_, 0, v___y_4531_);
                lean_ctor_set(v___x_4533_, 1, v___x_4532_);
                v___x_4534_ = 0;
                v___x_4535_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_4535_, 0, v___x_4533_);
                lean_ctor_set_uint8(
                    v___x_4535_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4534_,
                );
                v___x_4536_ = l_Repr_addAppParen(v___x_4535_, v_prec_4529_);
                return v___x_4536_;
            }
            2 => {
                v___x_4539_ = l_Lake_instReprLogLevel_repr___closed__3;
                lean_inc(v___y_4538_);
                v___x_4540_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4540_, 0, v___y_4538_);
                lean_ctor_set(v___x_4540_, 1, v___x_4539_);
                v___x_4541_ = 0;
                v___x_4542_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_4542_, 0, v___x_4540_);
                lean_ctor_set_uint8(
                    v___x_4542_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4541_,
                );
                v___x_4543_ = l_Repr_addAppParen(v___x_4542_, v_prec_4529_);
                return v___x_4543_;
            }
            3 => {
                v___x_4546_ = l_Lake_instReprLogLevel_repr___closed__5;
                lean_inc(v___y_4545_);
                v___x_4547_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4547_, 0, v___y_4545_);
                lean_ctor_set(v___x_4547_, 1, v___x_4546_);
                v___x_4548_ = 0;
                v___x_4549_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_4549_, 0, v___x_4547_);
                lean_ctor_set_uint8(
                    v___x_4549_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4548_,
                );
                v___x_4550_ = l_Repr_addAppParen(v___x_4549_, v_prec_4529_);
                return v___x_4550_;
            }
            4 => {
                v___x_4553_ = l_Lake_instReprLogLevel_repr___closed__7;
                lean_inc(v___y_4552_);
                v___x_4554_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4554_, 0, v___y_4552_);
                lean_ctor_set(v___x_4554_, 1, v___x_4553_);
                v___x_4555_ = 0;
                v___x_4556_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_4556_, 0, v___x_4554_);
                lean_ctor_set_uint8(
                    v___x_4556_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
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
    mut v_x_4574_: *mut LeanObject,
    mut v_prec_4575_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_229__boxed_4576_: u8 = 0;
    let mut v_res_4577_: *mut LeanObject = core::ptr::null_mut();
    v_x_229__boxed_4576_ = (lean_unbox(v_x_4574_) as u8);
    v_res_4577_ = l_Lake_instReprLogLevel_repr(v_x_229__boxed_4576_, v_prec_4575_);
    lean_dec(v_prec_4575_);
    return v_res_4577_;
}
pub unsafe fn l_Lake_LogLevel_ofNat(mut v_n_4580_: *mut LeanObject) -> u8 {
    let mut v___x_4581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4582_: u8 = 0;
    v___x_4581_ = lean_unsigned_to_nat(1);
    v___x_4582_ = lean_nat_dec_le(v_n_4580_, v___x_4581_);
    if v___x_4582_ == 0 {
        let mut v___x_4583_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4584_: u8 = 0;
        v___x_4583_ = lean_unsigned_to_nat(2);
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
        let mut v___x_4587_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4588_: u8 = 0;
        v___x_4587_ = lean_unsigned_to_nat(0);
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
pub unsafe fn l_Lake_LogLevel_ofNat___boxed(mut v_n_4591_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_4592_: u8 = 0;
    let mut v_r_4593_: *mut LeanObject = core::ptr::null_mut();
    v_res_4592_ = l_Lake_LogLevel_ofNat(v_n_4591_);
    lean_dec(v_n_4591_);
    v_r_4593_ = lean_box((v_res_4592_) as usize);
    return v_r_4593_;
}
pub unsafe fn l_Lake_instDecidableEqLogLevel(mut v_x_4594_: u8, mut v_y_4595_: u8) -> u8 {
    let mut v___x_4596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4598_: u8 = 0;
    v___x_4596_ = l_Lake_LogLevel_ctorIdx(v_x_4594_);
    v___x_4597_ = l_Lake_LogLevel_ctorIdx(v_y_4595_);
    v___x_4598_ = lean_nat_dec_eq(v___x_4596_, v___x_4597_);
    lean_dec(v___x_4597_);
    lean_dec(v___x_4596_);
    return v___x_4598_;
}
pub unsafe fn l_Lake_instDecidableEqLogLevel___boxed(
    mut v_x_4599_: *mut LeanObject,
    mut v_y_4600_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_13__boxed_4601_: u8 = 0;
    let mut v_y_14__boxed_4602_: u8 = 0;
    let mut v_res_4603_: u8 = 0;
    let mut v_r_4604_: *mut LeanObject = core::ptr::null_mut();
    v_x_13__boxed_4601_ = (lean_unbox(v_x_4599_) as u8);
    v_y_14__boxed_4602_ = (lean_unbox(v_y_4600_) as u8);
    v_res_4603_ = l_Lake_instDecidableEqLogLevel(v_x_13__boxed_4601_, v_y_14__boxed_4602_);
    v_r_4604_ = lean_box((v_res_4603_) as usize);
    return v_r_4604_;
}
pub unsafe fn l_Lake_instOrdLogLevel_ord(mut v_x_4605_: u8, mut v_y_4606_: u8) -> u8 {
    let mut v___x_4607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4609_: u8 = 0;
    v___x_4607_ = l_Lake_LogLevel_ctorIdx(v_x_4605_);
    v___x_4608_ = l_Lake_LogLevel_ctorIdx(v_y_4606_);
    v___x_4609_ = lean_nat_dec_lt(v___x_4607_, v___x_4608_);
    if v___x_4609_ == 0 {
        let mut v___x_4610_: u8 = 0;
        v___x_4610_ = lean_nat_dec_eq(v___x_4607_, v___x_4608_);
        lean_dec(v___x_4608_);
        lean_dec(v___x_4607_);
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
        lean_dec(v___x_4608_);
        lean_dec(v___x_4607_);
        v___x_4613_ = 0;
        return v___x_4613_;
    }
}
pub unsafe fn l_Lake_instOrdLogLevel_ord___boxed(
    mut v_x_4614_: *mut LeanObject,
    mut v_y_4615_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_30__boxed_4616_: u8 = 0;
    let mut v_y_31__boxed_4617_: u8 = 0;
    let mut v_res_4618_: u8 = 0;
    let mut v_r_4619_: *mut LeanObject = core::ptr::null_mut();
    v_x_30__boxed_4616_ = (lean_unbox(v_x_4614_) as u8);
    v_y_31__boxed_4617_ = (lean_unbox(v_y_4615_) as u8);
    v_res_4618_ = l_Lake_instOrdLogLevel_ord(v_x_30__boxed_4616_, v_y_31__boxed_4617_);
    v_r_4619_ = lean_box((v_res_4618_) as usize);
    return v_r_4619_;
}
pub unsafe fn l_Lake_instToJsonLogLevel_toJson(mut v_x_4634_: u8) -> *mut LeanObject {
    match v_x_4634_ {
        0 => {
            let mut v___x_4635_: *mut LeanObject = core::ptr::null_mut();
            v___x_4635_ = l_Lake_instToJsonLogLevel_toJson___closed__1;
            return v___x_4635_;
        }
        1 => {
            let mut v___x_4636_: *mut LeanObject = core::ptr::null_mut();
            v___x_4636_ = l_Lake_instToJsonLogLevel_toJson___closed__3;
            return v___x_4636_;
        }
        2 => {
            let mut v___x_4637_: *mut LeanObject = core::ptr::null_mut();
            v___x_4637_ = l_Lake_instToJsonLogLevel_toJson___closed__5;
            return v___x_4637_;
        }
        _ => {
            let mut v___x_4638_: *mut LeanObject = core::ptr::null_mut();
            v___x_4638_ = l_Lake_instToJsonLogLevel_toJson___closed__7;
            return v___x_4638_;
        }
    }
}
pub unsafe fn l_Lake_instToJsonLogLevel_toJson___boxed(
    mut v_x_4639_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_88__boxed_4640_: u8 = 0;
    let mut v_res_4641_: *mut LeanObject = core::ptr::null_mut();
    v_x_88__boxed_4640_ = (lean_unbox(v_x_4639_) as u8);
    v_res_4641_ = l_Lake_instToJsonLogLevel_toJson(v_x_88__boxed_4640_);
    return v_res_4641_;
}
pub unsafe fn l_Lake_instFromJsonLogLevel_fromJson(
    mut v_json_4662_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4663_: *mut LeanObject = core::ptr::null_mut();
    v___x_4663_ = l_Lean_Json_getTag_x3f(v_json_4662_);
    if lean_obj_tag(v___x_4663_) == 0 {
        let mut v___x_4664_: *mut LeanObject = core::ptr::null_mut();
        v___x_4664_ = l_Lake_instFromJsonLogLevel_fromJson___closed__1;
        return v___x_4664_;
    } else {
        let mut v_val_4665_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4666_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4667_: u8 = 0;
        v_val_4665_ = lean_ctor_get(v___x_4663_, 0);
        lean_inc(v_val_4665_);
        lean_dec_ref_known(v___x_4663_, 1);
        v___x_4666_ = l_Lake_instToJsonLogLevel_toJson___closed__6;
        v___x_4667_ = lean_string_dec_eq(v_val_4665_, v___x_4666_);
        if v___x_4667_ == 0 {
            let mut v___x_4668_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4669_: u8 = 0;
            v___x_4668_ = l_Lake_instToJsonLogLevel_toJson___closed__0;
            v___x_4669_ = lean_string_dec_eq(v_val_4665_, v___x_4668_);
            if v___x_4669_ == 0 {
                let mut v___x_4670_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4671_: u8 = 0;
                v___x_4670_ = l_Lake_instToJsonLogLevel_toJson___closed__2;
                v___x_4671_ = lean_string_dec_eq(v_val_4665_, v___x_4670_);
                if v___x_4671_ == 0 {
                    let mut v___x_4672_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_4673_: u8 = 0;
                    v___x_4672_ = l_Lake_instToJsonLogLevel_toJson___closed__4;
                    v___x_4673_ = lean_string_dec_eq(v_val_4665_, v___x_4672_);
                    lean_dec(v_val_4665_);
                    if v___x_4673_ == 0 {
                        let mut v___x_4674_: *mut LeanObject = core::ptr::null_mut();
                        v___x_4674_ = l_Lake_instFromJsonLogLevel_fromJson___closed__3;
                        return v___x_4674_;
                    } else {
                        let mut v___x_4675_: *mut LeanObject = core::ptr::null_mut();
                        v___x_4675_ = l_Lake_instFromJsonLogLevel_fromJson___closed__4;
                        return v___x_4675_;
                    }
                } else {
                    let mut v___x_4676_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec(v_val_4665_);
                    v___x_4676_ = l_Lake_instFromJsonLogLevel_fromJson___closed__5;
                    return v___x_4676_;
                }
            } else {
                let mut v___x_4677_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_val_4665_);
                v___x_4677_ = l_Lake_instFromJsonLogLevel_fromJson___closed__6;
                return v___x_4677_;
            }
        } else {
            let mut v___x_4678_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_val_4665_);
            v___x_4678_ = l_Lake_instFromJsonLogLevel_fromJson___closed__7;
            return v___x_4678_;
        }
    }
}
pub unsafe fn _init_l_Lake_instLTLogLevel() -> *mut LeanObject {
    let mut v___x_4681_: *mut LeanObject = core::ptr::null_mut();
    v___x_4681_ = lean_box(0);
    return v___x_4681_;
}
pub unsafe fn _init_l_Lake_instLELogLevel() -> *mut LeanObject {
    let mut v___x_4682_: *mut LeanObject = core::ptr::null_mut();
    v___x_4682_ = lean_box(0);
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
    mut v_x_4686_: *mut LeanObject,
    mut v_y_4687_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_4688_: u8 = 0;
    let mut v_y_boxed_4689_: u8 = 0;
    let mut v_res_4690_: u8 = 0;
    let mut v_r_4691_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_4688_ = (lean_unbox(v_x_4686_) as u8);
    v_y_boxed_4689_ = (lean_unbox(v_y_4687_) as u8);
    v_res_4690_ = l_Lake_instMinLogLevel___lam__0(v_x_boxed_4688_, v_y_boxed_4689_);
    v_r_4691_ = lean_box((v_res_4690_) as usize);
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
    mut v_x_4697_: *mut LeanObject,
    mut v_y_4698_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_4699_: u8 = 0;
    let mut v_y_boxed_4700_: u8 = 0;
    let mut v_res_4701_: u8 = 0;
    let mut v_r_4702_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_4699_ = (lean_unbox(v_x_4697_) as u8);
    v_y_boxed_4700_ = (lean_unbox(v_y_4698_) as u8);
    v_res_4701_ = l_Lake_instMaxLogLevel___lam__0(v_x_boxed_4699_, v_y_boxed_4700_);
    v_r_4702_ = lean_box((v_res_4701_) as usize);
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
pub unsafe fn l_Lake_LogLevel_icon___boxed(mut v_x_4709_: *mut LeanObject) -> *mut LeanObject {
    let mut v_x_33__boxed_4710_: u8 = 0;
    let mut v_res_4711_: u32 = 0;
    let mut v_r_4712_: *mut LeanObject = core::ptr::null_mut();
    v_x_33__boxed_4710_ = (lean_unbox(v_x_4709_) as u8);
    v_res_4711_ = l_Lake_LogLevel_icon(v_x_33__boxed_4710_);
    v_r_4712_ = lean_box_uint32(v_res_4711_);
    return v_r_4712_;
}
pub unsafe fn l_Lake_LogLevel_ansiColor(mut v_x_4716_: u8) -> *mut LeanObject {
    match v_x_4716_ {
        2 => {
            let mut v___x_4717_: *mut LeanObject = core::ptr::null_mut();
            v___x_4717_ = l_Lake_LogLevel_ansiColor___closed__0;
            return v___x_4717_;
        }
        3 => {
            let mut v___x_4718_: *mut LeanObject = core::ptr::null_mut();
            v___x_4718_ = l_Lake_LogLevel_ansiColor___closed__1;
            return v___x_4718_;
        }
        _ => {
            let mut v___x_4719_: *mut LeanObject = core::ptr::null_mut();
            v___x_4719_ = l_Lake_LogLevel_ansiColor___closed__2;
            return v___x_4719_;
        }
    }
}
pub unsafe fn l_Lake_LogLevel_ansiColor___boxed(mut v_x_4720_: *mut LeanObject) -> *mut LeanObject {
    let mut v_x_36__boxed_4721_: u8 = 0;
    let mut v_res_4722_: *mut LeanObject = core::ptr::null_mut();
    v_x_36__boxed_4721_ = (lean_unbox(v_x_4720_) as u8);
    v_res_4722_ = l_Lake_LogLevel_ansiColor(v_x_36__boxed_4721_);
    return v_res_4722_;
}
pub unsafe fn l_String_mapAux___at___00Lake_LogLevel_ofString_x3f_spec__0(
    mut v_s_4723_: *mut LeanObject,
    mut v_p_4724_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4726_: u32 = 0;
    let mut v___x_4727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4731_: *mut LeanObject = core::ptr::null_mut();
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
                    lean_dec(v_p_4724_);
                    return v_s_4723_;
                }
            }
            1 => {
                lean_inc(v_p_4724_);
                v___x_4727_ = lean_string_utf8_set(v_s_4723_, v_p_4724_, v___y_4726_);
                v___x_4728_ = l_Char_utf8Size(v___y_4726_);
                v___x_4729_ = lean_nat_add(v_p_4724_, v___x_4728_);
                lean_dec(v___x_4728_);
                lean_dec(v_p_4724_);
                v_s_4723_ = v___x_4727_;
                v_p_4724_ = v___x_4729_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LogLevel_ofString_x3f(mut v_s_4754_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_4756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4762_: u8 = 0;
    let mut v___x_4763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4764_: u8 = 0;
    let mut v___x_4765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4766_: u8 = 0;
    let mut v___x_4767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4768_: u8 = 0;
    let mut v___x_4769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4770_: u8 = 0;
    let mut v___x_4771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4772_: u8 = 0;
    let mut v___x_4773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4775_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4759_ = lean_unsigned_to_nat(0);
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
                                    lean_dec_ref(v___x_4760_);
                                    if v___x_4772_ == 0 {
                                        v___x_4773_ = lean_box(0);
                                        return v___x_4773_;
                                    } else {
                                        v___x_4774_ = l_Lake_LogLevel_ofString_x3f___closed__4;
                                        return v___x_4774_;
                                    }
                                } else {
                                    lean_dec_ref(v___x_4760_);
                                    state = 2;
                                    continue;
                                }
                            } else {
                                lean_dec_ref(v___x_4760_);
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v___x_4760_);
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_4760_);
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_4760_);
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
pub unsafe fn l_Lake_LogLevel_toString(mut v_x_4776_: u8) -> *mut LeanObject {
    match v_x_4776_ {
        0 => {
            let mut v___x_4777_: *mut LeanObject = core::ptr::null_mut();
            v___x_4777_ = l_Lake_instToJsonLogLevel_toJson___closed__0;
            return v___x_4777_;
        }
        1 => {
            let mut v___x_4778_: *mut LeanObject = core::ptr::null_mut();
            v___x_4778_ = l_Lake_instToJsonLogLevel_toJson___closed__2;
            return v___x_4778_;
        }
        2 => {
            let mut v___x_4779_: *mut LeanObject = core::ptr::null_mut();
            v___x_4779_ = l_Lake_instToJsonLogLevel_toJson___closed__4;
            return v___x_4779_;
        }
        _ => {
            let mut v___x_4780_: *mut LeanObject = core::ptr::null_mut();
            v___x_4780_ = l_Lake_instToJsonLogLevel_toJson___closed__6;
            return v___x_4780_;
        }
    }
}
pub unsafe fn l_Lake_LogLevel_toString___boxed(mut v_x_4781_: *mut LeanObject) -> *mut LeanObject {
    let mut v_x_36__boxed_4782_: u8 = 0;
    let mut v_res_4783_: *mut LeanObject = core::ptr::null_mut();
    v_x_36__boxed_4782_ = (lean_unbox(v_x_4781_) as u8);
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
    mut v_x_4790_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_25__boxed_4791_: u8 = 0;
    let mut v_res_4792_: u8 = 0;
    let mut v_r_4793_: *mut LeanObject = core::ptr::null_mut();
    v_x_25__boxed_4791_ = (lean_unbox(v_x_4790_) as u8);
    v_res_4792_ = l_Lake_LogLevel_ofMessageSeverity(v_x_25__boxed_4791_);
    v_r_4793_ = lean_box((v_res_4792_) as usize);
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
    mut v_x_4798_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_30__boxed_4799_: u8 = 0;
    let mut v_res_4800_: u8 = 0;
    let mut v_r_4801_: *mut LeanObject = core::ptr::null_mut();
    v_x_30__boxed_4799_ = (lean_unbox(v_x_4798_) as u8);
    v_res_4800_ = l_Lake_LogLevel_toMessageSeverity(v_x_30__boxed_4799_);
    v_r_4801_ = lean_box((v_res_4800_) as usize);
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
pub unsafe fn l_Lake_Verbosity_minLogLv___boxed(mut v_x_4806_: *mut LeanObject) -> *mut LeanObject {
    let mut v_x_25__boxed_4807_: u8 = 0;
    let mut v_res_4808_: u8 = 0;
    let mut v_r_4809_: *mut LeanObject = core::ptr::null_mut();
    v_x_25__boxed_4807_ = (lean_unbox(v_x_4806_) as u8);
    v_res_4808_ = l_Lake_Verbosity_minLogLv(v_x_25__boxed_4807_);
    v_r_4809_ = lean_box((v_res_4808_) as usize);
    return v_r_4809_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lake_instToJsonLogEntry_toJson_spec__0(
    mut v_a_4816_: *mut LeanObject,
    mut v_a_4817_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4821_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_4816_) == 0 {
                    v___x_4818_ = lean_array_to_list(v_a_4817_);
                    return v___x_4818_;
                } else {
                    v_head_4819_ = lean_ctor_get(v_a_4816_, 0);
                    lean_inc(v_head_4819_);
                    v_tail_4820_ = lean_ctor_get(v_a_4816_, 1);
                    lean_inc(v_tail_4820_);
                    lean_dec_ref_known(v_a_4816_, 2);
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
pub unsafe fn l_Lake_instToJsonLogEntry_toJson(mut v_x_4827_: *mut LeanObject) -> *mut LeanObject {
    let mut v_level_4828_: u8 = 0;
    let mut v_message_4829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4843_: *mut LeanObject = core::ptr::null_mut();
    v_level_4828_ = lean_ctor_get_uint8(
        v_x_4827_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
    );
    v_message_4829_ = lean_ctor_get(v_x_4827_, 0);
    v___x_4830_ = l_Lake_instToJsonLogEntry_toJson___closed__0;
    v___x_4831_ = l_Lake_instToJsonLogLevel_toJson(v_level_4828_);
    v___x_4832_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4832_, 0, v___x_4830_);
    lean_ctor_set(v___x_4832_, 1, v___x_4831_);
    v___x_4833_ = lean_box(0);
    v___x_4834_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_4834_, 0, v___x_4832_);
    lean_ctor_set(v___x_4834_, 1, v___x_4833_);
    v___x_4835_ = l_Lake_instToJsonLogEntry_toJson___closed__1;
    lean_inc_ref(v_message_4829_);
    v___x_4836_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_4836_, 0, v_message_4829_);
    v___x_4837_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4837_, 0, v___x_4835_);
    lean_ctor_set(v___x_4837_, 1, v___x_4836_);
    v___x_4838_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_4838_, 0, v___x_4837_);
    lean_ctor_set(v___x_4838_, 1, v___x_4833_);
    v___x_4839_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_4839_, 0, v___x_4838_);
    lean_ctor_set(v___x_4839_, 1, v___x_4833_);
    v___x_4840_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_4840_, 0, v___x_4834_);
    lean_ctor_set(v___x_4840_, 1, v___x_4839_);
    v___x_4841_ = l_Lake_instToJsonLogEntry_toJson___closed__2;
    v___x_4842_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lake_instToJsonLogEntry_toJson_spec__0(v___x_4840_, v___x_4841_);
    v___x_4843_ = l_Lean_Json_mkObj(v___x_4842_);
    lean_dec(v___x_4842_);
    return v___x_4843_;
}
pub unsafe fn l_Lake_instToJsonLogEntry_toJson___boxed(
    mut v_x_4844_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4845_: *mut LeanObject = core::ptr::null_mut();
    v_res_4845_ = l_Lake_instToJsonLogEntry_toJson(v_x_4844_);
    lean_dec_ref(v_x_4844_);
    return v_res_4845_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lake_instFromJsonLogEntry_fromJson_spec__0(
    mut v_j_4848_: *mut LeanObject,
    mut v_k_4849_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4851_: *mut LeanObject = core::ptr::null_mut();
    v___x_4850_ = l_Lean_Json_getObjValD(v_j_4848_, v_k_4849_);
    v___x_4851_ = l_Lake_instFromJsonLogLevel_fromJson(v___x_4850_);
    return v___x_4851_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lake_instFromJsonLogEntry_fromJson_spec__0___boxed(
    mut v_j_4852_: *mut LeanObject,
    mut v_k_4853_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4854_: *mut LeanObject = core::ptr::null_mut();
    v_res_4854_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_instFromJsonLogEntry_fromJson_spec__0(
        v_j_4852_, v_k_4853_,
    );
    lean_dec_ref(v_k_4853_);
    return v_res_4854_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lake_instFromJsonLogEntry_fromJson_spec__1(
    mut v_j_4855_: *mut LeanObject,
    mut v_k_4856_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4858_: *mut LeanObject = core::ptr::null_mut();
    v___x_4857_ = l_Lean_Json_getObjValD(v_j_4855_, v_k_4856_);
    v___x_4858_ = l_Lean_Json_getStr_x3f(v___x_4857_);
    return v___x_4858_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lake_instFromJsonLogEntry_fromJson_spec__1___boxed(
    mut v_j_4859_: *mut LeanObject,
    mut v_k_4860_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4861_: *mut LeanObject = core::ptr::null_mut();
    v_res_4861_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_instFromJsonLogEntry_fromJson_spec__1(
        v_j_4859_, v_k_4860_,
    );
    lean_dec_ref(v_k_4860_);
    return v_res_4861_;
}
pub unsafe fn _init_l_Lake_instFromJsonLogEntry_fromJson___closed__3() -> *mut LeanObject {
    let mut v___x_4867_: u8 = 0;
    let mut v___x_4868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4869_: *mut LeanObject = core::ptr::null_mut();
    v___x_4867_ = 1;
    v___x_4868_ = l_Lake_instFromJsonLogEntry_fromJson___closed__2;
    v___x_4869_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4868_, v___x_4867_);
    return v___x_4869_;
}
pub unsafe fn _init_l_Lake_instFromJsonLogEntry_fromJson___closed__5() -> *mut LeanObject {
    let mut v___x_4871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4873_: *mut LeanObject = core::ptr::null_mut();
    v___x_4871_ = l_Lake_instFromJsonLogEntry_fromJson___closed__4;
    v___x_4872_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instFromJsonLogEntry_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lake_instFromJsonLogEntry_fromJson___closed__3_once),
        _init_l_Lake_instFromJsonLogEntry_fromJson___closed__3,
    );
    v___x_4873_ = lean_string_append(v___x_4872_, v___x_4871_);
    return v___x_4873_;
}
pub unsafe fn _init_l_Lake_instFromJsonLogEntry_fromJson___closed__7() -> *mut LeanObject {
    let mut v___x_4876_: u8 = 0;
    let mut v___x_4877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4878_: *mut LeanObject = core::ptr::null_mut();
    v___x_4876_ = 1;
    v___x_4877_ = l_Lake_instFromJsonLogEntry_fromJson___closed__6;
    v___x_4878_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4877_, v___x_4876_);
    return v___x_4878_;
}
pub unsafe fn _init_l_Lake_instFromJsonLogEntry_fromJson___closed__8() -> *mut LeanObject {
    let mut v___x_4879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4881_: *mut LeanObject = core::ptr::null_mut();
    v___x_4879_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instFromJsonLogEntry_fromJson___closed__7),
        core::ptr::addr_of_mut!(l_Lake_instFromJsonLogEntry_fromJson___closed__7_once),
        _init_l_Lake_instFromJsonLogEntry_fromJson___closed__7,
    );
    v___x_4880_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instFromJsonLogEntry_fromJson___closed__5),
        core::ptr::addr_of_mut!(l_Lake_instFromJsonLogEntry_fromJson___closed__5_once),
        _init_l_Lake_instFromJsonLogEntry_fromJson___closed__5,
    );
    v___x_4881_ = lean_string_append(v___x_4880_, v___x_4879_);
    return v___x_4881_;
}
pub unsafe fn _init_l_Lake_instFromJsonLogEntry_fromJson___closed__10() -> *mut LeanObject {
    let mut v___x_4883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4885_: *mut LeanObject = core::ptr::null_mut();
    v___x_4883_ = l_Lake_instFromJsonLogEntry_fromJson___closed__9;
    v___x_4884_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instFromJsonLogEntry_fromJson___closed__8),
        core::ptr::addr_of_mut!(l_Lake_instFromJsonLogEntry_fromJson___closed__8_once),
        _init_l_Lake_instFromJsonLogEntry_fromJson___closed__8,
    );
    v___x_4885_ = lean_string_append(v___x_4884_, v___x_4883_);
    return v___x_4885_;
}
pub unsafe fn _init_l_Lake_instFromJsonLogEntry_fromJson___closed__12() -> *mut LeanObject {
    let mut v___x_4888_: u8 = 0;
    let mut v___x_4889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4890_: *mut LeanObject = core::ptr::null_mut();
    v___x_4888_ = 1;
    v___x_4889_ = l_Lake_instFromJsonLogEntry_fromJson___closed__11;
    v___x_4890_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4889_, v___x_4888_);
    return v___x_4890_;
}
pub unsafe fn _init_l_Lake_instFromJsonLogEntry_fromJson___closed__13() -> *mut LeanObject {
    let mut v___x_4891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4893_: *mut LeanObject = core::ptr::null_mut();
    v___x_4891_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instFromJsonLogEntry_fromJson___closed__12),
        core::ptr::addr_of_mut!(l_Lake_instFromJsonLogEntry_fromJson___closed__12_once),
        _init_l_Lake_instFromJsonLogEntry_fromJson___closed__12,
    );
    v___x_4892_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instFromJsonLogEntry_fromJson___closed__5),
        core::ptr::addr_of_mut!(l_Lake_instFromJsonLogEntry_fromJson___closed__5_once),
        _init_l_Lake_instFromJsonLogEntry_fromJson___closed__5,
    );
    v___x_4893_ = lean_string_append(v___x_4892_, v___x_4891_);
    return v___x_4893_;
}
pub unsafe fn _init_l_Lake_instFromJsonLogEntry_fromJson___closed__14() -> *mut LeanObject {
    let mut v___x_4894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4896_: *mut LeanObject = core::ptr::null_mut();
    v___x_4894_ = l_Lake_instFromJsonLogEntry_fromJson___closed__9;
    v___x_4895_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instFromJsonLogEntry_fromJson___closed__13),
        core::ptr::addr_of_mut!(l_Lake_instFromJsonLogEntry_fromJson___closed__13_once),
        _init_l_Lake_instFromJsonLogEntry_fromJson___closed__13,
    );
    v___x_4896_ = lean_string_append(v___x_4895_, v___x_4894_);
    return v___x_4896_;
}
pub unsafe fn l_Lake_instFromJsonLogEntry_fromJson(
    mut v_json_4897_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4903_: u8 = 0;
    let mut v___x_4904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4909_: u8 = 0;
    let mut v_a_4910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4913_: u8 = 0;
    let mut v___x_4915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4917_: u8 = 0;
    let mut v_a_4918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4924_: u8 = 0;
    let mut v___x_4925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4930_: u8 = 0;
    let mut v_a_4931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4934_: u8 = 0;
    let mut v___x_4936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4938_: u8 = 0;
    let mut v_a_4939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4942_: u8 = 0;
    let mut v___x_4943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4944_: u8 = 0;
    let mut v___x_4946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4948_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4898_ = l_Lake_instToJsonLogEntry_toJson___closed__0;
                lean_inc(v_json_4897_);
                v___x_4899_ =
                    l_Lean_Json_getObjValAs_x3f___at___00Lake_instFromJsonLogEntry_fromJson_spec__0(
                        v_json_4897_,
                        v___x_4898_,
                    );
                if lean_obj_tag(v___x_4899_) == 0 {
                    lean_dec(v_json_4897_);
                    v_a_4900_ = lean_ctor_get(v___x_4899_, 0);
                    v_isSharedCheck_4909_ = (!lean_is_exclusive(v___x_4899_)) as u8;
                    if v_isSharedCheck_4909_ == 0 {
                        v___x_4902_ = v___x_4899_;
                        v_isShared_4903_ = v_isSharedCheck_4909_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4900_);
                        lean_dec(v___x_4899_);
                        v___x_4902_ = lean_box(0);
                        v_isShared_4903_ = v_isSharedCheck_4909_;
                        state = 1;
                        continue;
                    }
                } else {
                    if lean_obj_tag(v___x_4899_) == 0 {
                        lean_dec(v_json_4897_);
                        v_a_4910_ = lean_ctor_get(v___x_4899_, 0);
                        v_isSharedCheck_4917_ = (!lean_is_exclusive(v___x_4899_)) as u8;
                        if v_isSharedCheck_4917_ == 0 {
                            v___x_4912_ = v___x_4899_;
                            v_isShared_4913_ = v_isSharedCheck_4917_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_4910_);
                            lean_dec(v___x_4899_);
                            v___x_4912_ = lean_box(0);
                            v_isShared_4913_ = v_isSharedCheck_4917_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_4918_ = lean_ctor_get(v___x_4899_, 0);
                        lean_inc(v_a_4918_);
                        lean_dec_ref_known(v___x_4899_, 1);
                        v___x_4919_ = l_Lake_instToJsonLogEntry_toJson___closed__1;
                        v___x_4920_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_instFromJsonLogEntry_fromJson_spec__1(v_json_4897_, v___x_4919_);
                        if lean_obj_tag(v___x_4920_) == 0 {
                            lean_dec(v_a_4918_);
                            v_a_4921_ = lean_ctor_get(v___x_4920_, 0);
                            v_isSharedCheck_4930_ = (!lean_is_exclusive(v___x_4920_)) as u8;
                            if v_isSharedCheck_4930_ == 0 {
                                v___x_4923_ = v___x_4920_;
                                v_isShared_4924_ = v_isSharedCheck_4930_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_4921_);
                                lean_dec(v___x_4920_);
                                v___x_4923_ = lean_box(0);
                                v_isShared_4924_ = v_isSharedCheck_4930_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if lean_obj_tag(v___x_4920_) == 0 {
                                lean_dec(v_a_4918_);
                                v_a_4931_ = lean_ctor_get(v___x_4920_, 0);
                                v_isSharedCheck_4938_ = (!lean_is_exclusive(v___x_4920_)) as u8;
                                if v_isSharedCheck_4938_ == 0 {
                                    v___x_4933_ = v___x_4920_;
                                    v_isShared_4934_ = v_isSharedCheck_4938_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_4931_);
                                    lean_dec(v___x_4920_);
                                    v___x_4933_ = lean_box(0);
                                    v_isShared_4934_ = v_isSharedCheck_4938_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_4939_ = lean_ctor_get(v___x_4920_, 0);
                                v_isSharedCheck_4948_ = (!lean_is_exclusive(v___x_4920_)) as u8;
                                if v_isSharedCheck_4948_ == 0 {
                                    v___x_4941_ = v___x_4920_;
                                    v_isShared_4942_ = v_isSharedCheck_4948_;
                                    state = 9;
                                    continue;
                                } else {
                                    lean_inc(v_a_4939_);
                                    lean_dec(v___x_4920_);
                                    v___x_4941_ = lean_box(0);
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
                v___x_4904_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_instFromJsonLogEntry_fromJson___closed__10),
                    core::ptr::addr_of_mut!(l_Lake_instFromJsonLogEntry_fromJson___closed__10_once),
                    _init_l_Lake_instFromJsonLogEntry_fromJson___closed__10,
                );
                v___x_4905_ = lean_string_append(v___x_4904_, v_a_4900_);
                lean_dec(v_a_4900_);
                if v_isShared_4903_ == 0 {
                    lean_ctor_set(v___x_4902_, 0, v___x_4905_);
                    v___x_4907_ = v___x_4902_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4908_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4908_, 0, v___x_4905_);
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
                    lean_ctor_set_tag(v___x_4912_, 0);
                    v___x_4915_ = v___x_4912_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4916_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4916_, 0, v_a_4910_);
                    v___x_4915_ = v_reuseFailAlloc_4916_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4915_;
            }
            5 => {
                v___x_4925_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_instFromJsonLogEntry_fromJson___closed__14),
                    core::ptr::addr_of_mut!(l_Lake_instFromJsonLogEntry_fromJson___closed__14_once),
                    _init_l_Lake_instFromJsonLogEntry_fromJson___closed__14,
                );
                v___x_4926_ = lean_string_append(v___x_4925_, v_a_4921_);
                lean_dec(v_a_4921_);
                if v_isShared_4924_ == 0 {
                    lean_ctor_set(v___x_4923_, 0, v___x_4926_);
                    v___x_4928_ = v___x_4923_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4929_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4929_, 0, v___x_4926_);
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
                    lean_ctor_set_tag(v___x_4933_, 0);
                    v___x_4936_ = v___x_4933_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4937_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4937_, 0, v_a_4931_);
                    v___x_4936_ = v_reuseFailAlloc_4937_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4936_;
            }
            9 => {
                v___x_4943_ = lean_alloc_ctor(0, 1, (1) as u32);
                lean_ctor_set(v___x_4943_, 0, v_a_4939_);
                v___x_4944_ = (lean_unbox(v_a_4918_) as u8);
                lean_dec(v_a_4918_);
                lean_ctor_set_uint8(
                    v___x_4943_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4944_,
                );
                if v_isShared_4942_ == 0 {
                    lean_ctor_set(v___x_4941_, 0, v___x_4943_);
                    v___x_4946_ = v___x_4941_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4947_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4947_, 0, v___x_4943_);
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
    mut v_self_4953_: *mut LeanObject,
    mut v_useAnsi_4954_: u8,
) -> *mut LeanObject {
    if v_useAnsi_4954_ == 0 {
        let mut v_level_4955_: u8 = 0;
        let mut v_message_4956_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4957_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4958_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4959_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4960_: *mut LeanObject = core::ptr::null_mut();
        v_level_4955_ = lean_ctor_get_uint8(
            v_self_4953_,
            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        );
        v_message_4956_ = lean_ctor_get(v_self_4953_, 0);
        v___x_4957_ = l_Lake_LogLevel_toString(v_level_4955_);
        v___x_4958_ = l_Lake_instFromJsonLogEntry_fromJson___closed__9;
        v___x_4959_ = lean_string_append(v___x_4957_, v___x_4958_);
        v___x_4960_ = lean_string_append(v___x_4959_, v_message_4956_);
        return v___x_4960_;
    } else {
        let mut v_level_4961_: u8 = 0;
        let mut v_message_4962_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4963_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4964_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4965_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4966_: *mut LeanObject = core::ptr::null_mut();
        let mut v_pre_4967_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4968_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4969_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4970_: *mut LeanObject = core::ptr::null_mut();
        v_level_4961_ = lean_ctor_get_uint8(
            v_self_4953_,
            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        );
        v_message_4962_ = lean_ctor_get(v_self_4953_, 0);
        v___x_4963_ = l_Lake_LogLevel_ansiColor(v_level_4961_);
        v___x_4964_ = l_Lake_LogLevel_toString(v_level_4961_);
        v___x_4965_ = l_Lake_LogEntry_toString___closed__0;
        v___x_4966_ = lean_string_append(v___x_4964_, v___x_4965_);
        v_pre_4967_ = l_Lake_Ansi_chalk(v___x_4963_, v___x_4966_);
        lean_dec_ref(v___x_4966_);
        lean_dec_ref(v___x_4963_);
        v___x_4968_ = l_Lake_LogEntry_toString___closed__1;
        v___x_4969_ = lean_string_append(v_pre_4967_, v___x_4968_);
        v___x_4970_ = lean_string_append(v___x_4969_, v_message_4962_);
        return v___x_4970_;
    }
}
pub unsafe fn l_Lake_LogEntry_toString___boxed(
    mut v_self_4971_: *mut LeanObject,
    mut v_useAnsi_4972_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_useAnsi_boxed_4973_: u8 = 0;
    let mut v_res_4974_: *mut LeanObject = core::ptr::null_mut();
    v_useAnsi_boxed_4973_ = (lean_unbox(v_useAnsi_4972_) as u8);
    v_res_4974_ = l_Lake_LogEntry_toString(v_self_4971_, v_useAnsi_boxed_4973_);
    lean_dec_ref(v_self_4971_);
    return v_res_4974_;
}
pub unsafe fn l_Lake_instToStringLogEntry___lam__0(
    mut v_self_4975_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4976_: u8 = 0;
    let mut v___x_4977_: *mut LeanObject = core::ptr::null_mut();
    v___x_4976_ = 0;
    v___x_4977_ = l_Lake_LogEntry_toString(v_self_4975_, v___x_4976_);
    return v___x_4977_;
}
pub unsafe fn l_Lake_instToStringLogEntry___lam__0___boxed(
    mut v_self_4978_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4979_: *mut LeanObject = core::ptr::null_mut();
    v_res_4979_ = l_Lake_instToStringLogEntry___lam__0(v_self_4978_);
    lean_dec_ref(v_self_4978_);
    return v_res_4979_;
}
pub unsafe fn l_Lake_LogEntry_trace(mut v_message_4982_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_4983_: u8 = 0;
    let mut v___x_4984_: *mut LeanObject = core::ptr::null_mut();
    v___x_4983_ = 0;
    v___x_4984_ = lean_alloc_ctor(0, 1, (1) as u32);
    lean_ctor_set(v___x_4984_, 0, v_message_4982_);
    lean_ctor_set_uint8(
        v___x_4984_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_4983_,
    );
    return v___x_4984_;
}
pub unsafe fn l_Lake_LogEntry_info(mut v_message_4985_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_4986_: u8 = 0;
    let mut v___x_4987_: *mut LeanObject = core::ptr::null_mut();
    v___x_4986_ = 1;
    v___x_4987_ = lean_alloc_ctor(0, 1, (1) as u32);
    lean_ctor_set(v___x_4987_, 0, v_message_4985_);
    lean_ctor_set_uint8(
        v___x_4987_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_4986_,
    );
    return v___x_4987_;
}
pub unsafe fn l_Lake_LogEntry_warning(mut v_message_4988_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_4989_: u8 = 0;
    let mut v___x_4990_: *mut LeanObject = core::ptr::null_mut();
    v___x_4989_ = 2;
    v___x_4990_ = lean_alloc_ctor(0, 1, (1) as u32);
    lean_ctor_set(v___x_4990_, 0, v_message_4988_);
    lean_ctor_set_uint8(
        v___x_4990_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_4989_,
    );
    return v___x_4990_;
}
pub unsafe fn l_Lake_LogEntry_error(mut v_message_4991_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_4992_: u8 = 0;
    let mut v___x_4993_: *mut LeanObject = core::ptr::null_mut();
    v___x_4992_ = 3;
    v___x_4993_ = lean_alloc_ctor(0, 1, (1) as u32);
    lean_ctor_set(v___x_4993_, 0, v_message_4991_);
    lean_ctor_set_uint8(
        v___x_4993_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_4992_,
    );
    return v___x_4993_;
}
pub unsafe fn l_Lake_LogEntry_ofSerialMessage(mut v_msg_4995_: *mut LeanObject) -> *mut LeanObject {
    let mut v_toBaseMessage_4996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_4997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_severity_4999_: u8 = 0;
    let mut v_caption_5000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_5001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5004_: u8 = 0;
    let mut v___x_5005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_5012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_5013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5015_: u8 = 0;
    let mut v___x_5016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5019_: u8 = 0;
    let mut v___x_5020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5029_: u8 = 0;
    let mut v_unused_5030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5035_: u8 = 0;
    let mut v___x_5036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_5040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_5041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_5042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5045_: u8 = 0;
    let mut v_unused_5046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5048_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toBaseMessage_4996_ = lean_ctor_get(v_msg_4995_, 0);
                lean_inc_ref(v_toBaseMessage_4996_);
                lean_dec_ref(v_msg_4995_);
                v_fileName_4997_ = lean_ctor_get(v_toBaseMessage_4996_, 0);
                lean_inc_ref(v_fileName_4997_);
                v_pos_4998_ = lean_ctor_get(v_toBaseMessage_4996_, 1);
                lean_inc_ref(v_pos_4998_);
                v_severity_4999_ = lean_ctor_get_uint8(
                    v_toBaseMessage_4996_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                );
                v_caption_5000_ = lean_ctor_get(v_toBaseMessage_4996_, 3);
                lean_inc_ref(v_caption_5000_);
                v_data_5001_ = lean_ctor_get(v_toBaseMessage_4996_, 4);
                lean_inc(v_data_5001_);
                lean_dec_ref(v_toBaseMessage_4996_);
                v___x_5008_ = lean_unsigned_to_nat(0);
                v___x_5009_ = lean_string_utf8_byte_size(v_caption_5000_);
                v___x_5010_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_5010_, 0, v_caption_5000_);
                lean_ctor_set(v___x_5010_, 1, v___x_5008_);
                lean_ctor_set(v___x_5010_, 2, v___x_5009_);
                v___x_5011_ = l_String_Slice_trimAscii(v___x_5010_);
                v_startInclusive_5012_ = lean_ctor_get(v___x_5011_, 1);
                lean_inc(v_startInclusive_5012_);
                v_endExclusive_5013_ = lean_ctor_get(v___x_5011_, 2);
                lean_inc(v_endExclusive_5013_);
                v___x_5014_ = lean_nat_sub(v_endExclusive_5013_, v_startInclusive_5012_);
                lean_dec(v_startInclusive_5012_);
                lean_dec(v_endExclusive_5013_);
                v___x_5015_ = lean_nat_dec_eq(v___x_5014_, v___x_5008_);
                lean_dec(v___x_5014_);
                if v___x_5015_ == 0 {
                    v___x_5016_ = l_String_Slice_toString(v___x_5011_);
                    v_isSharedCheck_5029_ = (!lean_is_exclusive(v___x_5011_)) as u8;
                    if v_isSharedCheck_5029_ == 0 {
                        v_unused_5030_ = lean_ctor_get(v___x_5011_, 2);
                        lean_dec(v_unused_5030_);
                        v_unused_5031_ = lean_ctor_get(v___x_5011_, 1);
                        lean_dec(v_unused_5031_);
                        v_unused_5032_ = lean_ctor_get(v___x_5011_, 0);
                        lean_dec(v_unused_5032_);
                        v___x_5018_ = v___x_5011_;
                        v_isShared_5019_ = v_isSharedCheck_5029_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v___x_5011_);
                        v___x_5018_ = lean_box(0);
                        v_isShared_5019_ = v_isSharedCheck_5029_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_isSharedCheck_5045_ = (!lean_is_exclusive(v___x_5011_)) as u8;
                    if v_isSharedCheck_5045_ == 0 {
                        v_unused_5046_ = lean_ctor_get(v___x_5011_, 2);
                        lean_dec(v_unused_5046_);
                        v_unused_5047_ = lean_ctor_get(v___x_5011_, 1);
                        lean_dec(v_unused_5047_);
                        v_unused_5048_ = lean_ctor_get(v___x_5011_, 0);
                        lean_dec(v_unused_5048_);
                        v___x_5034_ = v___x_5011_;
                        v_isShared_5035_ = v_isSharedCheck_5045_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v___x_5011_);
                        v___x_5034_ = lean_box(0);
                        v_isShared_5035_ = v_isSharedCheck_5045_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5004_ = l_Lake_LogLevel_ofMessageSeverity(v_severity_4999_);
                v___x_5005_ = lean_box(0);
                v___x_5006_ = l_Lean_mkErrorStringWithPos(
                    v_fileName_4997_,
                    v_pos_4998_,
                    v___y_5003_,
                    v___x_5005_,
                    v___x_5005_,
                    v___x_5005_,
                );
                lean_dec_ref(v___y_5003_);
                v___x_5007_ = lean_alloc_ctor(0, 1, (1) as u32);
                lean_ctor_set(v___x_5007_, 0, v___x_5006_);
                lean_ctor_set_uint8(
                    v___x_5007_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_5004_,
                );
                return v___x_5007_;
            }
            2 => {
                v___x_5020_ = l_Lake_LogEntry_ofSerialMessage___closed__0;
                v___x_5021_ = lean_string_append(v___x_5016_, v___x_5020_);
                v___x_5022_ = lean_string_utf8_byte_size(v_data_5001_);
                if v_isShared_5019_ == 0 {
                    lean_ctor_set(v___x_5018_, 2, v___x_5022_);
                    lean_ctor_set(v___x_5018_, 1, v___x_5008_);
                    lean_ctor_set(v___x_5018_, 0, v_data_5001_);
                    v___x_5024_ = v___x_5018_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5028_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5028_, 0, v_data_5001_);
                    lean_ctor_set(v_reuseFailAlloc_5028_, 1, v___x_5008_);
                    lean_ctor_set(v_reuseFailAlloc_5028_, 2, v___x_5022_);
                    v___x_5024_ = v_reuseFailAlloc_5028_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5025_ = l_String_Slice_trimAscii(v___x_5024_);
                v___x_5026_ = l_String_Slice_toString(v___x_5025_);
                lean_dec_ref(v___x_5025_);
                v___x_5027_ = lean_string_append(v___x_5021_, v___x_5026_);
                lean_dec_ref(v___x_5026_);
                v___y_5003_ = v___x_5027_;
                state = 1;
                continue;
            }
            4 => {
                v___x_5036_ = lean_string_utf8_byte_size(v_data_5001_);
                if v_isShared_5035_ == 0 {
                    lean_ctor_set(v___x_5034_, 2, v___x_5036_);
                    lean_ctor_set(v___x_5034_, 1, v___x_5008_);
                    lean_ctor_set(v___x_5034_, 0, v_data_5001_);
                    v___x_5038_ = v___x_5034_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5044_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5044_, 0, v_data_5001_);
                    lean_ctor_set(v_reuseFailAlloc_5044_, 1, v___x_5008_);
                    lean_ctor_set(v_reuseFailAlloc_5044_, 2, v___x_5036_);
                    v___x_5038_ = v_reuseFailAlloc_5044_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5039_ = l_String_Slice_trimAscii(v___x_5038_);
                v_str_5040_ = lean_ctor_get(v___x_5039_, 0);
                lean_inc_ref(v_str_5040_);
                v_startInclusive_5041_ = lean_ctor_get(v___x_5039_, 1);
                lean_inc(v_startInclusive_5041_);
                v_endExclusive_5042_ = lean_ctor_get(v___x_5039_, 2);
                lean_inc(v_endExclusive_5042_);
                lean_dec_ref(v___x_5039_);
                v___x_5043_ = lean_string_utf8_extract(
                    v_str_5040_,
                    v_startInclusive_5041_,
                    v_endExclusive_5042_,
                );
                lean_dec(v_endExclusive_5042_);
                lean_dec(v_startInclusive_5041_);
                lean_dec_ref(v_str_5040_);
                v___y_5003_ = v___x_5043_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LogEntry_ofMessage(mut v_msg_5049_: *mut LeanObject) -> *mut LeanObject {
    let mut v_fileName_5051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_5052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_severity_5053_: u8 = 0;
    let mut v_caption_5054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_5055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5059_: u8 = 0;
    let mut v___x_5060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_5067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_5068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5070_: u8 = 0;
    let mut v___x_5071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5074_: u8 = 0;
    let mut v___x_5075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5084_: u8 = 0;
    let mut v_unused_5085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5090_: u8 = 0;
    let mut v___x_5091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_5095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_5096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_5097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5100_: u8 = 0;
    let mut v_unused_5101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5103_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_5051_ = lean_ctor_get(v_msg_5049_, 0);
                lean_inc_ref(v_fileName_5051_);
                v_pos_5052_ = lean_ctor_get(v_msg_5049_, 1);
                lean_inc_ref(v_pos_5052_);
                v_severity_5053_ = lean_ctor_get_uint8(
                    v_msg_5049_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                );
                v_caption_5054_ = lean_ctor_get(v_msg_5049_, 3);
                lean_inc_ref(v_caption_5054_);
                v_data_5055_ = lean_ctor_get(v_msg_5049_, 4);
                lean_inc(v_data_5055_);
                lean_dec_ref(v_msg_5049_);
                v___x_5056_ = l_Lean_MessageData_toString(v_data_5055_);
                v___x_5063_ = lean_unsigned_to_nat(0);
                v___x_5064_ = lean_string_utf8_byte_size(v_caption_5054_);
                v___x_5065_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_5065_, 0, v_caption_5054_);
                lean_ctor_set(v___x_5065_, 1, v___x_5063_);
                lean_ctor_set(v___x_5065_, 2, v___x_5064_);
                v___x_5066_ = l_String_Slice_trimAscii(v___x_5065_);
                v_startInclusive_5067_ = lean_ctor_get(v___x_5066_, 1);
                lean_inc(v_startInclusive_5067_);
                v_endExclusive_5068_ = lean_ctor_get(v___x_5066_, 2);
                lean_inc(v_endExclusive_5068_);
                v___x_5069_ = lean_nat_sub(v_endExclusive_5068_, v_startInclusive_5067_);
                lean_dec(v_startInclusive_5067_);
                lean_dec(v_endExclusive_5068_);
                v___x_5070_ = lean_nat_dec_eq(v___x_5069_, v___x_5063_);
                lean_dec(v___x_5069_);
                if v___x_5070_ == 0 {
                    v___x_5071_ = l_String_Slice_toString(v___x_5066_);
                    v_isSharedCheck_5084_ = (!lean_is_exclusive(v___x_5066_)) as u8;
                    if v_isSharedCheck_5084_ == 0 {
                        v_unused_5085_ = lean_ctor_get(v___x_5066_, 2);
                        lean_dec(v_unused_5085_);
                        v_unused_5086_ = lean_ctor_get(v___x_5066_, 1);
                        lean_dec(v_unused_5086_);
                        v_unused_5087_ = lean_ctor_get(v___x_5066_, 0);
                        lean_dec(v_unused_5087_);
                        v___x_5073_ = v___x_5066_;
                        v_isShared_5074_ = v_isSharedCheck_5084_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v___x_5066_);
                        v___x_5073_ = lean_box(0);
                        v_isShared_5074_ = v_isSharedCheck_5084_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_isSharedCheck_5100_ = (!lean_is_exclusive(v___x_5066_)) as u8;
                    if v_isSharedCheck_5100_ == 0 {
                        v_unused_5101_ = lean_ctor_get(v___x_5066_, 2);
                        lean_dec(v_unused_5101_);
                        v_unused_5102_ = lean_ctor_get(v___x_5066_, 1);
                        lean_dec(v_unused_5102_);
                        v_unused_5103_ = lean_ctor_get(v___x_5066_, 0);
                        lean_dec(v_unused_5103_);
                        v___x_5089_ = v___x_5066_;
                        v_isShared_5090_ = v_isSharedCheck_5100_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v___x_5066_);
                        v___x_5089_ = lean_box(0);
                        v_isShared_5090_ = v_isSharedCheck_5100_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5059_ = l_Lake_LogLevel_ofMessageSeverity(v_severity_5053_);
                v___x_5060_ = lean_box(0);
                v___x_5061_ = l_Lean_mkErrorStringWithPos(
                    v_fileName_5051_,
                    v_pos_5052_,
                    v___y_5058_,
                    v___x_5060_,
                    v___x_5060_,
                    v___x_5060_,
                );
                lean_dec_ref(v___y_5058_);
                v___x_5062_ = lean_alloc_ctor(0, 1, (1) as u32);
                lean_ctor_set(v___x_5062_, 0, v___x_5061_);
                lean_ctor_set_uint8(
                    v___x_5062_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_5059_,
                );
                return v___x_5062_;
            }
            2 => {
                v___x_5075_ = l_Lake_LogEntry_ofSerialMessage___closed__0;
                v___x_5076_ = lean_string_append(v___x_5071_, v___x_5075_);
                v___x_5077_ = lean_string_utf8_byte_size(v___x_5056_);
                if v_isShared_5074_ == 0 {
                    lean_ctor_set(v___x_5073_, 2, v___x_5077_);
                    lean_ctor_set(v___x_5073_, 1, v___x_5063_);
                    lean_ctor_set(v___x_5073_, 0, v___x_5056_);
                    v___x_5079_ = v___x_5073_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5083_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5083_, 0, v___x_5056_);
                    lean_ctor_set(v_reuseFailAlloc_5083_, 1, v___x_5063_);
                    lean_ctor_set(v_reuseFailAlloc_5083_, 2, v___x_5077_);
                    v___x_5079_ = v_reuseFailAlloc_5083_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5080_ = l_String_Slice_trimAscii(v___x_5079_);
                v___x_5081_ = l_String_Slice_toString(v___x_5080_);
                lean_dec_ref(v___x_5080_);
                v___x_5082_ = lean_string_append(v___x_5076_, v___x_5081_);
                lean_dec_ref(v___x_5081_);
                v___y_5058_ = v___x_5082_;
                state = 1;
                continue;
            }
            4 => {
                v___x_5091_ = lean_string_utf8_byte_size(v___x_5056_);
                if v_isShared_5090_ == 0 {
                    lean_ctor_set(v___x_5089_, 2, v___x_5091_);
                    lean_ctor_set(v___x_5089_, 1, v___x_5063_);
                    lean_ctor_set(v___x_5089_, 0, v___x_5056_);
                    v___x_5093_ = v___x_5089_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5099_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5099_, 0, v___x_5056_);
                    lean_ctor_set(v_reuseFailAlloc_5099_, 1, v___x_5063_);
                    lean_ctor_set(v_reuseFailAlloc_5099_, 2, v___x_5091_);
                    v___x_5093_ = v_reuseFailAlloc_5099_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5094_ = l_String_Slice_trimAscii(v___x_5093_);
                v_str_5095_ = lean_ctor_get(v___x_5094_, 0);
                lean_inc_ref(v_str_5095_);
                v_startInclusive_5096_ = lean_ctor_get(v___x_5094_, 1);
                lean_inc(v_startInclusive_5096_);
                v_endExclusive_5097_ = lean_ctor_get(v___x_5094_, 2);
                lean_inc(v_endExclusive_5097_);
                lean_dec_ref(v___x_5094_);
                v___x_5098_ = lean_string_utf8_extract(
                    v_str_5095_,
                    v_startInclusive_5096_,
                    v_endExclusive_5097_,
                );
                lean_dec(v_endExclusive_5097_);
                lean_dec(v_startInclusive_5096_);
                lean_dec_ref(v_str_5095_);
                v___y_5058_ = v___x_5098_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LogEntry_ofMessage___boxed(
    mut v_msg_5104_: *mut LeanObject,
    mut v_a_5105_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5106_: *mut LeanObject = core::ptr::null_mut();
    v_res_5106_ = l_Lake_LogEntry_ofMessage(v_msg_5104_);
    return v_res_5106_;
}
pub unsafe fn l_Lake_logVerbose___redArg(
    mut v_inst_5107_: *mut LeanObject,
    mut v_message_5108_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5109_: u8 = 0;
    let mut v___x_5110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5111_: *mut LeanObject = core::ptr::null_mut();
    v___x_5109_ = 0;
    v___x_5110_ = lean_alloc_ctor(0, 1, (1) as u32);
    lean_ctor_set(v___x_5110_, 0, v_message_5108_);
    lean_ctor_set_uint8(
        v___x_5110_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_5109_,
    );
    v___x_5111_ = lean_apply_1(v_inst_5107_, v___x_5110_);
    return v___x_5111_;
}
pub unsafe fn l_Lake_logVerbose(
    mut v_m_5112_: *mut LeanObject,
    mut v_inst_5113_: *mut LeanObject,
    mut v_inst_5114_: *mut LeanObject,
    mut v_message_5115_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5116_: u8 = 0;
    let mut v___x_5117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5118_: *mut LeanObject = core::ptr::null_mut();
    v___x_5116_ = 0;
    v___x_5117_ = lean_alloc_ctor(0, 1, (1) as u32);
    lean_ctor_set(v___x_5117_, 0, v_message_5115_);
    lean_ctor_set_uint8(
        v___x_5117_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_5116_,
    );
    v___x_5118_ = lean_apply_1(v_inst_5114_, v___x_5117_);
    return v___x_5118_;
}
pub unsafe fn l_Lake_logVerbose___boxed(
    mut v_m_5119_: *mut LeanObject,
    mut v_inst_5120_: *mut LeanObject,
    mut v_inst_5121_: *mut LeanObject,
    mut v_message_5122_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5123_: *mut LeanObject = core::ptr::null_mut();
    v_res_5123_ = l_Lake_logVerbose(v_m_5119_, v_inst_5120_, v_inst_5121_, v_message_5122_);
    lean_dec_ref(v_inst_5120_);
    return v_res_5123_;
}
pub unsafe fn l_Lake_logInfo___redArg(
    mut v_inst_5124_: *mut LeanObject,
    mut v_message_5125_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5126_: u8 = 0;
    let mut v___x_5127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5128_: *mut LeanObject = core::ptr::null_mut();
    v___x_5126_ = 1;
    v___x_5127_ = lean_alloc_ctor(0, 1, (1) as u32);
    lean_ctor_set(v___x_5127_, 0, v_message_5125_);
    lean_ctor_set_uint8(
        v___x_5127_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_5126_,
    );
    v___x_5128_ = lean_apply_1(v_inst_5124_, v___x_5127_);
    return v___x_5128_;
}
pub unsafe fn l_Lake_logInfo(
    mut v_m_5129_: *mut LeanObject,
    mut v_inst_5130_: *mut LeanObject,
    mut v_inst_5131_: *mut LeanObject,
    mut v_message_5132_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5133_: u8 = 0;
    let mut v___x_5134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5135_: *mut LeanObject = core::ptr::null_mut();
    v___x_5133_ = 1;
    v___x_5134_ = lean_alloc_ctor(0, 1, (1) as u32);
    lean_ctor_set(v___x_5134_, 0, v_message_5132_);
    lean_ctor_set_uint8(
        v___x_5134_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_5133_,
    );
    v___x_5135_ = lean_apply_1(v_inst_5131_, v___x_5134_);
    return v___x_5135_;
}
pub unsafe fn l_Lake_logInfo___boxed(
    mut v_m_5136_: *mut LeanObject,
    mut v_inst_5137_: *mut LeanObject,
    mut v_inst_5138_: *mut LeanObject,
    mut v_message_5139_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5140_: *mut LeanObject = core::ptr::null_mut();
    v_res_5140_ = l_Lake_logInfo(v_m_5136_, v_inst_5137_, v_inst_5138_, v_message_5139_);
    lean_dec_ref(v_inst_5137_);
    return v_res_5140_;
}
pub unsafe fn l_Lake_logWarning___redArg(
    mut v_inst_5141_: *mut LeanObject,
    mut v_message_5142_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5143_: u8 = 0;
    let mut v___x_5144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5145_: *mut LeanObject = core::ptr::null_mut();
    v___x_5143_ = 2;
    v___x_5144_ = lean_alloc_ctor(0, 1, (1) as u32);
    lean_ctor_set(v___x_5144_, 0, v_message_5142_);
    lean_ctor_set_uint8(
        v___x_5144_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_5143_,
    );
    v___x_5145_ = lean_apply_1(v_inst_5141_, v___x_5144_);
    return v___x_5145_;
}
pub unsafe fn l_Lake_logWarning(
    mut v_m_5146_: *mut LeanObject,
    mut v_inst_5147_: *mut LeanObject,
    mut v_message_5148_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5149_: u8 = 0;
    let mut v___x_5150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5151_: *mut LeanObject = core::ptr::null_mut();
    v___x_5149_ = 2;
    v___x_5150_ = lean_alloc_ctor(0, 1, (1) as u32);
    lean_ctor_set(v___x_5150_, 0, v_message_5148_);
    lean_ctor_set_uint8(
        v___x_5150_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_5149_,
    );
    v___x_5151_ = lean_apply_1(v_inst_5147_, v___x_5150_);
    return v___x_5151_;
}
pub unsafe fn l_Lake_logError___redArg(
    mut v_inst_5152_: *mut LeanObject,
    mut v_message_5153_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5154_: u8 = 0;
    let mut v___x_5155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5156_: *mut LeanObject = core::ptr::null_mut();
    v___x_5154_ = 3;
    v___x_5155_ = lean_alloc_ctor(0, 1, (1) as u32);
    lean_ctor_set(v___x_5155_, 0, v_message_5153_);
    lean_ctor_set_uint8(
        v___x_5155_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_5154_,
    );
    v___x_5156_ = lean_apply_1(v_inst_5152_, v___x_5155_);
    return v___x_5156_;
}
pub unsafe fn l_Lake_logError(
    mut v_m_5157_: *mut LeanObject,
    mut v_inst_5158_: *mut LeanObject,
    mut v_message_5159_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5160_: u8 = 0;
    let mut v___x_5161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5162_: *mut LeanObject = core::ptr::null_mut();
    v___x_5160_ = 3;
    v___x_5161_ = lean_alloc_ctor(0, 1, (1) as u32);
    lean_ctor_set(v___x_5161_, 0, v_message_5159_);
    lean_ctor_set_uint8(
        v___x_5161_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_5160_,
    );
    v___x_5162_ = lean_apply_1(v_inst_5158_, v___x_5161_);
    return v___x_5162_;
}
pub unsafe fn l_Lake_logSerialMessage___redArg(
    mut v_msg_5163_: *mut LeanObject,
    mut v_inst_5164_: *mut LeanObject,
    mut v_inst_5165_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBaseMessage_5166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSilent_5167_: u8 = 0;
    v_toBaseMessage_5166_ = lean_ctor_get(v_msg_5163_, 0);
    v_isSilent_5167_ = lean_ctor_get_uint8(
        v_toBaseMessage_5166_,
        (core::mem::size_of::<*mut LeanObject>() * 5 + 2) as u32,
    );
    if v_isSilent_5167_ == 0 {
        let mut v___x_5168_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5169_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_inst_5164_);
        v___x_5168_ = l_Lake_LogEntry_ofSerialMessage(v_msg_5163_);
        v___x_5169_ = lean_apply_1(v_inst_5165_, v___x_5168_);
        return v___x_5169_;
    } else {
        let mut v_toApplicative_5170_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_5171_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5172_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5173_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_inst_5165_);
        lean_dec_ref(v_msg_5163_);
        v_toApplicative_5170_ = lean_ctor_get(v_inst_5164_, 0);
        lean_inc_ref(v_toApplicative_5170_);
        lean_dec_ref(v_inst_5164_);
        v_toPure_5171_ = lean_ctor_get(v_toApplicative_5170_, 1);
        lean_inc(v_toPure_5171_);
        lean_dec_ref(v_toApplicative_5170_);
        v___x_5172_ = lean_box(0);
        v___x_5173_ = lean_apply_2(v_toPure_5171_, lean_box(0), v___x_5172_);
        return v___x_5173_;
    }
}
pub unsafe fn l_Lake_logSerialMessage(
    mut v_m_5174_: *mut LeanObject,
    mut v_msg_5175_: *mut LeanObject,
    mut v_inst_5176_: *mut LeanObject,
    mut v_inst_5177_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBaseMessage_5178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSilent_5179_: u8 = 0;
    v_toBaseMessage_5178_ = lean_ctor_get(v_msg_5175_, 0);
    v_isSilent_5179_ = lean_ctor_get_uint8(
        v_toBaseMessage_5178_,
        (core::mem::size_of::<*mut LeanObject>() * 5 + 2) as u32,
    );
    if v_isSilent_5179_ == 0 {
        let mut v___x_5180_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5181_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_inst_5176_);
        v___x_5180_ = l_Lake_LogEntry_ofSerialMessage(v_msg_5175_);
        v___x_5181_ = lean_apply_1(v_inst_5177_, v___x_5180_);
        return v___x_5181_;
    } else {
        let mut v_toApplicative_5182_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_5183_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5184_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5185_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_inst_5177_);
        lean_dec_ref(v_msg_5175_);
        v_toApplicative_5182_ = lean_ctor_get(v_inst_5176_, 0);
        lean_inc_ref(v_toApplicative_5182_);
        lean_dec_ref(v_inst_5176_);
        v_toPure_5183_ = lean_ctor_get(v_toApplicative_5182_, 1);
        lean_inc(v_toPure_5183_);
        lean_dec_ref(v_toApplicative_5182_);
        v___x_5184_ = lean_box(0);
        v___x_5185_ = lean_apply_2(v_toPure_5183_, lean_box(0), v___x_5184_);
        return v___x_5185_;
    }
}
pub unsafe fn l_Lake_logMessage___redArg___lam__0(
    mut v_inst_5186_: *mut LeanObject,
    mut v_____do__lift_5187_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5188_: *mut LeanObject = core::ptr::null_mut();
    v___x_5188_ = lean_apply_1(v_inst_5186_, v_____do__lift_5187_);
    return v___x_5188_;
}
pub unsafe fn l_Lake_logMessage___redArg(
    mut v_msg_5189_: *mut LeanObject,
    mut v_inst_5190_: *mut LeanObject,
    mut v_inst_5191_: *mut LeanObject,
    mut v_inst_5192_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isSilent_5193_: u8 = 0;
    v_isSilent_5193_ = lean_ctor_get_uint8(
        v_msg_5189_,
        (core::mem::size_of::<*mut LeanObject>() * 5 + 2) as u32,
    );
    if v_isSilent_5193_ == 0 {
        let mut v_toBind_5194_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_5195_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5196_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5197_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5198_: *mut LeanObject = core::ptr::null_mut();
        v_toBind_5194_ = lean_ctor_get(v_inst_5190_, 1);
        lean_inc(v_toBind_5194_);
        lean_dec_ref(v_inst_5190_);
        v___f_5195_ = lean_alloc_closure(
            l_Lake_logMessage___redArg___lam__0 as *mut core::ffi::c_void,
            2,
            1,
        );
        lean_closure_set(v___f_5195_, 0, v_inst_5191_);
        v___x_5196_ = lean_alloc_closure(
            l_Lake_LogEntry_ofMessage___boxed as *mut core::ffi::c_void,
            2,
            1,
        );
        lean_closure_set(v___x_5196_, 0, v_msg_5189_);
        v___x_5197_ = lean_apply_2(v_inst_5192_, lean_box(0), v___x_5196_);
        v___x_5198_ = lean_apply_4(
            v_toBind_5194_,
            lean_box(0),
            lean_box(0),
            v___x_5197_,
            v___f_5195_,
        );
        return v___x_5198_;
    } else {
        let mut v_toApplicative_5199_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_5200_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5201_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5202_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_inst_5192_);
        lean_dec(v_inst_5191_);
        lean_dec_ref(v_msg_5189_);
        v_toApplicative_5199_ = lean_ctor_get(v_inst_5190_, 0);
        lean_inc_ref(v_toApplicative_5199_);
        lean_dec_ref(v_inst_5190_);
        v_toPure_5200_ = lean_ctor_get(v_toApplicative_5199_, 1);
        lean_inc(v_toPure_5200_);
        lean_dec_ref(v_toApplicative_5199_);
        v___x_5201_ = lean_box(0);
        v___x_5202_ = lean_apply_2(v_toPure_5200_, lean_box(0), v___x_5201_);
        return v___x_5202_;
    }
}
pub unsafe fn l_Lake_logMessage(
    mut v_m_5203_: *mut LeanObject,
    mut v_msg_5204_: *mut LeanObject,
    mut v_inst_5205_: *mut LeanObject,
    mut v_inst_5206_: *mut LeanObject,
    mut v_inst_5207_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isSilent_5208_: u8 = 0;
    v_isSilent_5208_ = lean_ctor_get_uint8(
        v_msg_5204_,
        (core::mem::size_of::<*mut LeanObject>() * 5 + 2) as u32,
    );
    if v_isSilent_5208_ == 0 {
        let mut v_toBind_5209_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_5210_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5211_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5212_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5213_: *mut LeanObject = core::ptr::null_mut();
        v_toBind_5209_ = lean_ctor_get(v_inst_5205_, 1);
        lean_inc(v_toBind_5209_);
        lean_dec_ref(v_inst_5205_);
        v___f_5210_ = lean_alloc_closure(
            l_Lake_logMessage___redArg___lam__0 as *mut core::ffi::c_void,
            2,
            1,
        );
        lean_closure_set(v___f_5210_, 0, v_inst_5206_);
        v___x_5211_ = lean_alloc_closure(
            l_Lake_LogEntry_ofMessage___boxed as *mut core::ffi::c_void,
            2,
            1,
        );
        lean_closure_set(v___x_5211_, 0, v_msg_5204_);
        v___x_5212_ = lean_apply_2(v_inst_5207_, lean_box(0), v___x_5211_);
        v___x_5213_ = lean_apply_4(
            v_toBind_5209_,
            lean_box(0),
            lean_box(0),
            v___x_5212_,
            v___f_5210_,
        );
        return v___x_5213_;
    } else {
        let mut v_toApplicative_5214_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_5215_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5216_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5217_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_inst_5207_);
        lean_dec(v_inst_5206_);
        lean_dec_ref(v_msg_5204_);
        v_toApplicative_5214_ = lean_ctor_get(v_inst_5205_, 0);
        lean_inc_ref(v_toApplicative_5214_);
        lean_dec_ref(v_inst_5205_);
        v_toPure_5215_ = lean_ctor_get(v_toApplicative_5214_, 1);
        lean_inc(v_toPure_5215_);
        lean_dec_ref(v_toApplicative_5214_);
        v___x_5216_ = lean_box(0);
        v___x_5217_ = lean_apply_2(v_toPure_5215_, lean_box(0), v___x_5216_);
        return v___x_5217_;
    }
}
pub unsafe fn l_Lake_logToStream(
    mut v_e_5218_: *mut LeanObject,
    mut v_out_5219_: *mut LeanObject,
    mut v_minLv_5220_: u8,
    mut v_useAnsi_5221_: u8,
) -> *mut LeanObject {
    let mut v_level_5223_: u8 = 0;
    let mut v___x_5224_: u8 = 0;
    v_level_5223_ = lean_ctor_get_uint8(
        v_e_5218_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
    );
    v___x_5224_ = l_Lake_instOrdLogLevel_ord(v_minLv_5220_, v_level_5223_);
    if v___x_5224_ == 2 {
        let mut v___x_5225_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_out_5219_);
        v___x_5225_ = lean_box(0);
        return v___x_5225_;
    } else {
        let mut v___x_5226_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5227_: *mut LeanObject = core::ptr::null_mut();
        v___x_5226_ = l_Lake_LogEntry_toString(v_e_5218_, v_useAnsi_5221_);
        v___x_5227_ = l_IO_FS_Stream_putStrLn(v_out_5219_, v___x_5226_);
        if lean_obj_tag(v___x_5227_) == 0 {
            let mut v_a_5228_: *mut LeanObject = core::ptr::null_mut();
            v_a_5228_ = lean_ctor_get(v___x_5227_, 0);
            lean_inc(v_a_5228_);
            lean_dec_ref_known(v___x_5227_, 1);
            return v_a_5228_;
        } else {
            let mut v___x_5229_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref_known(v___x_5227_, 1);
            v___x_5229_ = lean_box(0);
            return v___x_5229_;
        }
    }
}
pub unsafe fn l_Lake_logToStream___boxed(
    mut v_e_5230_: *mut LeanObject,
    mut v_out_5231_: *mut LeanObject,
    mut v_minLv_5232_: *mut LeanObject,
    mut v_useAnsi_5233_: *mut LeanObject,
    mut v_a_5234_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_minLv_boxed_5235_: u8 = 0;
    let mut v_useAnsi_boxed_5236_: u8 = 0;
    let mut v_res_5237_: *mut LeanObject = core::ptr::null_mut();
    v_minLv_boxed_5235_ = (lean_unbox(v_minLv_5232_) as u8);
    v_useAnsi_boxed_5236_ = (lean_unbox(v_useAnsi_5233_) as u8);
    v_res_5237_ = l_Lake_logToStream(
        v_e_5230_,
        v_out_5231_,
        v_minLv_boxed_5235_,
        v_useAnsi_boxed_5236_,
    );
    lean_dec_ref(v_e_5230_);
    return v_res_5237_;
}
pub unsafe fn l_Lake_MonadLog_nop___redArg___lam__0(
    mut v_inst_5238_: *mut LeanObject,
    mut v_x_5239_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5241_: *mut LeanObject = core::ptr::null_mut();
    v___x_5240_ = lean_box(0);
    v___x_5241_ = lean_apply_2(v_inst_5238_, lean_box(0), v___x_5240_);
    return v___x_5241_;
}
pub unsafe fn l_Lake_MonadLog_nop___redArg___lam__0___boxed(
    mut v_inst_5242_: *mut LeanObject,
    mut v_x_5243_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5244_: *mut LeanObject = core::ptr::null_mut();
    v_res_5244_ = l_Lake_MonadLog_nop___redArg___lam__0(v_inst_5242_, v_x_5243_);
    lean_dec_ref(v_x_5243_);
    return v_res_5244_;
}
pub unsafe fn l_Lake_MonadLog_nop___redArg(mut v_inst_5245_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_5246_: *mut LeanObject = core::ptr::null_mut();
    v___f_5246_ = lean_alloc_closure(
        l_Lake_MonadLog_nop___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_5246_, 0, v_inst_5245_);
    return v___f_5246_;
}
pub unsafe fn l_Lake_MonadLog_nop(
    mut v_m_5247_: *mut LeanObject,
    mut v_inst_5248_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5249_: *mut LeanObject = core::ptr::null_mut();
    v___f_5249_ = lean_alloc_closure(
        l_Lake_MonadLog_nop___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_5249_, 0, v_inst_5248_);
    return v___f_5249_;
}
pub unsafe fn l_Lake_MonadLog_instInhabitedOfPure___redArg(
    mut v_inst_5250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5251_: *mut LeanObject = core::ptr::null_mut();
    v___f_5251_ = lean_alloc_closure(
        l_Lake_MonadLog_nop___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_5251_, 0, v_inst_5250_);
    return v___f_5251_;
}
pub unsafe fn l_Lake_MonadLog_instInhabitedOfPure(
    mut v_m_5252_: *mut LeanObject,
    mut v_inst_5253_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5254_: *mut LeanObject = core::ptr::null_mut();
    v___f_5254_ = lean_alloc_closure(
        l_Lake_MonadLog_nop___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_5254_, 0, v_inst_5253_);
    return v___f_5254_;
}
pub unsafe fn l_Lake_MonadLog_lift___redArg___lam__0(
    mut v_self_5255_: *mut LeanObject,
    mut v_inst_5256_: *mut LeanObject,
    mut v_e_5257_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5259_: *mut LeanObject = core::ptr::null_mut();
    v___x_5258_ = lean_apply_1(v_self_5255_, v_e_5257_);
    v___x_5259_ = lean_apply_2(v_inst_5256_, lean_box(0), v___x_5258_);
    return v___x_5259_;
}
pub unsafe fn l_Lake_MonadLog_lift___redArg(
    mut v_inst_5260_: *mut LeanObject,
    mut v_self_5261_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5262_: *mut LeanObject = core::ptr::null_mut();
    v___f_5262_ = lean_alloc_closure(
        l_Lake_MonadLog_lift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_5262_, 0, v_self_5261_);
    lean_closure_set(v___f_5262_, 1, v_inst_5260_);
    return v___f_5262_;
}
pub unsafe fn l_Lake_MonadLog_lift(
    mut v_m_5263_: *mut LeanObject,
    mut v_n_5264_: *mut LeanObject,
    mut v_inst_5265_: *mut LeanObject,
    mut v_self_5266_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5267_: *mut LeanObject = core::ptr::null_mut();
    v___f_5267_ = lean_alloc_closure(
        l_Lake_MonadLog_lift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_5267_, 0, v_self_5266_);
    lean_closure_set(v___f_5267_, 1, v_inst_5265_);
    return v___f_5267_;
}
pub unsafe fn l_Lake_MonadLog_instOfMonadLift___redArg___lam__0(
    mut v_methods_5268_: *mut LeanObject,
    mut v_inst_5269_: *mut LeanObject,
    mut v_e_5270_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5272_: *mut LeanObject = core::ptr::null_mut();
    v___x_5271_ = lean_apply_1(v_methods_5268_, v_e_5270_);
    v___x_5272_ = lean_apply_2(v_inst_5269_, lean_box(0), v___x_5271_);
    return v___x_5272_;
}
pub unsafe fn l_Lake_MonadLog_instOfMonadLift___redArg(
    mut v_inst_5273_: *mut LeanObject,
    mut v_methods_5274_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5275_: *mut LeanObject = core::ptr::null_mut();
    v___f_5275_ = lean_alloc_closure(
        l_Lake_MonadLog_instOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_5275_, 0, v_methods_5274_);
    lean_closure_set(v___f_5275_, 1, v_inst_5273_);
    return v___f_5275_;
}
pub unsafe fn l_Lake_MonadLog_instOfMonadLift(
    mut v_m_5276_: *mut LeanObject,
    mut v_n_5277_: *mut LeanObject,
    mut v_inst_5278_: *mut LeanObject,
    mut v_methods_5279_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5280_: *mut LeanObject = core::ptr::null_mut();
    v___f_5280_ = lean_alloc_closure(
        l_Lake_MonadLog_instOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_5280_, 0, v_methods_5279_);
    lean_closure_set(v___f_5280_, 1, v_inst_5278_);
    return v___f_5280_;
}
pub unsafe fn l_Lake_MonadLog_stream___redArg___lam__0(
    mut v_out_5281_: *mut LeanObject,
    mut v_minLv_5282_: u8,
    mut v_useAnsi_5283_: u8,
    mut v_inst_5284_: *mut LeanObject,
    mut v_e_5285_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5289_: *mut LeanObject = core::ptr::null_mut();
    v___x_5286_ = lean_box((v_minLv_5282_) as usize);
    v___x_5287_ = lean_box((v_useAnsi_5283_) as usize);
    v___x_5288_ = lean_alloc_closure(l_Lake_logToStream___boxed as *mut core::ffi::c_void, 5, 4);
    lean_closure_set(v___x_5288_, 0, v_e_5285_);
    lean_closure_set(v___x_5288_, 1, v_out_5281_);
    lean_closure_set(v___x_5288_, 2, v___x_5286_);
    lean_closure_set(v___x_5288_, 3, v___x_5287_);
    v___x_5289_ = lean_apply_2(v_inst_5284_, lean_box(0), v___x_5288_);
    return v___x_5289_;
}
pub unsafe fn l_Lake_MonadLog_stream___redArg___lam__0___boxed(
    mut v_out_5290_: *mut LeanObject,
    mut v_minLv_5291_: *mut LeanObject,
    mut v_useAnsi_5292_: *mut LeanObject,
    mut v_inst_5293_: *mut LeanObject,
    mut v_e_5294_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_minLv_boxed_5295_: u8 = 0;
    let mut v_useAnsi_boxed_5296_: u8 = 0;
    let mut v_res_5297_: *mut LeanObject = core::ptr::null_mut();
    v_minLv_boxed_5295_ = (lean_unbox(v_minLv_5291_) as u8);
    v_useAnsi_boxed_5296_ = (lean_unbox(v_useAnsi_5292_) as u8);
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
    mut v_inst_5298_: *mut LeanObject,
    mut v_out_5299_: *mut LeanObject,
    mut v_minLv_5300_: u8,
    mut v_useAnsi_5301_: u8,
) -> *mut LeanObject {
    let mut v___x_5302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5304_: *mut LeanObject = core::ptr::null_mut();
    v___x_5302_ = lean_box((v_minLv_5300_) as usize);
    v___x_5303_ = lean_box((v_useAnsi_5301_) as usize);
    v___f_5304_ = lean_alloc_closure(
        l_Lake_MonadLog_stream___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_5304_, 0, v_out_5299_);
    lean_closure_set(v___f_5304_, 1, v___x_5302_);
    lean_closure_set(v___f_5304_, 2, v___x_5303_);
    lean_closure_set(v___f_5304_, 3, v_inst_5298_);
    return v___f_5304_;
}
pub unsafe fn l_Lake_MonadLog_stream___redArg___boxed(
    mut v_inst_5305_: *mut LeanObject,
    mut v_out_5306_: *mut LeanObject,
    mut v_minLv_5307_: *mut LeanObject,
    mut v_useAnsi_5308_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_minLv_boxed_5309_: u8 = 0;
    let mut v_useAnsi_boxed_5310_: u8 = 0;
    let mut v_res_5311_: *mut LeanObject = core::ptr::null_mut();
    v_minLv_boxed_5309_ = (lean_unbox(v_minLv_5307_) as u8);
    v_useAnsi_boxed_5310_ = (lean_unbox(v_useAnsi_5308_) as u8);
    v_res_5311_ = l_Lake_MonadLog_stream___redArg(
        v_inst_5305_,
        v_out_5306_,
        v_minLv_boxed_5309_,
        v_useAnsi_boxed_5310_,
    );
    return v_res_5311_;
}
pub unsafe fn l_Lake_MonadLog_stream(
    mut v_m_5312_: *mut LeanObject,
    mut v_inst_5313_: *mut LeanObject,
    mut v_out_5314_: *mut LeanObject,
    mut v_minLv_5315_: u8,
    mut v_useAnsi_5316_: u8,
) -> *mut LeanObject {
    let mut v___x_5317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5319_: *mut LeanObject = core::ptr::null_mut();
    v___x_5317_ = lean_box((v_minLv_5315_) as usize);
    v___x_5318_ = lean_box((v_useAnsi_5316_) as usize);
    v___f_5319_ = lean_alloc_closure(
        l_Lake_MonadLog_stream___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_5319_, 0, v_out_5314_);
    lean_closure_set(v___f_5319_, 1, v___x_5317_);
    lean_closure_set(v___f_5319_, 2, v___x_5318_);
    lean_closure_set(v___f_5319_, 3, v_inst_5313_);
    return v___f_5319_;
}
pub unsafe fn l_Lake_MonadLog_stream___boxed(
    mut v_m_5320_: *mut LeanObject,
    mut v_inst_5321_: *mut LeanObject,
    mut v_out_5322_: *mut LeanObject,
    mut v_minLv_5323_: *mut LeanObject,
    mut v_useAnsi_5324_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_minLv_boxed_5325_: u8 = 0;
    let mut v_useAnsi_boxed_5326_: u8 = 0;
    let mut v_res_5327_: *mut LeanObject = core::ptr::null_mut();
    v_minLv_boxed_5325_ = (lean_unbox(v_minLv_5323_) as u8);
    v_useAnsi_boxed_5326_ = (lean_unbox(v_useAnsi_5324_) as u8);
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
    mut v_failure_5328_: *mut LeanObject,
    mut v_x_5329_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5330_: *mut LeanObject = core::ptr::null_mut();
    v___x_5330_ = lean_apply_1(v_failure_5328_, lean_box(0));
    return v___x_5330_;
}
pub unsafe fn l_Lake_MonadLog_error___redArg(
    mut v_inst_5331_: *mut LeanObject,
    mut v_inst_5332_: *mut LeanObject,
    mut v_msg_5333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_5334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_failure_5335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_5336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5338_: u8 = 0;
    let mut v___x_5339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5341_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_5334_ = lean_ctor_get(v_inst_5331_, 0);
    lean_inc_ref(v_toApplicative_5334_);
    v_failure_5335_ = lean_ctor_get(v_inst_5331_, 1);
    lean_inc(v_failure_5335_);
    lean_dec_ref(v_inst_5331_);
    v_toSeqRight_5336_ = lean_ctor_get(v_toApplicative_5334_, 4);
    lean_inc(v_toSeqRight_5336_);
    lean_dec_ref(v_toApplicative_5334_);
    v___f_5337_ = lean_alloc_closure(
        l_Lake_MonadLog_error___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_5337_, 0, v_failure_5335_);
    v___x_5338_ = 3;
    v___x_5339_ = lean_alloc_ctor(0, 1, (1) as u32);
    lean_ctor_set(v___x_5339_, 0, v_msg_5333_);
    lean_ctor_set_uint8(
        v___x_5339_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_5338_,
    );
    v___x_5340_ = lean_apply_1(v_inst_5332_, v___x_5339_);
    v___x_5341_ = lean_apply_4(
        v_toSeqRight_5336_,
        lean_box(0),
        lean_box(0),
        v___x_5340_,
        v___f_5337_,
    );
    return v___x_5341_;
}
pub unsafe fn l_Lake_MonadLog_error(
    mut v_m_5342_: *mut LeanObject,
    mut v_00_u03b1_5343_: *mut LeanObject,
    mut v_inst_5344_: *mut LeanObject,
    mut v_inst_5345_: *mut LeanObject,
    mut v_msg_5346_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_5347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_failure_5348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_5349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5351_: u8 = 0;
    let mut v___x_5352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5354_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_5347_ = lean_ctor_get(v_inst_5344_, 0);
    lean_inc_ref(v_toApplicative_5347_);
    v_failure_5348_ = lean_ctor_get(v_inst_5344_, 1);
    lean_inc(v_failure_5348_);
    lean_dec_ref(v_inst_5344_);
    v_toSeqRight_5349_ = lean_ctor_get(v_toApplicative_5347_, 4);
    lean_inc(v_toSeqRight_5349_);
    lean_dec_ref(v_toApplicative_5347_);
    v___f_5350_ = lean_alloc_closure(
        l_Lake_MonadLog_error___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_5350_, 0, v_failure_5348_);
    v___x_5351_ = 3;
    v___x_5352_ = lean_alloc_ctor(0, 1, (1) as u32);
    lean_ctor_set(v___x_5352_, 0, v_msg_5346_);
    lean_ctor_set_uint8(
        v___x_5352_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_5351_,
    );
    v___x_5353_ = lean_apply_1(v_inst_5345_, v___x_5352_);
    v___x_5354_ = lean_apply_4(
        v_toSeqRight_5349_,
        lean_box(0),
        lean_box(0),
        v___x_5353_,
        v___f_5350_,
    );
    return v___x_5354_;
}
pub unsafe fn l_Lake_OutStream_logEntry(
    mut v_self_5355_: *mut LeanObject,
    mut v_e_5356_: *mut LeanObject,
    mut v_minLv_5357_: u8,
    mut v_ansiMode_5358_: u8,
) -> *mut LeanObject {
    let mut v___x_5360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5361_: u8 = 0;
    let mut v___x_5362_: *mut LeanObject = core::ptr::null_mut();
    v___x_5360_ = l_Lake_OutStream_get(v_self_5355_);
    lean_inc_ref(v___x_5360_);
    v___x_5361_ = l_Lake_AnsiMode_isEnabled(v___x_5360_, v_ansiMode_5358_);
    v___x_5362_ = l_Lake_logToStream(v_e_5356_, v___x_5360_, v_minLv_5357_, v___x_5361_);
    return v___x_5362_;
}
pub unsafe fn l_Lake_OutStream_logEntry___boxed(
    mut v_self_5363_: *mut LeanObject,
    mut v_e_5364_: *mut LeanObject,
    mut v_minLv_5365_: *mut LeanObject,
    mut v_ansiMode_5366_: *mut LeanObject,
    mut v_a_5367_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_minLv_boxed_5368_: u8 = 0;
    let mut v_ansiMode_boxed_5369_: u8 = 0;
    let mut v_res_5370_: *mut LeanObject = core::ptr::null_mut();
    v_minLv_boxed_5368_ = (lean_unbox(v_minLv_5365_) as u8);
    v_ansiMode_boxed_5369_ = (lean_unbox(v_ansiMode_5366_) as u8);
    v_res_5370_ = l_Lake_OutStream_logEntry(
        v_self_5363_,
        v_e_5364_,
        v_minLv_boxed_5368_,
        v_ansiMode_boxed_5369_,
    );
    lean_dec_ref(v_e_5364_);
    lean_dec(v_self_5363_);
    return v_res_5370_;
}
pub unsafe fn l_Lake_OutStream_logger___redArg___lam__0(
    mut v_out_5371_: *mut LeanObject,
    mut v_minLv_5372_: u8,
    mut v_ansiMode_5373_: u8,
    mut v_inst_5374_: *mut LeanObject,
    mut v_e_5375_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5379_: *mut LeanObject = core::ptr::null_mut();
    v___x_5376_ = lean_box((v_minLv_5372_) as usize);
    v___x_5377_ = lean_box((v_ansiMode_5373_) as usize);
    v___x_5378_ = lean_alloc_closure(
        l_Lake_OutStream_logEntry___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___x_5378_, 0, v_out_5371_);
    lean_closure_set(v___x_5378_, 1, v_e_5375_);
    lean_closure_set(v___x_5378_, 2, v___x_5376_);
    lean_closure_set(v___x_5378_, 3, v___x_5377_);
    v___x_5379_ = lean_apply_2(v_inst_5374_, lean_box(0), v___x_5378_);
    return v___x_5379_;
}
pub unsafe fn l_Lake_OutStream_logger___redArg___lam__0___boxed(
    mut v_out_5380_: *mut LeanObject,
    mut v_minLv_5381_: *mut LeanObject,
    mut v_ansiMode_5382_: *mut LeanObject,
    mut v_inst_5383_: *mut LeanObject,
    mut v_e_5384_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_minLv_boxed_5385_: u8 = 0;
    let mut v_ansiMode_boxed_5386_: u8 = 0;
    let mut v_res_5387_: *mut LeanObject = core::ptr::null_mut();
    v_minLv_boxed_5385_ = (lean_unbox(v_minLv_5381_) as u8);
    v_ansiMode_boxed_5386_ = (lean_unbox(v_ansiMode_5382_) as u8);
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
    mut v_inst_5388_: *mut LeanObject,
    mut v_out_5389_: *mut LeanObject,
    mut v_minLv_5390_: u8,
    mut v_ansiMode_5391_: u8,
) -> *mut LeanObject {
    let mut v___x_5392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5394_: *mut LeanObject = core::ptr::null_mut();
    v___x_5392_ = lean_box((v_minLv_5390_) as usize);
    v___x_5393_ = lean_box((v_ansiMode_5391_) as usize);
    v___f_5394_ = lean_alloc_closure(
        l_Lake_OutStream_logger___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_5394_, 0, v_out_5389_);
    lean_closure_set(v___f_5394_, 1, v___x_5392_);
    lean_closure_set(v___f_5394_, 2, v___x_5393_);
    lean_closure_set(v___f_5394_, 3, v_inst_5388_);
    return v___f_5394_;
}
pub unsafe fn l_Lake_OutStream_logger___redArg___boxed(
    mut v_inst_5395_: *mut LeanObject,
    mut v_out_5396_: *mut LeanObject,
    mut v_minLv_5397_: *mut LeanObject,
    mut v_ansiMode_5398_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_minLv_boxed_5399_: u8 = 0;
    let mut v_ansiMode_boxed_5400_: u8 = 0;
    let mut v_res_5401_: *mut LeanObject = core::ptr::null_mut();
    v_minLv_boxed_5399_ = (lean_unbox(v_minLv_5397_) as u8);
    v_ansiMode_boxed_5400_ = (lean_unbox(v_ansiMode_5398_) as u8);
    v_res_5401_ = l_Lake_OutStream_logger___redArg(
        v_inst_5395_,
        v_out_5396_,
        v_minLv_boxed_5399_,
        v_ansiMode_boxed_5400_,
    );
    return v_res_5401_;
}
pub unsafe fn l_Lake_OutStream_logger(
    mut v_m_5402_: *mut LeanObject,
    mut v_inst_5403_: *mut LeanObject,
    mut v_out_5404_: *mut LeanObject,
    mut v_minLv_5405_: u8,
    mut v_ansiMode_5406_: u8,
) -> *mut LeanObject {
    let mut v___x_5407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5409_: *mut LeanObject = core::ptr::null_mut();
    v___x_5407_ = lean_box((v_minLv_5405_) as usize);
    v___x_5408_ = lean_box((v_ansiMode_5406_) as usize);
    v___f_5409_ = lean_alloc_closure(
        l_Lake_OutStream_logger___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_5409_, 0, v_out_5404_);
    lean_closure_set(v___f_5409_, 1, v___x_5407_);
    lean_closure_set(v___f_5409_, 2, v___x_5408_);
    lean_closure_set(v___f_5409_, 3, v_inst_5403_);
    return v___f_5409_;
}
pub unsafe fn l_Lake_OutStream_logger___boxed(
    mut v_m_5410_: *mut LeanObject,
    mut v_inst_5411_: *mut LeanObject,
    mut v_out_5412_: *mut LeanObject,
    mut v_minLv_5413_: *mut LeanObject,
    mut v_ansiMode_5414_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_minLv_boxed_5415_: u8 = 0;
    let mut v_ansiMode_boxed_5416_: u8 = 0;
    let mut v_res_5417_: *mut LeanObject = core::ptr::null_mut();
    v_minLv_boxed_5415_ = (lean_unbox(v_minLv_5413_) as u8);
    v_ansiMode_boxed_5416_ = (lean_unbox(v_ansiMode_5414_) as u8);
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
    mut v___x_5418_: *mut LeanObject,
    mut v_minLv_5419_: u8,
    mut v_ansiMode_5420_: u8,
    mut v_inst_5421_: *mut LeanObject,
    mut v_e_5422_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5426_: *mut LeanObject = core::ptr::null_mut();
    v___x_5423_ = lean_box((v_minLv_5419_) as usize);
    v___x_5424_ = lean_box((v_ansiMode_5420_) as usize);
    v___x_5425_ = lean_alloc_closure(
        l_Lake_OutStream_logEntry___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___x_5425_, 0, v___x_5418_);
    lean_closure_set(v___x_5425_, 1, v_e_5422_);
    lean_closure_set(v___x_5425_, 2, v___x_5423_);
    lean_closure_set(v___x_5425_, 3, v___x_5424_);
    v___x_5426_ = lean_apply_2(v_inst_5421_, lean_box(0), v___x_5425_);
    return v___x_5426_;
}
pub unsafe fn l_Lake_MonadLog_stdout___redArg___lam__0___boxed(
    mut v___x_5427_: *mut LeanObject,
    mut v_minLv_5428_: *mut LeanObject,
    mut v_ansiMode_5429_: *mut LeanObject,
    mut v_inst_5430_: *mut LeanObject,
    mut v_e_5431_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_minLv_boxed_5432_: u8 = 0;
    let mut v_ansiMode_boxed_5433_: u8 = 0;
    let mut v_res_5434_: *mut LeanObject = core::ptr::null_mut();
    v_minLv_boxed_5432_ = (lean_unbox(v_minLv_5428_) as u8);
    v_ansiMode_boxed_5433_ = (lean_unbox(v_ansiMode_5429_) as u8);
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
    mut v_inst_5435_: *mut LeanObject,
    mut v_minLv_5436_: u8,
    mut v_ansiMode_5437_: u8,
) -> *mut LeanObject {
    let mut v___x_5438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5441_: *mut LeanObject = core::ptr::null_mut();
    v___x_5438_ = lean_box(0);
    v___x_5439_ = lean_box((v_minLv_5436_) as usize);
    v___x_5440_ = lean_box((v_ansiMode_5437_) as usize);
    v___f_5441_ = lean_alloc_closure(
        l_Lake_MonadLog_stdout___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_5441_, 0, v___x_5438_);
    lean_closure_set(v___f_5441_, 1, v___x_5439_);
    lean_closure_set(v___f_5441_, 2, v___x_5440_);
    lean_closure_set(v___f_5441_, 3, v_inst_5435_);
    return v___f_5441_;
}
pub unsafe fn l_Lake_MonadLog_stdout___redArg___boxed(
    mut v_inst_5442_: *mut LeanObject,
    mut v_minLv_5443_: *mut LeanObject,
    mut v_ansiMode_5444_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_minLv_boxed_5445_: u8 = 0;
    let mut v_ansiMode_boxed_5446_: u8 = 0;
    let mut v_res_5447_: *mut LeanObject = core::ptr::null_mut();
    v_minLv_boxed_5445_ = (lean_unbox(v_minLv_5443_) as u8);
    v_ansiMode_boxed_5446_ = (lean_unbox(v_ansiMode_5444_) as u8);
    v_res_5447_ =
        l_Lake_MonadLog_stdout___redArg(v_inst_5442_, v_minLv_boxed_5445_, v_ansiMode_boxed_5446_);
    return v_res_5447_;
}
pub unsafe fn l_Lake_MonadLog_stdout(
    mut v_m_5448_: *mut LeanObject,
    mut v_inst_5449_: *mut LeanObject,
    mut v_minLv_5450_: u8,
    mut v_ansiMode_5451_: u8,
) -> *mut LeanObject {
    let mut v___x_5452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5455_: *mut LeanObject = core::ptr::null_mut();
    v___x_5452_ = lean_box(0);
    v___x_5453_ = lean_box((v_minLv_5450_) as usize);
    v___x_5454_ = lean_box((v_ansiMode_5451_) as usize);
    v___f_5455_ = lean_alloc_closure(
        l_Lake_MonadLog_stdout___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_5455_, 0, v___x_5452_);
    lean_closure_set(v___f_5455_, 1, v___x_5453_);
    lean_closure_set(v___f_5455_, 2, v___x_5454_);
    lean_closure_set(v___f_5455_, 3, v_inst_5449_);
    return v___f_5455_;
}
pub unsafe fn l_Lake_MonadLog_stdout___boxed(
    mut v_m_5456_: *mut LeanObject,
    mut v_inst_5457_: *mut LeanObject,
    mut v_minLv_5458_: *mut LeanObject,
    mut v_ansiMode_5459_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_minLv_boxed_5460_: u8 = 0;
    let mut v_ansiMode_boxed_5461_: u8 = 0;
    let mut v_res_5462_: *mut LeanObject = core::ptr::null_mut();
    v_minLv_boxed_5460_ = (lean_unbox(v_minLv_5458_) as u8);
    v_ansiMode_boxed_5461_ = (lean_unbox(v_ansiMode_5459_) as u8);
    v_res_5462_ = l_Lake_MonadLog_stdout(
        v_m_5456_,
        v_inst_5457_,
        v_minLv_boxed_5460_,
        v_ansiMode_boxed_5461_,
    );
    return v_res_5462_;
}
pub unsafe fn l_Lake_MonadLog_stderr___redArg(
    mut v_inst_5463_: *mut LeanObject,
    mut v_minLv_5464_: u8,
    mut v_ansiMode_5465_: u8,
) -> *mut LeanObject {
    let mut v___x_5466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5469_: *mut LeanObject = core::ptr::null_mut();
    v___x_5466_ = lean_box(1);
    v___x_5467_ = lean_box((v_minLv_5464_) as usize);
    v___x_5468_ = lean_box((v_ansiMode_5465_) as usize);
    v___f_5469_ = lean_alloc_closure(
        l_Lake_MonadLog_stdout___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_5469_, 0, v___x_5466_);
    lean_closure_set(v___f_5469_, 1, v___x_5467_);
    lean_closure_set(v___f_5469_, 2, v___x_5468_);
    lean_closure_set(v___f_5469_, 3, v_inst_5463_);
    return v___f_5469_;
}
pub unsafe fn l_Lake_MonadLog_stderr___redArg___boxed(
    mut v_inst_5470_: *mut LeanObject,
    mut v_minLv_5471_: *mut LeanObject,
    mut v_ansiMode_5472_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_minLv_boxed_5473_: u8 = 0;
    let mut v_ansiMode_boxed_5474_: u8 = 0;
    let mut v_res_5475_: *mut LeanObject = core::ptr::null_mut();
    v_minLv_boxed_5473_ = (lean_unbox(v_minLv_5471_) as u8);
    v_ansiMode_boxed_5474_ = (lean_unbox(v_ansiMode_5472_) as u8);
    v_res_5475_ =
        l_Lake_MonadLog_stderr___redArg(v_inst_5470_, v_minLv_boxed_5473_, v_ansiMode_boxed_5474_);
    return v_res_5475_;
}
pub unsafe fn l_Lake_MonadLog_stderr(
    mut v_m_5476_: *mut LeanObject,
    mut v_inst_5477_: *mut LeanObject,
    mut v_minLv_5478_: u8,
    mut v_ansiMode_5479_: u8,
) -> *mut LeanObject {
    let mut v___x_5480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5483_: *mut LeanObject = core::ptr::null_mut();
    v___x_5480_ = lean_box(1);
    v___x_5481_ = lean_box((v_minLv_5478_) as usize);
    v___x_5482_ = lean_box((v_ansiMode_5479_) as usize);
    v___f_5483_ = lean_alloc_closure(
        l_Lake_MonadLog_stdout___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_5483_, 0, v___x_5480_);
    lean_closure_set(v___f_5483_, 1, v___x_5481_);
    lean_closure_set(v___f_5483_, 2, v___x_5482_);
    lean_closure_set(v___f_5483_, 3, v_inst_5477_);
    return v___f_5483_;
}
pub unsafe fn l_Lake_MonadLog_stderr___boxed(
    mut v_m_5484_: *mut LeanObject,
    mut v_inst_5485_: *mut LeanObject,
    mut v_minLv_5486_: *mut LeanObject,
    mut v_ansiMode_5487_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_minLv_boxed_5488_: u8 = 0;
    let mut v_ansiMode_boxed_5489_: u8 = 0;
    let mut v_res_5490_: *mut LeanObject = core::ptr::null_mut();
    v_minLv_boxed_5488_ = (lean_unbox(v_minLv_5486_) as u8);
    v_ansiMode_boxed_5489_ = (lean_unbox(v_ansiMode_5487_) as u8);
    v_res_5490_ = l_Lake_MonadLog_stderr(
        v_m_5484_,
        v_inst_5485_,
        v_minLv_boxed_5488_,
        v_ansiMode_boxed_5489_,
    );
    return v_res_5490_;
}
pub unsafe fn l_Lake_OutStream_getLogger___redArg___lam__0(
    mut v_val_5491_: *mut LeanObject,
    mut v_minLv_5492_: u8,
    mut v_val_5493_: u8,
    mut v_inst_5494_: *mut LeanObject,
    mut v_e_5495_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5499_: *mut LeanObject = core::ptr::null_mut();
    v___x_5496_ = lean_box((v_minLv_5492_) as usize);
    v___x_5497_ = lean_box((v_val_5493_) as usize);
    v___x_5498_ = lean_alloc_closure(l_Lake_logToStream___boxed as *mut core::ffi::c_void, 5, 4);
    lean_closure_set(v___x_5498_, 0, v_e_5495_);
    lean_closure_set(v___x_5498_, 1, v_val_5491_);
    lean_closure_set(v___x_5498_, 2, v___x_5496_);
    lean_closure_set(v___x_5498_, 3, v___x_5497_);
    v___x_5499_ = lean_apply_2(v_inst_5494_, lean_box(0), v___x_5498_);
    return v___x_5499_;
}
pub unsafe fn l_Lake_OutStream_getLogger___redArg___lam__0___boxed(
    mut v_val_5500_: *mut LeanObject,
    mut v_minLv_5501_: *mut LeanObject,
    mut v_val_5502_: *mut LeanObject,
    mut v_inst_5503_: *mut LeanObject,
    mut v_e_5504_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_minLv_boxed_5505_: u8 = 0;
    let mut v_val_105__boxed_5506_: u8 = 0;
    let mut v_res_5507_: *mut LeanObject = core::ptr::null_mut();
    v_minLv_boxed_5505_ = (lean_unbox(v_minLv_5501_) as u8);
    v_val_105__boxed_5506_ = (lean_unbox(v_val_5502_) as u8);
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
    mut v_inst_5508_: *mut LeanObject,
    mut v_out_5509_: *mut LeanObject,
    mut v_minLv_5510_: u8,
    mut v_ansiMode_5511_: u8,
) -> *mut LeanObject {
    let mut v___x_5513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5514_: u8 = 0;
    let mut v___x_5515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5517_: *mut LeanObject = core::ptr::null_mut();
    v___x_5513_ = l_Lake_OutStream_get(v_out_5509_);
    lean_inc_ref(v___x_5513_);
    v___x_5514_ = l_Lake_AnsiMode_isEnabled(v___x_5513_, v_ansiMode_5511_);
    v___x_5515_ = lean_box((v_minLv_5510_) as usize);
    v___x_5516_ = lean_box((v___x_5514_) as usize);
    v___f_5517_ = lean_alloc_closure(
        l_Lake_OutStream_getLogger___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_5517_, 0, v___x_5513_);
    lean_closure_set(v___f_5517_, 1, v___x_5515_);
    lean_closure_set(v___f_5517_, 2, v___x_5516_);
    lean_closure_set(v___f_5517_, 3, v_inst_5508_);
    return v___f_5517_;
}
pub unsafe fn l_Lake_OutStream_getLogger___redArg___boxed(
    mut v_inst_5518_: *mut LeanObject,
    mut v_out_5519_: *mut LeanObject,
    mut v_minLv_5520_: *mut LeanObject,
    mut v_ansiMode_5521_: *mut LeanObject,
    mut v_a_5522_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_minLv_boxed_5523_: u8 = 0;
    let mut v_ansiMode_boxed_5524_: u8 = 0;
    let mut v_res_5525_: *mut LeanObject = core::ptr::null_mut();
    v_minLv_boxed_5523_ = (lean_unbox(v_minLv_5520_) as u8);
    v_ansiMode_boxed_5524_ = (lean_unbox(v_ansiMode_5521_) as u8);
    v_res_5525_ = l_Lake_OutStream_getLogger___redArg(
        v_inst_5518_,
        v_out_5519_,
        v_minLv_boxed_5523_,
        v_ansiMode_boxed_5524_,
    );
    lean_dec(v_out_5519_);
    return v_res_5525_;
}
pub unsafe fn l_Lake_OutStream_getLogger(
    mut v_m_5526_: *mut LeanObject,
    mut v_inst_5527_: *mut LeanObject,
    mut v_out_5528_: *mut LeanObject,
    mut v_minLv_5529_: u8,
    mut v_ansiMode_5530_: u8,
) -> *mut LeanObject {
    let mut v___x_5532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5533_: u8 = 0;
    let mut v___x_5534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5536_: *mut LeanObject = core::ptr::null_mut();
    v___x_5532_ = l_Lake_OutStream_get(v_out_5528_);
    lean_inc_ref(v___x_5532_);
    v___x_5533_ = l_Lake_AnsiMode_isEnabled(v___x_5532_, v_ansiMode_5530_);
    v___x_5534_ = lean_box((v_minLv_5529_) as usize);
    v___x_5535_ = lean_box((v___x_5533_) as usize);
    v___f_5536_ = lean_alloc_closure(
        l_Lake_OutStream_getLogger___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_5536_, 0, v___x_5532_);
    lean_closure_set(v___f_5536_, 1, v___x_5534_);
    lean_closure_set(v___f_5536_, 2, v___x_5535_);
    lean_closure_set(v___f_5536_, 3, v_inst_5527_);
    return v___f_5536_;
}
pub unsafe fn l_Lake_OutStream_getLogger___boxed(
    mut v_m_5537_: *mut LeanObject,
    mut v_inst_5538_: *mut LeanObject,
    mut v_out_5539_: *mut LeanObject,
    mut v_minLv_5540_: *mut LeanObject,
    mut v_ansiMode_5541_: *mut LeanObject,
    mut v_a_5542_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_minLv_boxed_5543_: u8 = 0;
    let mut v_ansiMode_boxed_5544_: u8 = 0;
    let mut v_res_5545_: *mut LeanObject = core::ptr::null_mut();
    v_minLv_boxed_5543_ = (lean_unbox(v_minLv_5540_) as u8);
    v_ansiMode_boxed_5544_ = (lean_unbox(v_ansiMode_5541_) as u8);
    v_res_5545_ = l_Lake_OutStream_getLogger(
        v_m_5537_,
        v_inst_5538_,
        v_out_5539_,
        v_minLv_boxed_5543_,
        v_ansiMode_boxed_5544_,
    );
    lean_dec(v_out_5539_);
    return v_res_5545_;
}
pub unsafe fn l_Lake_MonadLogT_instInhabitedOfPure___redArg___lam__0(
    mut v_inst_5546_: *mut LeanObject,
    mut v_inst_5547_: *mut LeanObject,
    mut v_x_5548_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5549_: *mut LeanObject = core::ptr::null_mut();
    v___x_5549_ = lean_apply_2(v_inst_5546_, lean_box(0), v_inst_5547_);
    return v___x_5549_;
}
pub unsafe fn l_Lake_MonadLogT_instInhabitedOfPure___redArg___lam__0___boxed(
    mut v_inst_5550_: *mut LeanObject,
    mut v_inst_5551_: *mut LeanObject,
    mut v_x_5552_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5553_: *mut LeanObject = core::ptr::null_mut();
    v_res_5553_ = l_Lake_MonadLogT_instInhabitedOfPure___redArg___lam__0(
        v_inst_5550_,
        v_inst_5551_,
        v_x_5552_,
    );
    lean_dec(v_x_5552_);
    return v_res_5553_;
}
pub unsafe fn l_Lake_MonadLogT_instInhabitedOfPure___redArg(
    mut v_inst_5554_: *mut LeanObject,
    mut v_inst_5555_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5556_: *mut LeanObject = core::ptr::null_mut();
    v___f_5556_ = lean_alloc_closure(
        l_Lake_MonadLogT_instInhabitedOfPure___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_5556_, 0, v_inst_5554_);
    lean_closure_set(v___f_5556_, 1, v_inst_5555_);
    return v___f_5556_;
}
pub unsafe fn l_Lake_MonadLogT_instInhabitedOfPure(
    mut v_n_5557_: *mut LeanObject,
    mut v_00_u03b1_5558_: *mut LeanObject,
    mut v_m_5559_: *mut LeanObject,
    mut v_inst_5560_: *mut LeanObject,
    mut v_inst_5561_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5562_: *mut LeanObject = core::ptr::null_mut();
    v___f_5562_ = lean_alloc_closure(
        l_Lake_MonadLogT_instInhabitedOfPure___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_5562_, 0, v_inst_5560_);
    lean_closure_set(v___f_5562_, 1, v_inst_5561_);
    return v___f_5562_;
}
pub unsafe fn l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg___lam__0(
    mut v_e_5563_: *mut LeanObject,
    mut v_inst_5564_: *mut LeanObject,
    mut v_a_5565_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5567_: *mut LeanObject = core::ptr::null_mut();
    v___x_5566_ = lean_apply_1(v_a_5565_, v_e_5563_);
    v___x_5567_ = lean_apply_2(v_inst_5564_, lean_box(0), v___x_5566_);
    return v___x_5567_;
}
pub unsafe fn l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg___lam__1(
    mut v_inst_5568_: *mut LeanObject,
    mut v_inst_5569_: *mut LeanObject,
    mut v_e_5570_: *mut LeanObject,
    mut v___y_5571_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_5572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_5573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_5574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5577_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_5572_ = lean_ctor_get(v_inst_5568_, 0);
    lean_inc_ref(v_toApplicative_5572_);
    v_toBind_5573_ = lean_ctor_get(v_inst_5568_, 1);
    lean_inc(v_toBind_5573_);
    lean_dec_ref(v_inst_5568_);
    v_toPure_5574_ = lean_ctor_get(v_toApplicative_5572_, 1);
    lean_inc(v_toPure_5574_);
    lean_dec_ref(v_toApplicative_5572_);
    v___f_5575_ = lean_alloc_closure(
        l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_5575_, 0, v_e_5570_);
    lean_closure_set(v___f_5575_, 1, v_inst_5569_);
    lean_inc(v___y_5571_);
    v___x_5576_ = lean_apply_2(v_toPure_5574_, lean_box(0), v___y_5571_);
    v___x_5577_ = lean_apply_4(
        v_toBind_5573_,
        lean_box(0),
        lean_box(0),
        v___x_5576_,
        v___f_5575_,
    );
    return v___x_5577_;
}
pub unsafe fn l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg___lam__1___boxed(
    mut v_inst_5578_: *mut LeanObject,
    mut v_inst_5579_: *mut LeanObject,
    mut v_e_5580_: *mut LeanObject,
    mut v___y_5581_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5582_: *mut LeanObject = core::ptr::null_mut();
    v_res_5582_ = l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg___lam__1(
        v_inst_5578_,
        v_inst_5579_,
        v_e_5580_,
        v___y_5581_,
    );
    lean_dec(v___y_5581_);
    return v_res_5582_;
}
pub unsafe fn l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg(
    mut v_inst_5583_: *mut LeanObject,
    mut v_inst_5584_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5585_: *mut LeanObject = core::ptr::null_mut();
    v___f_5585_ = lean_alloc_closure(
        l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_5585_, 0, v_inst_5583_);
    lean_closure_set(v___f_5585_, 1, v_inst_5584_);
    return v___f_5585_;
}
pub unsafe fn l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT(
    mut v_n_5586_: *mut LeanObject,
    mut v_m_5587_: *mut LeanObject,
    mut v_inst_5588_: *mut LeanObject,
    mut v_inst_5589_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5590_: *mut LeanObject = core::ptr::null_mut();
    v___f_5590_ = lean_alloc_closure(
        l_Lake_MonadLogT_instMonadLogOfMonadOfMonadLiftT___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_5590_, 0, v_inst_5588_);
    lean_closure_set(v___f_5590_, 1, v_inst_5589_);
    return v___f_5590_;
}
pub unsafe fn l_Lake_MonadLogT_adaptMethods___redArg(
    mut v_f_5591_: *mut LeanObject,
    mut v_self_5592_: *mut LeanObject,
    mut v_a_5593_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5595_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_5593_);
    v___x_5594_ = lean_apply_1(v_f_5591_, v_a_5593_);
    v___x_5595_ = lean_apply_1(v_self_5592_, v___x_5594_);
    return v___x_5595_;
}
pub unsafe fn l_Lake_MonadLogT_adaptMethods___redArg___boxed(
    mut v_f_5596_: *mut LeanObject,
    mut v_self_5597_: *mut LeanObject,
    mut v_a_5598_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5599_: *mut LeanObject = core::ptr::null_mut();
    v_res_5599_ = l_Lake_MonadLogT_adaptMethods___redArg(v_f_5596_, v_self_5597_, v_a_5598_);
    lean_dec(v_a_5598_);
    return v_res_5599_;
}
pub unsafe fn l_Lake_MonadLogT_adaptMethods(
    mut v_n_5600_: *mut LeanObject,
    mut v_m_5601_: *mut LeanObject,
    mut v_m_x27_5602_: *mut LeanObject,
    mut v_00_u03b1_5603_: *mut LeanObject,
    mut v_inst_5604_: *mut LeanObject,
    mut v_f_5605_: *mut LeanObject,
    mut v_self_5606_: *mut LeanObject,
    mut v_a_5607_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5609_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_5607_);
    v___x_5608_ = lean_apply_1(v_f_5605_, v_a_5607_);
    v___x_5609_ = lean_apply_1(v_self_5606_, v___x_5608_);
    return v___x_5609_;
}
pub unsafe fn l_Lake_MonadLogT_adaptMethods___boxed(
    mut v_n_5610_: *mut LeanObject,
    mut v_m_5611_: *mut LeanObject,
    mut v_m_x27_5612_: *mut LeanObject,
    mut v_00_u03b1_5613_: *mut LeanObject,
    mut v_inst_5614_: *mut LeanObject,
    mut v_f_5615_: *mut LeanObject,
    mut v_self_5616_: *mut LeanObject,
    mut v_a_5617_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5618_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_5617_);
    lean_dec_ref(v_inst_5614_);
    return v_res_5618_;
}
pub unsafe fn l_Lake_MonadLogT_ignoreLog___redArg(
    mut v_inst_5619_: *mut LeanObject,
    mut v_self_5620_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5622_: *mut LeanObject = core::ptr::null_mut();
    v___f_5621_ = lean_alloc_closure(
        l_Lake_MonadLog_nop___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_5621_, 0, v_inst_5619_);
    v___x_5622_ = lean_apply_1(v_self_5620_, v___f_5621_);
    return v___x_5622_;
}
pub unsafe fn l_Lake_MonadLogT_ignoreLog(
    mut v_m_5623_: *mut LeanObject,
    mut v_n_5624_: *mut LeanObject,
    mut v_00_u03b1_5625_: *mut LeanObject,
    mut v_inst_5626_: *mut LeanObject,
    mut v_self_5627_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5629_: *mut LeanObject = core::ptr::null_mut();
    v___f_5628_ = lean_alloc_closure(
        l_Lake_MonadLog_nop___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_5628_, 0, v_inst_5626_);
    v___x_5629_ = lean_apply_1(v_self_5627_, v___f_5628_);
    return v___x_5629_;
}
pub unsafe fn l_Lake_instToJsonLog___lam__0(
    mut v___x_5634_: *mut LeanObject,
    mut v_x_5635_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5636_: *mut LeanObject = core::ptr::null_mut();
    v___x_5636_ = l_Array_toJson___redArg(v___x_5634_, v_x_5635_);
    return v___x_5636_;
}
pub unsafe fn l_Lake_instFromJsonLog___lam__0(
    mut v___x_5640_: *mut LeanObject,
    mut v_x_5641_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5646_: u8 = 0;
    let mut v___x_5648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5650_: u8 = 0;
    let mut v_a_5651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5654_: u8 = 0;
    let mut v___x_5656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5658_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5642_ = l_Array_fromJson_x3f___redArg(v___x_5640_, v_x_5641_);
                if lean_obj_tag(v___x_5642_) == 0 {
                    v_a_5643_ = lean_ctor_get(v___x_5642_, 0);
                    v_isSharedCheck_5650_ = (!lean_is_exclusive(v___x_5642_)) as u8;
                    if v_isSharedCheck_5650_ == 0 {
                        v___x_5645_ = v___x_5642_;
                        v_isShared_5646_ = v_isSharedCheck_5650_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5643_);
                        lean_dec(v___x_5642_);
                        v___x_5645_ = lean_box(0);
                        v_isShared_5646_ = v_isSharedCheck_5650_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5651_ = lean_ctor_get(v___x_5642_, 0);
                    v_isSharedCheck_5658_ = (!lean_is_exclusive(v___x_5642_)) as u8;
                    if v_isSharedCheck_5658_ == 0 {
                        v___x_5653_ = v___x_5642_;
                        v_isShared_5654_ = v_isSharedCheck_5658_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5651_);
                        lean_dec(v___x_5642_);
                        v___x_5653_ = lean_box(0);
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
                    v_reuseFailAlloc_5649_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5649_, 0, v_a_5643_);
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
                    v_reuseFailAlloc_5657_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5657_, 0, v_a_5651_);
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
pub unsafe fn _init_l_Lake_Log_instInhabitedPos_default() -> *mut LeanObject {
    let mut v___x_5662_: *mut LeanObject = core::ptr::null_mut();
    v___x_5662_ = lean_unsigned_to_nat(0);
    return v___x_5662_;
}
pub unsafe fn _init_l_Lake_Log_instInhabitedPos() -> *mut LeanObject {
    let mut v___x_5663_: *mut LeanObject = core::ptr::null_mut();
    v___x_5663_ = lean_unsigned_to_nat(0);
    return v___x_5663_;
}
pub unsafe fn l_Lake_Log_instDecidableEqPos_decEq(
    mut v_x_5664_: *mut LeanObject,
    mut v_x_5665_: *mut LeanObject,
) -> u8 {
    let mut v___x_5666_: u8 = 0;
    v___x_5666_ = lean_nat_dec_eq(v_x_5664_, v_x_5665_);
    return v___x_5666_;
}
pub unsafe fn l_Lake_Log_instDecidableEqPos_decEq___boxed(
    mut v_x_5667_: *mut LeanObject,
    mut v_x_5668_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5669_: u8 = 0;
    let mut v_r_5670_: *mut LeanObject = core::ptr::null_mut();
    v_res_5669_ = l_Lake_Log_instDecidableEqPos_decEq(v_x_5667_, v_x_5668_);
    lean_dec(v_x_5668_);
    lean_dec(v_x_5667_);
    v_r_5670_ = lean_box((v_res_5669_) as usize);
    return v_r_5670_;
}
pub unsafe fn l_Lake_Log_instDecidableEqPos(
    mut v_x_5671_: *mut LeanObject,
    mut v_x_5672_: *mut LeanObject,
) -> u8 {
    let mut v___x_5673_: u8 = 0;
    v___x_5673_ = lean_nat_dec_eq(v_x_5671_, v_x_5672_);
    return v___x_5673_;
}
pub unsafe fn l_Lake_Log_instDecidableEqPos___boxed(
    mut v_x_5674_: *mut LeanObject,
    mut v_x_5675_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5676_: u8 = 0;
    let mut v_r_5677_: *mut LeanObject = core::ptr::null_mut();
    v_res_5676_ = l_Lake_Log_instDecidableEqPos(v_x_5674_, v_x_5675_);
    lean_dec(v_x_5675_);
    lean_dec(v_x_5674_);
    v_r_5677_ = lean_box((v_res_5676_) as usize);
    return v_r_5677_;
}
pub unsafe fn _init_l_Lake_instOfNatPos() -> *mut LeanObject {
    let mut v___x_5678_: *mut LeanObject = core::ptr::null_mut();
    v___x_5678_ = lean_unsigned_to_nat(0);
    return v___x_5678_;
}
pub unsafe fn l_Lake_instOrdPos___lam__0(
    mut v_x1_5679_: *mut LeanObject,
    mut v_x2_5680_: *mut LeanObject,
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
    mut v_x1_5686_: *mut LeanObject,
    mut v_x2_5687_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5688_: u8 = 0;
    let mut v_r_5689_: *mut LeanObject = core::ptr::null_mut();
    v_res_5688_ = l_Lake_instOrdPos___lam__0(v_x1_5686_, v_x2_5687_);
    lean_dec(v_x2_5687_);
    lean_dec(v_x1_5686_);
    v_r_5689_ = lean_box((v_res_5688_) as usize);
    return v_r_5689_;
}
pub unsafe fn _init_l_Lake_instLTPos() -> *mut LeanObject {
    let mut v___x_5692_: *mut LeanObject = core::ptr::null_mut();
    v___x_5692_ = lean_box(0);
    return v___x_5692_;
}
pub unsafe fn l_Lake_instDecidableRelPosLt(
    mut v_a_5693_: *mut LeanObject,
    mut v_b_5694_: *mut LeanObject,
) -> u8 {
    let mut v___x_5695_: u8 = 0;
    v___x_5695_ = lean_nat_dec_lt(v_a_5693_, v_b_5694_);
    return v___x_5695_;
}
pub unsafe fn l_Lake_instDecidableRelPosLt___boxed(
    mut v_a_5696_: *mut LeanObject,
    mut v_b_5697_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5698_: u8 = 0;
    let mut v_r_5699_: *mut LeanObject = core::ptr::null_mut();
    v_res_5698_ = l_Lake_instDecidableRelPosLt(v_a_5696_, v_b_5697_);
    lean_dec(v_b_5697_);
    lean_dec(v_a_5696_);
    v_r_5699_ = lean_box((v_res_5698_) as usize);
    return v_r_5699_;
}
pub unsafe fn _init_l_Lake_instLEPos() -> *mut LeanObject {
    let mut v___x_5700_: *mut LeanObject = core::ptr::null_mut();
    v___x_5700_ = lean_box(0);
    return v___x_5700_;
}
pub unsafe fn l_Lake_instDecidableRelPosLe(
    mut v_a_5701_: *mut LeanObject,
    mut v_b_5702_: *mut LeanObject,
) -> u8 {
    let mut v___x_5703_: u8 = 0;
    v___x_5703_ = lean_nat_dec_le(v_a_5701_, v_b_5702_);
    return v___x_5703_;
}
pub unsafe fn l_Lake_instDecidableRelPosLe___boxed(
    mut v_a_5704_: *mut LeanObject,
    mut v_b_5705_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5706_: u8 = 0;
    let mut v_r_5707_: *mut LeanObject = core::ptr::null_mut();
    v_res_5706_ = l_Lake_instDecidableRelPosLe(v_a_5704_, v_b_5705_);
    lean_dec(v_b_5705_);
    lean_dec(v_a_5704_);
    v_r_5707_ = lean_box((v_res_5706_) as usize);
    return v_r_5707_;
}
pub unsafe fn l_Lake_instMinPos___lam__0(
    mut v_x_5708_: *mut LeanObject,
    mut v_y_5709_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5710_: u8 = 0;
    v___x_5710_ = lean_nat_dec_le(v_x_5708_, v_y_5709_);
    if v___x_5710_ == 0 {
        lean_inc(v_y_5709_);
        return v_y_5709_;
    } else {
        lean_inc(v_x_5708_);
        return v_x_5708_;
    }
}
pub unsafe fn l_Lake_instMinPos___lam__0___boxed(
    mut v_x_5711_: *mut LeanObject,
    mut v_y_5712_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5713_: *mut LeanObject = core::ptr::null_mut();
    v_res_5713_ = l_Lake_instMinPos___lam__0(v_x_5711_, v_y_5712_);
    lean_dec(v_y_5712_);
    lean_dec(v_x_5711_);
    return v_res_5713_;
}
pub unsafe fn l_Lake_instMaxPos___lam__0(
    mut v_x_5716_: *mut LeanObject,
    mut v_y_5717_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5718_: u8 = 0;
    v___x_5718_ = lean_nat_dec_le(v_x_5716_, v_y_5717_);
    if v___x_5718_ == 0 {
        lean_inc(v_x_5716_);
        return v_x_5716_;
    } else {
        lean_inc(v_y_5717_);
        return v_y_5717_;
    }
}
pub unsafe fn l_Lake_instMaxPos___lam__0___boxed(
    mut v_x_5719_: *mut LeanObject,
    mut v_y_5720_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5721_: *mut LeanObject = core::ptr::null_mut();
    v_res_5721_ = l_Lake_instMaxPos___lam__0(v_x_5719_, v_y_5720_);
    lean_dec(v_y_5720_);
    lean_dec(v_x_5719_);
    return v_res_5721_;
}
pub unsafe fn l_Lake_Log_size(mut v_log_5728_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_5729_: *mut LeanObject = core::ptr::null_mut();
    v___x_5729_ = lean_array_get_size(v_log_5728_);
    return v___x_5729_;
}
pub unsafe fn l_Lake_Log_size___boxed(mut v_log_5730_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_5731_: *mut LeanObject = core::ptr::null_mut();
    v_res_5731_ = l_Lake_Log_size(v_log_5730_);
    lean_dec_ref(v_log_5730_);
    return v_res_5731_;
}
pub unsafe fn l_Lake_Log_isEmpty(mut v_log_5732_: *mut LeanObject) -> u8 {
    let mut v___x_5733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5735_: u8 = 0;
    v___x_5733_ = lean_array_get_size(v_log_5732_);
    v___x_5734_ = lean_unsigned_to_nat(0);
    v___x_5735_ = lean_nat_dec_eq(v___x_5733_, v___x_5734_);
    return v___x_5735_;
}
pub unsafe fn l_Lake_Log_isEmpty___boxed(mut v_log_5736_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_5737_: u8 = 0;
    let mut v_r_5738_: *mut LeanObject = core::ptr::null_mut();
    v_res_5737_ = l_Lake_Log_isEmpty(v_log_5736_);
    lean_dec_ref(v_log_5736_);
    v_r_5738_ = lean_box((v_res_5737_) as usize);
    return v_r_5738_;
}
pub unsafe fn l_Lake_Log_hasEntries(mut v_log_5739_: *mut LeanObject) -> u8 {
    let mut v___x_5740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5742_: u8 = 0;
    v___x_5740_ = lean_array_get_size(v_log_5739_);
    v___x_5741_ = lean_unsigned_to_nat(0);
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
pub unsafe fn l_Lake_Log_hasEntries___boxed(mut v_log_5745_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_5746_: u8 = 0;
    let mut v_r_5747_: *mut LeanObject = core::ptr::null_mut();
    v_res_5746_ = l_Lake_Log_hasEntries(v_log_5745_);
    lean_dec_ref(v_log_5745_);
    v_r_5747_ = lean_box((v_res_5746_) as usize);
    return v_r_5747_;
}
pub unsafe fn l_Lake_Log_endPos(mut v_log_5748_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_5749_: *mut LeanObject = core::ptr::null_mut();
    v___x_5749_ = lean_array_get_size(v_log_5748_);
    return v___x_5749_;
}
pub unsafe fn l_Lake_Log_endPos___boxed(mut v_log_5750_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_5751_: *mut LeanObject = core::ptr::null_mut();
    v_res_5751_ = l_Lake_Log_endPos(v_log_5750_);
    lean_dec_ref(v_log_5750_);
    return v_res_5751_;
}
pub unsafe fn l_Lake_Log_push(
    mut v_log_5752_: *mut LeanObject,
    mut v_e_5753_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5754_: *mut LeanObject = core::ptr::null_mut();
    v___x_5754_ = lean_array_push(v_log_5752_, v_e_5753_);
    return v___x_5754_;
}
pub unsafe fn l_Lake_Log_append(
    mut v_log_5755_: *mut LeanObject,
    mut v_o_5756_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5757_: *mut LeanObject = core::ptr::null_mut();
    v___x_5757_ = l_Array_append___redArg(v_log_5755_, v_o_5756_);
    return v___x_5757_;
}
pub unsafe fn l_Lake_Log_append___boxed(
    mut v_log_5758_: *mut LeanObject,
    mut v_o_5759_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5760_: *mut LeanObject = core::ptr::null_mut();
    v_res_5760_ = l_Lake_Log_append(v_log_5758_, v_o_5759_);
    lean_dec_ref(v_o_5759_);
    return v_res_5760_;
}
pub unsafe fn l_Lake_Log_extract(
    mut v_log_5763_: *mut LeanObject,
    mut v_start_5764_: *mut LeanObject,
    mut v_stop_5765_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5766_: *mut LeanObject = core::ptr::null_mut();
    v___x_5766_ = l_Array_extract___redArg(v_log_5763_, v_start_5764_, v_stop_5765_);
    return v___x_5766_;
}
pub unsafe fn l_Lake_Log_extract___boxed(
    mut v_log_5767_: *mut LeanObject,
    mut v_start_5768_: *mut LeanObject,
    mut v_stop_5769_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5770_: *mut LeanObject = core::ptr::null_mut();
    v_res_5770_ = l_Lake_Log_extract(v_log_5767_, v_start_5768_, v_stop_5769_);
    lean_dec_ref(v_log_5767_);
    return v_res_5770_;
}
pub unsafe fn l_Lake_Log_dropFrom(
    mut v_log_5771_: *mut LeanObject,
    mut v_pos_5772_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5773_: *mut LeanObject = core::ptr::null_mut();
    v___x_5773_ = l_Array_shrink___redArg(v_log_5771_, v_pos_5772_);
    return v___x_5773_;
}
pub unsafe fn l_Lake_Log_dropFrom___boxed(
    mut v_log_5774_: *mut LeanObject,
    mut v_pos_5775_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5776_: *mut LeanObject = core::ptr::null_mut();
    v_res_5776_ = l_Lake_Log_dropFrom(v_log_5774_, v_pos_5775_);
    lean_dec(v_pos_5775_);
    return v_res_5776_;
}
pub unsafe fn l_Lake_Log_takeFrom(
    mut v_log_5777_: *mut LeanObject,
    mut v_pos_5778_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5780_: *mut LeanObject = core::ptr::null_mut();
    v___x_5779_ = lean_array_get_size(v_log_5777_);
    v___x_5780_ = l_Array_extract___redArg(v_log_5777_, v_pos_5778_, v___x_5779_);
    return v___x_5780_;
}
pub unsafe fn l_Lake_Log_takeFrom___boxed(
    mut v_log_5781_: *mut LeanObject,
    mut v_pos_5782_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5783_: *mut LeanObject = core::ptr::null_mut();
    v_res_5783_ = l_Lake_Log_takeFrom(v_log_5781_, v_pos_5782_);
    lean_dec_ref(v_log_5781_);
    return v_res_5783_;
}
pub unsafe fn l_Lake_Log_split(
    mut v_log_5784_: *mut LeanObject,
    mut v_pos_5785_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5789_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_log_5784_);
    v___x_5786_ = l_Array_shrink___redArg(v_log_5784_, v_pos_5785_);
    v___x_5787_ = lean_array_get_size(v_log_5784_);
    v___x_5788_ = l_Array_extract___redArg(v_log_5784_, v_pos_5785_, v___x_5787_);
    lean_dec_ref(v_log_5784_);
    v___x_5789_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5789_, 0, v___x_5786_);
    lean_ctor_set(v___x_5789_, 1, v___x_5788_);
    return v___x_5789_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_toString_spec__0(
    mut v_as_5791_: *mut LeanObject,
    mut v_i_5792_: usize,
    mut v_stop_5793_: usize,
    mut v_b_5794_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5795_: u8 = 0;
    let mut v___x_5796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5800_: *mut LeanObject = core::ptr::null_mut();
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
                    lean_dec_ref(v___x_5797_);
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
    mut v_as_5804_: *mut LeanObject,
    mut v_i_5805_: *mut LeanObject,
    mut v_stop_5806_: *mut LeanObject,
    mut v_b_5807_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5808_: usize = 0;
    let mut v_stop_boxed_5809_: usize = 0;
    let mut v_res_5810_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5808_ = lean_unbox_usize(v_i_5805_);
    lean_dec(v_i_5805_);
    v_stop_boxed_5809_ = lean_unbox_usize(v_stop_5806_);
    lean_dec(v_stop_5806_);
    v_res_5810_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_toString_spec__0(v_as_5804_, v_i_boxed_5808_, v_stop_boxed_5809_, v_b_5807_);
    lean_dec_ref(v_as_5804_);
    return v_res_5810_;
}
pub unsafe fn l_Lake_Log_toString(mut v_log_5811_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_5812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5815_: u8 = 0;
    v___x_5812_ = l_Lake_instInhabitedLogEntry_default___closed__0;
    v___x_5813_ = lean_unsigned_to_nat(0);
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
                let mut v___x_5819_: *mut LeanObject = core::ptr::null_mut();
                v___x_5817_ = 0usize;
                v___x_5818_ = lean_usize_of_nat(v___x_5814_);
                v___x_5819_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_toString_spec__0(v_log_5811_, v___x_5817_, v___x_5818_, v___x_5812_);
                return v___x_5819_;
            }
        } else {
            let mut v___x_5820_: usize = 0;
            let mut v___x_5821_: usize = 0;
            let mut v___x_5822_: *mut LeanObject = core::ptr::null_mut();
            v___x_5820_ = 0usize;
            v___x_5821_ = lean_usize_of_nat(v___x_5814_);
            v___x_5822_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_toString_spec__0(v_log_5811_, v___x_5820_, v___x_5821_, v___x_5812_);
            return v___x_5822_;
        }
    }
}
pub unsafe fn l_Lake_Log_toString___boxed(mut v_log_5823_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_5824_: *mut LeanObject = core::ptr::null_mut();
    v_res_5824_ = l_Lake_Log_toString(v_log_5823_);
    lean_dec_ref(v_log_5823_);
    return v_res_5824_;
}
pub unsafe fn l_Lake_Log_replay___redArg___lam__0(
    mut v_logger_5827_: *mut LeanObject,
    mut v_x_5828_: *mut LeanObject,
    mut v___y_5829_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5830_: *mut LeanObject = core::ptr::null_mut();
    v___x_5830_ = lean_apply_1(v_logger_5827_, v___y_5829_);
    return v___x_5830_;
}
pub unsafe fn l_Lake_Log_replay___redArg(
    mut v_inst_5831_: *mut LeanObject,
    mut v_logger_5832_: *mut LeanObject,
    mut v_log_5833_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5837_: u8 = 0;
    v___x_5834_ = lean_unsigned_to_nat(0);
    v___x_5835_ = lean_array_get_size(v_log_5833_);
    v___x_5836_ = lean_box(0);
    v___x_5837_ = lean_nat_dec_lt(v___x_5834_, v___x_5835_);
    if v___x_5837_ == 0 {
        let mut v_toApplicative_5838_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_5839_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5840_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_log_5833_);
        lean_dec(v_logger_5832_);
        v_toApplicative_5838_ = lean_ctor_get(v_inst_5831_, 0);
        lean_inc_ref(v_toApplicative_5838_);
        lean_dec_ref(v_inst_5831_);
        v_toPure_5839_ = lean_ctor_get(v_toApplicative_5838_, 1);
        lean_inc(v_toPure_5839_);
        lean_dec_ref(v_toApplicative_5838_);
        v___x_5840_ = lean_apply_2(v_toPure_5839_, lean_box(0), v___x_5836_);
        return v___x_5840_;
    } else {
        let mut v___f_5841_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5842_: u8 = 0;
        v___f_5841_ = lean_alloc_closure(
            l_Lake_Log_replay___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        lean_closure_set(v___f_5841_, 0, v_logger_5832_);
        v___x_5842_ = lean_nat_dec_le(v___x_5835_, v___x_5835_);
        if v___x_5842_ == 0 {
            if v___x_5837_ == 0 {
                let mut v_toApplicative_5843_: *mut LeanObject = core::ptr::null_mut();
                let mut v_toPure_5844_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5845_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v___f_5841_);
                lean_dec_ref(v_log_5833_);
                v_toApplicative_5843_ = lean_ctor_get(v_inst_5831_, 0);
                lean_inc_ref(v_toApplicative_5843_);
                lean_dec_ref(v_inst_5831_);
                v_toPure_5844_ = lean_ctor_get(v_toApplicative_5843_, 1);
                lean_inc(v_toPure_5844_);
                lean_dec_ref(v_toApplicative_5843_);
                v___x_5845_ = lean_apply_2(v_toPure_5844_, lean_box(0), v___x_5836_);
                return v___x_5845_;
            } else {
                let mut v___x_5846_: usize = 0;
                let mut v___x_5847_: usize = 0;
                let mut v___x_5848_: *mut LeanObject = core::ptr::null_mut();
                v___x_5846_ = 0usize;
                v___x_5847_ = lean_usize_of_nat(v___x_5835_);
                v___x_5848_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
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
            let mut v___x_5851_: *mut LeanObject = core::ptr::null_mut();
            v___x_5849_ = 0usize;
            v___x_5850_ = lean_usize_of_nat(v___x_5835_);
            v___x_5851_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
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
    mut v_m_5852_: *mut LeanObject,
    mut v_inst_5853_: *mut LeanObject,
    mut v_logger_5854_: *mut LeanObject,
    mut v_log_5855_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5859_: u8 = 0;
    v___x_5856_ = lean_unsigned_to_nat(0);
    v___x_5857_ = lean_array_get_size(v_log_5855_);
    v___x_5858_ = lean_box(0);
    v___x_5859_ = lean_nat_dec_lt(v___x_5856_, v___x_5857_);
    if v___x_5859_ == 0 {
        let mut v_toApplicative_5860_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_5861_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5862_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_log_5855_);
        lean_dec(v_logger_5854_);
        v_toApplicative_5860_ = lean_ctor_get(v_inst_5853_, 0);
        lean_inc_ref(v_toApplicative_5860_);
        lean_dec_ref(v_inst_5853_);
        v_toPure_5861_ = lean_ctor_get(v_toApplicative_5860_, 1);
        lean_inc(v_toPure_5861_);
        lean_dec_ref(v_toApplicative_5860_);
        v___x_5862_ = lean_apply_2(v_toPure_5861_, lean_box(0), v___x_5858_);
        return v___x_5862_;
    } else {
        let mut v___f_5863_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5864_: u8 = 0;
        v___f_5863_ = lean_alloc_closure(
            l_Lake_Log_replay___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        lean_closure_set(v___f_5863_, 0, v_logger_5854_);
        v___x_5864_ = lean_nat_dec_le(v___x_5857_, v___x_5857_);
        if v___x_5864_ == 0 {
            if v___x_5859_ == 0 {
                let mut v_toApplicative_5865_: *mut LeanObject = core::ptr::null_mut();
                let mut v_toPure_5866_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5867_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v___f_5863_);
                lean_dec_ref(v_log_5855_);
                v_toApplicative_5865_ = lean_ctor_get(v_inst_5853_, 0);
                lean_inc_ref(v_toApplicative_5865_);
                lean_dec_ref(v_inst_5853_);
                v_toPure_5866_ = lean_ctor_get(v_toApplicative_5865_, 1);
                lean_inc(v_toPure_5866_);
                lean_dec_ref(v_toApplicative_5865_);
                v___x_5867_ = lean_apply_2(v_toPure_5866_, lean_box(0), v___x_5858_);
                return v___x_5867_;
            } else {
                let mut v___x_5868_: usize = 0;
                let mut v___x_5869_: usize = 0;
                let mut v___x_5870_: *mut LeanObject = core::ptr::null_mut();
                v___x_5868_ = 0usize;
                v___x_5869_ = lean_usize_of_nat(v___x_5857_);
                v___x_5870_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
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
            let mut v___x_5873_: *mut LeanObject = core::ptr::null_mut();
            v___x_5871_ = 0usize;
            v___x_5872_ = lean_usize_of_nat(v___x_5857_);
            v___x_5873_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
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
    mut v_f_5874_: *mut LeanObject,
    mut v_x1_5875_: *mut LeanObject,
    mut v_x2_5876_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5878_: u8 = 0;
    lean_inc_ref(v_x2_5876_);
    v___x_5877_ = lean_apply_1(v_f_5874_, v_x2_5876_);
    v___x_5878_ = (lean_unbox(v___x_5877_) as u8);
    if v___x_5878_ == 0 {
        lean_dec_ref(v_x2_5876_);
        return v_x1_5875_;
    } else {
        let mut v___x_5879_: *mut LeanObject = core::ptr::null_mut();
        v___x_5879_ = lean_array_push(v_x1_5875_, v_x2_5876_);
        return v___x_5879_;
    }
}
pub unsafe fn l_Lake_Log_filter(
    mut v_f_5899_: *mut LeanObject,
    mut v_log_5900_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5905_: u8 = 0;
    v___x_5901_ = lean_unsigned_to_nat(0);
    v___x_5902_ = lean_array_get_size(v_log_5900_);
    v___x_5903_ = l_Lake_Log_empty___closed__0;
    v___x_5904_ = l_Lake_Log_filter___closed__9;
    v___x_5905_ = lean_nat_dec_lt(v___x_5901_, v___x_5902_);
    if v___x_5905_ == 0 {
        lean_dec_ref(v_log_5900_);
        lean_dec_ref(v_f_5899_);
        return v___x_5903_;
    } else {
        let mut v___f_5906_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5907_: u8 = 0;
        v___f_5906_ =
            lean_alloc_closure(l_Lake_Log_filter___lam__0 as *mut core::ffi::c_void, 3, 1);
        lean_closure_set(v___f_5906_, 0, v_f_5899_);
        v___x_5907_ = lean_nat_dec_le(v___x_5902_, v___x_5902_);
        if v___x_5907_ == 0 {
            if v___x_5905_ == 0 {
                lean_dec_ref(v___f_5906_);
                lean_dec_ref(v_log_5900_);
                return v___x_5903_;
            } else {
                let mut v___x_5908_: usize = 0;
                let mut v___x_5909_: usize = 0;
                let mut v___x_5910_: *mut LeanObject = core::ptr::null_mut();
                v___x_5908_ = 0usize;
                v___x_5909_ = lean_usize_of_nat(v___x_5902_);
                v___x_5910_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
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
            let mut v___x_5913_: *mut LeanObject = core::ptr::null_mut();
            v___x_5911_ = 0usize;
            v___x_5912_ = lean_usize_of_nat(v___x_5902_);
            v___x_5913_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
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
    mut v_f_5914_: *mut LeanObject,
    mut v_x_5915_: *mut LeanObject,
) -> u8 {
    let mut v___x_5916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5917_: u8 = 0;
    v___x_5916_ = lean_apply_1(v_f_5914_, v_x_5915_);
    v___x_5917_ = (lean_unbox(v___x_5916_) as u8);
    return v___x_5917_;
}
pub unsafe fn l_Lake_Log_any___lam__0___boxed(
    mut v_f_5918_: *mut LeanObject,
    mut v_x_5919_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5920_: u8 = 0;
    let mut v_r_5921_: *mut LeanObject = core::ptr::null_mut();
    v_res_5920_ = l_Lake_Log_any___lam__0(v_f_5918_, v_x_5919_);
    v_r_5921_ = lean_box((v_res_5920_) as usize);
    return v_r_5921_;
}
pub unsafe fn l_Lake_Log_any(
    mut v_f_5922_: *mut LeanObject,
    mut v_log_5923_: *mut LeanObject,
) -> u8 {
    let mut v___x_5924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5927_: u8 = 0;
    v___x_5924_ = lean_unsigned_to_nat(0);
    v___x_5925_ = lean_array_get_size(v_log_5923_);
    v___x_5926_ = l_Lake_Log_filter___closed__9;
    v___x_5927_ = lean_nat_dec_lt(v___x_5924_, v___x_5925_);
    if v___x_5927_ == 0 {
        lean_dec_ref(v_log_5923_);
        lean_dec_ref(v_f_5922_);
        return v___x_5927_;
    } else {
        if v___x_5927_ == 0 {
            lean_dec_ref(v_log_5923_);
            lean_dec_ref(v_f_5922_);
            return v___x_5927_;
        } else {
            let mut v___f_5928_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5929_: usize = 0;
            let mut v___x_5930_: usize = 0;
            let mut v___x_5931_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5932_: u8 = 0;
            v___f_5928_ = lean_alloc_closure(
                l_Lake_Log_any___lam__0___boxed as *mut core::ffi::c_void,
                2,
                1,
            );
            lean_closure_set(v___f_5928_, 0, v_f_5922_);
            v___x_5929_ = 0usize;
            v___x_5930_ = lean_usize_of_nat(v___x_5925_);
            v___x_5931_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                lean_box(0),
                lean_box(0),
                v___x_5926_,
                v___f_5928_,
                v_log_5923_,
                v___x_5929_,
                v___x_5930_,
            );
            v___x_5932_ = (lean_unbox(v___x_5931_) as u8);
            lean_dec(v___x_5931_);
            return v___x_5932_;
        }
    }
}
pub unsafe fn l_Lake_Log_any___boxed(
    mut v_f_5933_: *mut LeanObject,
    mut v_log_5934_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5935_: u8 = 0;
    let mut v_r_5936_: *mut LeanObject = core::ptr::null_mut();
    v_res_5935_ = l_Lake_Log_any(v_f_5933_, v_log_5934_);
    v_r_5936_ = lean_box((v_res_5935_) as usize);
    return v_r_5936_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_maxLv_spec__0(
    mut v_as_5937_: *mut LeanObject,
    mut v_i_5938_: usize,
    mut v_stop_5939_: usize,
    mut v_b_5940_: u8,
) -> u8 {
    let mut v___y_5942_: u8 = 0;
    let mut v___x_5943_: usize = 0;
    let mut v___x_5944_: usize = 0;
    let mut v___x_5946_: u8 = 0;
    let mut v___x_5947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_level_5948_: u8 = 0;
    let mut v___x_5949_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5946_ = lean_usize_dec_eq(v_i_5938_, v_stop_5939_);
                if v___x_5946_ == 0 {
                    v___x_5947_ = lean_array_uget_borrowed(v_as_5937_, v_i_5938_);
                    v_level_5948_ = lean_ctor_get_uint8(
                        v___x_5947_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
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
    mut v_as_5950_: *mut LeanObject,
    mut v_i_5951_: *mut LeanObject,
    mut v_stop_5952_: *mut LeanObject,
    mut v_b_5953_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5954_: usize = 0;
    let mut v_stop_boxed_5955_: usize = 0;
    let mut v_b_boxed_5956_: u8 = 0;
    let mut v_res_5957_: u8 = 0;
    let mut v_r_5958_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5954_ = lean_unbox_usize(v_i_5951_);
    lean_dec(v_i_5951_);
    v_stop_boxed_5955_ = lean_unbox_usize(v_stop_5952_);
    lean_dec(v_stop_5952_);
    v_b_boxed_5956_ = (lean_unbox(v_b_5953_) as u8);
    v_res_5957_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Log_maxLv_spec__0(v_as_5950_, v_i_boxed_5954_, v_stop_boxed_5955_, v_b_boxed_5956_);
    lean_dec_ref(v_as_5950_);
    v_r_5958_ = lean_box((v_res_5957_) as usize);
    return v_r_5958_;
}
pub unsafe fn l_Lake_Log_maxLv(mut v_log_5959_: *mut LeanObject) -> u8 {
    let mut v___x_5960_: u8 = 0;
    let mut v___x_5961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5963_: u8 = 0;
    v___x_5960_ = 0;
    v___x_5961_ = lean_unsigned_to_nat(0);
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
pub unsafe fn l_Lake_Log_maxLv___boxed(mut v_log_5971_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_5972_: u8 = 0;
    let mut v_r_5973_: *mut LeanObject = core::ptr::null_mut();
    v_res_5972_ = l_Lake_Log_maxLv(v_log_5971_);
    lean_dec_ref(v_log_5971_);
    v_r_5973_ = lean_box((v_res_5972_) as usize);
    return v_r_5973_;
}
pub unsafe fn l_Lake_pushLogEntry___redArg___lam__0(
    mut v_e_5974_: *mut LeanObject,
    mut v_s_5975_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5978_: *mut LeanObject = core::ptr::null_mut();
    v___x_5976_ = lean_box(0);
    v___x_5977_ = lean_array_push(v_s_5975_, v_e_5974_);
    v___x_5978_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5978_, 0, v___x_5976_);
    lean_ctor_set(v___x_5978_, 1, v___x_5977_);
    return v___x_5978_;
}
pub unsafe fn l_Lake_pushLogEntry___redArg(
    mut v_inst_5979_: *mut LeanObject,
    mut v_e_5980_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_modifyGet_5981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5983_: *mut LeanObject = core::ptr::null_mut();
    v_modifyGet_5981_ = lean_ctor_get(v_inst_5979_, 2);
    lean_inc(v_modifyGet_5981_);
    lean_dec_ref(v_inst_5979_);
    v___f_5982_ = lean_alloc_closure(
        l_Lake_pushLogEntry___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_5982_, 0, v_e_5980_);
    v___x_5983_ = lean_apply_2(v_modifyGet_5981_, lean_box(0), v___f_5982_);
    return v___x_5983_;
}
pub unsafe fn l_Lake_pushLogEntry(
    mut v_m_5984_: *mut LeanObject,
    mut v_inst_5985_: *mut LeanObject,
    mut v_e_5986_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_modifyGet_5987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5989_: *mut LeanObject = core::ptr::null_mut();
    v_modifyGet_5987_ = lean_ctor_get(v_inst_5985_, 2);
    lean_inc(v_modifyGet_5987_);
    lean_dec_ref(v_inst_5985_);
    v___f_5988_ = lean_alloc_closure(
        l_Lake_pushLogEntry___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_5988_, 0, v_e_5986_);
    v___x_5989_ = lean_apply_2(v_modifyGet_5987_, lean_box(0), v___f_5988_);
    return v___x_5989_;
}
pub unsafe fn l_Lake_MonadLog_ofMonadState___redArg(
    mut v_inst_5990_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5991_: *mut LeanObject = core::ptr::null_mut();
    v___x_5991_ = lean_alloc_closure(l_Lake_pushLogEntry as *mut core::ffi::c_void, 3, 2);
    lean_closure_set(v___x_5991_, 0, lean_box(0));
    lean_closure_set(v___x_5991_, 1, v_inst_5990_);
    return v___x_5991_;
}
pub unsafe fn l_Lake_MonadLog_ofMonadState(
    mut v_m_5992_: *mut LeanObject,
    mut v_inst_5993_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5994_: *mut LeanObject = core::ptr::null_mut();
    v___x_5994_ = lean_alloc_closure(l_Lake_pushLogEntry as *mut core::ffi::c_void, 3, 2);
    lean_closure_set(v___x_5994_, 0, lean_box(0));
    lean_closure_set(v___x_5994_, 1, v_inst_5993_);
    return v___x_5994_;
}
pub unsafe fn l_Lake_getLog___redArg(mut v_inst_5995_: *mut LeanObject) -> *mut LeanObject {
    let mut v_get_5996_: *mut LeanObject = core::ptr::null_mut();
    v_get_5996_ = lean_ctor_get(v_inst_5995_, 0);
    lean_inc(v_get_5996_);
    return v_get_5996_;
}
pub unsafe fn l_Lake_getLog___redArg___boxed(mut v_inst_5997_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_5998_: *mut LeanObject = core::ptr::null_mut();
    v_res_5998_ = l_Lake_getLog___redArg(v_inst_5997_);
    lean_dec_ref(v_inst_5997_);
    return v_res_5998_;
}
pub unsafe fn l_Lake_getLog(
    mut v_m_5999_: *mut LeanObject,
    mut v_inst_6000_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_get_6001_: *mut LeanObject = core::ptr::null_mut();
    v_get_6001_ = lean_ctor_get(v_inst_6000_, 0);
    lean_inc(v_get_6001_);
    return v_get_6001_;
}
pub unsafe fn l_Lake_getLog___boxed(
    mut v_m_6002_: *mut LeanObject,
    mut v_inst_6003_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6004_: *mut LeanObject = core::ptr::null_mut();
    v_res_6004_ = l_Lake_getLog(v_m_6002_, v_inst_6003_);
    lean_dec_ref(v_inst_6003_);
    return v_res_6004_;
}
pub unsafe fn l_Lake_getLogPos___redArg___lam__0(
    mut v_x_6005_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6006_: *mut LeanObject = core::ptr::null_mut();
    v___x_6006_ = lean_array_get_size(v_x_6005_);
    return v___x_6006_;
}
pub unsafe fn l_Lake_getLogPos___redArg___lam__0___boxed(
    mut v_x_6007_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6008_: *mut LeanObject = core::ptr::null_mut();
    v_res_6008_ = l_Lake_getLogPos___redArg___lam__0(v_x_6007_);
    lean_dec_ref(v_x_6007_);
    return v_res_6008_;
}
pub unsafe fn l_Lake_getLogPos___redArg(
    mut v_inst_6010_: *mut LeanObject,
    mut v_inst_6011_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_6012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_get_6013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6015_: *mut LeanObject = core::ptr::null_mut();
    v_map_6012_ = lean_ctor_get(v_inst_6010_, 0);
    lean_inc(v_map_6012_);
    lean_dec_ref(v_inst_6010_);
    v_get_6013_ = lean_ctor_get(v_inst_6011_, 0);
    lean_inc(v_get_6013_);
    lean_dec_ref(v_inst_6011_);
    v___f_6014_ = l_Lake_getLogPos___redArg___closed__0;
    v___x_6015_ = lean_apply_4(
        v_map_6012_,
        lean_box(0),
        lean_box(0),
        v___f_6014_,
        v_get_6013_,
    );
    return v___x_6015_;
}
pub unsafe fn l_Lake_getLogPos(
    mut v_m_6016_: *mut LeanObject,
    mut v_inst_6017_: *mut LeanObject,
    mut v_inst_6018_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_6019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_get_6020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6022_: *mut LeanObject = core::ptr::null_mut();
    v_map_6019_ = lean_ctor_get(v_inst_6017_, 0);
    lean_inc(v_map_6019_);
    lean_dec_ref(v_inst_6017_);
    v_get_6020_ = lean_ctor_get(v_inst_6018_, 0);
    lean_inc(v_get_6020_);
    lean_dec_ref(v_inst_6018_);
    v___f_6021_ = l_Lake_getLogPos___redArg___closed__0;
    v___x_6022_ = lean_apply_4(
        v_map_6019_,
        lean_box(0),
        lean_box(0),
        v___f_6021_,
        v_get_6020_,
    );
    return v___x_6022_;
}
pub unsafe fn l_Lake_takeLog___redArg___lam__0(
    mut v_log_6023_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6025_: *mut LeanObject = core::ptr::null_mut();
    v___x_6024_ = l_Lake_Log_empty___closed__0;
    v___x_6025_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_6025_, 0, v_log_6023_);
    lean_ctor_set(v___x_6025_, 1, v___x_6024_);
    return v___x_6025_;
}
pub unsafe fn l_Lake_takeLog___redArg(mut v_inst_6027_: *mut LeanObject) -> *mut LeanObject {
    let mut v_modifyGet_6028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6030_: *mut LeanObject = core::ptr::null_mut();
    v_modifyGet_6028_ = lean_ctor_get(v_inst_6027_, 2);
    lean_inc(v_modifyGet_6028_);
    lean_dec_ref(v_inst_6027_);
    v___f_6029_ = l_Lake_takeLog___redArg___closed__0;
    v___x_6030_ = lean_apply_2(v_modifyGet_6028_, lean_box(0), v___f_6029_);
    return v___x_6030_;
}
pub unsafe fn l_Lake_takeLog(
    mut v_m_6031_: *mut LeanObject,
    mut v_inst_6032_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_modifyGet_6033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6035_: *mut LeanObject = core::ptr::null_mut();
    v_modifyGet_6033_ = lean_ctor_get(v_inst_6032_, 2);
    lean_inc(v_modifyGet_6033_);
    lean_dec_ref(v_inst_6032_);
    v___f_6034_ = l_Lake_takeLog___redArg___closed__0;
    v___x_6035_ = lean_apply_2(v_modifyGet_6033_, lean_box(0), v___f_6034_);
    return v___x_6035_;
}
pub unsafe fn l_Lake_takeLogFrom___redArg___lam__0(
    mut v_pos_6036_: *mut LeanObject,
    mut v_log_6037_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6041_: *mut LeanObject = core::ptr::null_mut();
    v___x_6038_ = lean_array_get_size(v_log_6037_);
    lean_inc(v_pos_6036_);
    v___x_6039_ = l_Array_extract___redArg(v_log_6037_, v_pos_6036_, v___x_6038_);
    v___x_6040_ = l_Array_shrink___redArg(v_log_6037_, v_pos_6036_);
    lean_dec(v_pos_6036_);
    v___x_6041_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_6041_, 0, v___x_6039_);
    lean_ctor_set(v___x_6041_, 1, v___x_6040_);
    return v___x_6041_;
}
pub unsafe fn l_Lake_takeLogFrom___redArg(
    mut v_inst_6042_: *mut LeanObject,
    mut v_pos_6043_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_modifyGet_6044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6046_: *mut LeanObject = core::ptr::null_mut();
    v_modifyGet_6044_ = lean_ctor_get(v_inst_6042_, 2);
    lean_inc(v_modifyGet_6044_);
    lean_dec_ref(v_inst_6042_);
    v___f_6045_ = lean_alloc_closure(
        l_Lake_takeLogFrom___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_6045_, 0, v_pos_6043_);
    v___x_6046_ = lean_apply_2(v_modifyGet_6044_, lean_box(0), v___f_6045_);
    return v___x_6046_;
}
pub unsafe fn l_Lake_takeLogFrom(
    mut v_m_6047_: *mut LeanObject,
    mut v_inst_6048_: *mut LeanObject,
    mut v_pos_6049_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_modifyGet_6050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6052_: *mut LeanObject = core::ptr::null_mut();
    v_modifyGet_6050_ = lean_ctor_get(v_inst_6048_, 2);
    lean_inc(v_modifyGet_6050_);
    lean_dec_ref(v_inst_6048_);
    v___f_6051_ = lean_alloc_closure(
        l_Lake_takeLogFrom___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_6051_, 0, v_pos_6049_);
    v___x_6052_ = lean_apply_2(v_modifyGet_6050_, lean_box(0), v___f_6051_);
    return v___x_6052_;
}
pub unsafe fn l_Lake_dropLogFrom___redArg___lam__0(
    mut v_pos_6053_: *mut LeanObject,
    mut v_s_6054_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6057_: *mut LeanObject = core::ptr::null_mut();
    v___x_6055_ = lean_box(0);
    v___x_6056_ = l_Array_shrink___redArg(v_s_6054_, v_pos_6053_);
    v___x_6057_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_6057_, 0, v___x_6055_);
    lean_ctor_set(v___x_6057_, 1, v___x_6056_);
    return v___x_6057_;
}
pub unsafe fn l_Lake_dropLogFrom___redArg___lam__0___boxed(
    mut v_pos_6058_: *mut LeanObject,
    mut v_s_6059_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6060_: *mut LeanObject = core::ptr::null_mut();
    v_res_6060_ = l_Lake_dropLogFrom___redArg___lam__0(v_pos_6058_, v_s_6059_);
    lean_dec(v_pos_6058_);
    return v_res_6060_;
}
pub unsafe fn l_Lake_dropLogFrom___redArg(
    mut v_inst_6061_: *mut LeanObject,
    mut v_pos_6062_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_modifyGet_6063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6065_: *mut LeanObject = core::ptr::null_mut();
    v_modifyGet_6063_ = lean_ctor_get(v_inst_6061_, 2);
    lean_inc(v_modifyGet_6063_);
    lean_dec_ref(v_inst_6061_);
    v___f_6064_ = lean_alloc_closure(
        l_Lake_dropLogFrom___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_6064_, 0, v_pos_6062_);
    v___x_6065_ = lean_apply_2(v_modifyGet_6063_, lean_box(0), v___f_6064_);
    return v___x_6065_;
}
pub unsafe fn l_Lake_dropLogFrom(
    mut v_m_6066_: *mut LeanObject,
    mut v_inst_6067_: *mut LeanObject,
    mut v_pos_6068_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_modifyGet_6069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6071_: *mut LeanObject = core::ptr::null_mut();
    v_modifyGet_6069_ = lean_ctor_get(v_inst_6067_, 2);
    lean_inc(v_modifyGet_6069_);
    lean_dec_ref(v_inst_6067_);
    v___f_6070_ = lean_alloc_closure(
        l_Lake_dropLogFrom___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_6070_, 0, v_pos_6068_);
    v___x_6071_ = lean_apply_2(v_modifyGet_6069_, lean_box(0), v___f_6070_);
    return v___x_6071_;
}
pub unsafe fn l_Lake_extractLog___redArg___lam__1(
    mut v_iniPos_6072_: *mut LeanObject,
    mut v_toPure_6073_: *mut LeanObject,
    mut v_log_6074_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6077_: *mut LeanObject = core::ptr::null_mut();
    v___x_6075_ = lean_array_get_size(v_log_6074_);
    v___x_6076_ = l_Array_extract___redArg(v_log_6074_, v_iniPos_6072_, v___x_6075_);
    v___x_6077_ = lean_apply_2(v_toPure_6073_, lean_box(0), v___x_6076_);
    return v___x_6077_;
}
pub unsafe fn l_Lake_extractLog___redArg___lam__1___boxed(
    mut v_iniPos_6078_: *mut LeanObject,
    mut v_toPure_6079_: *mut LeanObject,
    mut v_log_6080_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6081_: *mut LeanObject = core::ptr::null_mut();
    v_res_6081_ = l_Lake_extractLog___redArg___lam__1(v_iniPos_6078_, v_toPure_6079_, v_log_6080_);
    lean_dec_ref(v_log_6080_);
    return v_res_6081_;
}
pub unsafe fn l_Lake_extractLog___redArg___lam__0(
    mut v_toBind_6082_: *mut LeanObject,
    mut v_get_6083_: *mut LeanObject,
    mut v___f_6084_: *mut LeanObject,
    mut v_____r_6085_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6086_: *mut LeanObject = core::ptr::null_mut();
    v___x_6086_ = lean_apply_4(
        v_toBind_6082_,
        lean_box(0),
        lean_box(0),
        v_get_6083_,
        v___f_6084_,
    );
    return v___x_6086_;
}
pub unsafe fn l_Lake_extractLog___redArg___lam__2(
    mut v_toPure_6087_: *mut LeanObject,
    mut v_toBind_6088_: *mut LeanObject,
    mut v_get_6089_: *mut LeanObject,
    mut v_x_6090_: *mut LeanObject,
    mut v_iniPos_6091_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6094_: *mut LeanObject = core::ptr::null_mut();
    v___f_6092_ = lean_alloc_closure(
        l_Lake_extractLog___redArg___lam__1___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_6092_, 0, v_iniPos_6091_);
    lean_closure_set(v___f_6092_, 1, v_toPure_6087_);
    lean_inc(v_toBind_6088_);
    v___f_6093_ = lean_alloc_closure(
        l_Lake_extractLog___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_6093_, 0, v_toBind_6088_);
    lean_closure_set(v___f_6093_, 1, v_get_6089_);
    lean_closure_set(v___f_6093_, 2, v___f_6092_);
    v___x_6094_ = lean_apply_4(
        v_toBind_6088_,
        lean_box(0),
        lean_box(0),
        v_x_6090_,
        v___f_6093_,
    );
    return v___x_6094_;
}
pub unsafe fn l_Lake_extractLog___redArg(
    mut v_inst_6095_: *mut LeanObject,
    mut v_inst_6096_: *mut LeanObject,
    mut v_x_6097_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_6098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_6099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_6100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_6101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_6102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_get_6103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6107_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_6098_ = lean_ctor_get(v_inst_6095_, 0);
    lean_inc_ref(v_toApplicative_6098_);
    v_toFunctor_6099_ = lean_ctor_get(v_toApplicative_6098_, 0);
    lean_inc_ref(v_toFunctor_6099_);
    v_toBind_6100_ = lean_ctor_get(v_inst_6095_, 1);
    lean_inc_n(v_toBind_6100_, 2);
    lean_dec_ref(v_inst_6095_);
    v_toPure_6101_ = lean_ctor_get(v_toApplicative_6098_, 1);
    lean_inc(v_toPure_6101_);
    lean_dec_ref(v_toApplicative_6098_);
    v_map_6102_ = lean_ctor_get(v_toFunctor_6099_, 0);
    lean_inc(v_map_6102_);
    lean_dec_ref(v_toFunctor_6099_);
    v_get_6103_ = lean_ctor_get(v_inst_6096_, 0);
    lean_inc_n(v_get_6103_, 2);
    lean_dec_ref(v_inst_6096_);
    v___f_6104_ = l_Lake_getLogPos___redArg___closed__0;
    v___f_6105_ = lean_alloc_closure(
        l_Lake_extractLog___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_6105_, 0, v_toPure_6101_);
    lean_closure_set(v___f_6105_, 1, v_toBind_6100_);
    lean_closure_set(v___f_6105_, 2, v_get_6103_);
    lean_closure_set(v___f_6105_, 3, v_x_6097_);
    v___x_6106_ = lean_apply_4(
        v_map_6102_,
        lean_box(0),
        lean_box(0),
        v___f_6104_,
        v_get_6103_,
    );
    v___x_6107_ = lean_apply_4(
        v_toBind_6100_,
        lean_box(0),
        lean_box(0),
        v___x_6106_,
        v___f_6105_,
    );
    return v___x_6107_;
}
pub unsafe fn l_Lake_extractLog(
    mut v_m_6108_: *mut LeanObject,
    mut v_inst_6109_: *mut LeanObject,
    mut v_inst_6110_: *mut LeanObject,
    mut v_x_6111_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_6112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_6113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_6114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_6115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_6116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_get_6117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6121_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_6112_ = lean_ctor_get(v_inst_6109_, 0);
    lean_inc_ref(v_toApplicative_6112_);
    v_toFunctor_6113_ = lean_ctor_get(v_toApplicative_6112_, 0);
    lean_inc_ref(v_toFunctor_6113_);
    v_toBind_6114_ = lean_ctor_get(v_inst_6109_, 1);
    lean_inc_n(v_toBind_6114_, 2);
    lean_dec_ref(v_inst_6109_);
    v_toPure_6115_ = lean_ctor_get(v_toApplicative_6112_, 1);
    lean_inc(v_toPure_6115_);
    lean_dec_ref(v_toApplicative_6112_);
    v_map_6116_ = lean_ctor_get(v_toFunctor_6113_, 0);
    lean_inc(v_map_6116_);
    lean_dec_ref(v_toFunctor_6113_);
    v_get_6117_ = lean_ctor_get(v_inst_6110_, 0);
    lean_inc_n(v_get_6117_, 2);
    lean_dec_ref(v_inst_6110_);
    v___f_6118_ = l_Lake_getLogPos___redArg___closed__0;
    v___f_6119_ = lean_alloc_closure(
        l_Lake_extractLog___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_6119_, 0, v_toPure_6115_);
    lean_closure_set(v___f_6119_, 1, v_toBind_6114_);
    lean_closure_set(v___f_6119_, 2, v_get_6117_);
    lean_closure_set(v___f_6119_, 3, v_x_6111_);
    v___x_6120_ = lean_apply_4(
        v_map_6116_,
        lean_box(0),
        lean_box(0),
        v___f_6118_,
        v_get_6117_,
    );
    v___x_6121_ = lean_apply_4(
        v_toBind_6114_,
        lean_box(0),
        lean_box(0),
        v___x_6120_,
        v___f_6119_,
    );
    return v___x_6121_;
}
pub unsafe fn l_Lake_withExtractLog___redArg___lam__1(
    mut v_iniPos_6122_: *mut LeanObject,
    mut v_a_6123_: *mut LeanObject,
    mut v_toPure_6124_: *mut LeanObject,
    mut v_log_6125_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6129_: *mut LeanObject = core::ptr::null_mut();
    v___x_6126_ = lean_array_get_size(v_log_6125_);
    v___x_6127_ = l_Array_extract___redArg(v_log_6125_, v_iniPos_6122_, v___x_6126_);
    v___x_6128_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_6128_, 0, v_a_6123_);
    lean_ctor_set(v___x_6128_, 1, v___x_6127_);
    v___x_6129_ = lean_apply_2(v_toPure_6124_, lean_box(0), v___x_6128_);
    return v___x_6129_;
}
pub unsafe fn l_Lake_withExtractLog___redArg___lam__1___boxed(
    mut v_iniPos_6130_: *mut LeanObject,
    mut v_a_6131_: *mut LeanObject,
    mut v_toPure_6132_: *mut LeanObject,
    mut v_log_6133_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6134_: *mut LeanObject = core::ptr::null_mut();
    v_res_6134_ = l_Lake_withExtractLog___redArg___lam__1(
        v_iniPos_6130_,
        v_a_6131_,
        v_toPure_6132_,
        v_log_6133_,
    );
    lean_dec_ref(v_log_6133_);
    return v_res_6134_;
}
pub unsafe fn l_Lake_withExtractLog___redArg___lam__0(
    mut v_iniPos_6135_: *mut LeanObject,
    mut v_toPure_6136_: *mut LeanObject,
    mut v_toBind_6137_: *mut LeanObject,
    mut v_get_6138_: *mut LeanObject,
    mut v_a_6139_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6141_: *mut LeanObject = core::ptr::null_mut();
    v___f_6140_ = lean_alloc_closure(
        l_Lake_withExtractLog___redArg___lam__1___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_6140_, 0, v_iniPos_6135_);
    lean_closure_set(v___f_6140_, 1, v_a_6139_);
    lean_closure_set(v___f_6140_, 2, v_toPure_6136_);
    v___x_6141_ = lean_apply_4(
        v_toBind_6137_,
        lean_box(0),
        lean_box(0),
        v_get_6138_,
        v___f_6140_,
    );
    return v___x_6141_;
}
pub unsafe fn l_Lake_withExtractLog___redArg___lam__2(
    mut v_toPure_6142_: *mut LeanObject,
    mut v_toBind_6143_: *mut LeanObject,
    mut v_get_6144_: *mut LeanObject,
    mut v_x_6145_: *mut LeanObject,
    mut v_iniPos_6146_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6148_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_toBind_6143_);
    v___f_6147_ = lean_alloc_closure(
        l_Lake_withExtractLog___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_6147_, 0, v_iniPos_6146_);
    lean_closure_set(v___f_6147_, 1, v_toPure_6142_);
    lean_closure_set(v___f_6147_, 2, v_toBind_6143_);
    lean_closure_set(v___f_6147_, 3, v_get_6144_);
    v___x_6148_ = lean_apply_4(
        v_toBind_6143_,
        lean_box(0),
        lean_box(0),
        v_x_6145_,
        v___f_6147_,
    );
    return v___x_6148_;
}
pub unsafe fn l_Lake_withExtractLog___redArg(
    mut v_inst_6149_: *mut LeanObject,
    mut v_inst_6150_: *mut LeanObject,
    mut v_x_6151_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_6152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_6153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_6154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_6155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_6156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_get_6157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6161_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_6152_ = lean_ctor_get(v_inst_6149_, 0);
    lean_inc_ref(v_toApplicative_6152_);
    v_toFunctor_6153_ = lean_ctor_get(v_toApplicative_6152_, 0);
    lean_inc_ref(v_toFunctor_6153_);
    v_toBind_6154_ = lean_ctor_get(v_inst_6149_, 1);
    lean_inc_n(v_toBind_6154_, 2);
    lean_dec_ref(v_inst_6149_);
    v_toPure_6155_ = lean_ctor_get(v_toApplicative_6152_, 1);
    lean_inc(v_toPure_6155_);
    lean_dec_ref(v_toApplicative_6152_);
    v_map_6156_ = lean_ctor_get(v_toFunctor_6153_, 0);
    lean_inc(v_map_6156_);
    lean_dec_ref(v_toFunctor_6153_);
    v_get_6157_ = lean_ctor_get(v_inst_6150_, 0);
    lean_inc_n(v_get_6157_, 2);
    lean_dec_ref(v_inst_6150_);
    v___f_6158_ = l_Lake_getLogPos___redArg___closed__0;
    v___f_6159_ = lean_alloc_closure(
        l_Lake_withExtractLog___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_6159_, 0, v_toPure_6155_);
    lean_closure_set(v___f_6159_, 1, v_toBind_6154_);
    lean_closure_set(v___f_6159_, 2, v_get_6157_);
    lean_closure_set(v___f_6159_, 3, v_x_6151_);
    v___x_6160_ = lean_apply_4(
        v_map_6156_,
        lean_box(0),
        lean_box(0),
        v___f_6158_,
        v_get_6157_,
    );
    v___x_6161_ = lean_apply_4(
        v_toBind_6154_,
        lean_box(0),
        lean_box(0),
        v___x_6160_,
        v___f_6159_,
    );
    return v___x_6161_;
}
pub unsafe fn l_Lake_withExtractLog(
    mut v_m_6162_: *mut LeanObject,
    mut v_00_u03b1_6163_: *mut LeanObject,
    mut v_inst_6164_: *mut LeanObject,
    mut v_inst_6165_: *mut LeanObject,
    mut v_x_6166_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_6167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_6168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_6169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_6170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_6171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_get_6172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6176_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_6167_ = lean_ctor_get(v_inst_6164_, 0);
    lean_inc_ref(v_toApplicative_6167_);
    v_toFunctor_6168_ = lean_ctor_get(v_toApplicative_6167_, 0);
    lean_inc_ref(v_toFunctor_6168_);
    v_toBind_6169_ = lean_ctor_get(v_inst_6164_, 1);
    lean_inc_n(v_toBind_6169_, 2);
    lean_dec_ref(v_inst_6164_);
    v_toPure_6170_ = lean_ctor_get(v_toApplicative_6167_, 1);
    lean_inc(v_toPure_6170_);
    lean_dec_ref(v_toApplicative_6167_);
    v_map_6171_ = lean_ctor_get(v_toFunctor_6168_, 0);
    lean_inc(v_map_6171_);
    lean_dec_ref(v_toFunctor_6168_);
    v_get_6172_ = lean_ctor_get(v_inst_6165_, 0);
    lean_inc_n(v_get_6172_, 2);
    lean_dec_ref(v_inst_6165_);
    v___f_6173_ = l_Lake_getLogPos___redArg___closed__0;
    v___f_6174_ = lean_alloc_closure(
        l_Lake_withExtractLog___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_6174_, 0, v_toPure_6170_);
    lean_closure_set(v___f_6174_, 1, v_toBind_6169_);
    lean_closure_set(v___f_6174_, 2, v_get_6172_);
    lean_closure_set(v___f_6174_, 3, v_x_6166_);
    v___x_6175_ = lean_apply_4(
        v_map_6171_,
        lean_box(0),
        lean_box(0),
        v___f_6173_,
        v_get_6172_,
    );
    v___x_6176_ = lean_apply_4(
        v_toBind_6169_,
        lean_box(0),
        lean_box(0),
        v___x_6175_,
        v___f_6174_,
    );
    return v___x_6176_;
}
pub unsafe fn l_Lake_throwIfLogs___redArg___lam__1(
    mut v_iniPos_6177_: *mut LeanObject,
    mut v_inst_6178_: *mut LeanObject,
    mut v_toPure_6179_: *mut LeanObject,
    mut v_a_6180_: *mut LeanObject,
    mut v_endPos_6181_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6182_: u8 = 0;
    v___x_6182_ = lean_nat_dec_eq(v_iniPos_6177_, v_endPos_6181_);
    if v___x_6182_ == 0 {
        let mut v_throw_6183_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6184_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_a_6180_);
        lean_dec(v_toPure_6179_);
        v_throw_6183_ = lean_ctor_get(v_inst_6178_, 0);
        lean_inc(v_throw_6183_);
        lean_dec_ref(v_inst_6178_);
        v___x_6184_ = lean_apply_2(v_throw_6183_, lean_box(0), v_iniPos_6177_);
        return v___x_6184_;
    } else {
        let mut v___x_6185_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_inst_6178_);
        lean_dec(v_iniPos_6177_);
        v___x_6185_ = lean_apply_2(v_toPure_6179_, lean_box(0), v_a_6180_);
        return v___x_6185_;
    }
}
pub unsafe fn l_Lake_throwIfLogs___redArg___lam__1___boxed(
    mut v_iniPos_6186_: *mut LeanObject,
    mut v_inst_6187_: *mut LeanObject,
    mut v_toPure_6188_: *mut LeanObject,
    mut v_a_6189_: *mut LeanObject,
    mut v_endPos_6190_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6191_: *mut LeanObject = core::ptr::null_mut();
    v_res_6191_ = l_Lake_throwIfLogs___redArg___lam__1(
        v_iniPos_6186_,
        v_inst_6187_,
        v_toPure_6188_,
        v_a_6189_,
        v_endPos_6190_,
    );
    lean_dec(v_endPos_6190_);
    return v_res_6191_;
}
pub unsafe fn l_Lake_throwIfLogs___redArg___lam__0(
    mut v_iniPos_6192_: *mut LeanObject,
    mut v_inst_6193_: *mut LeanObject,
    mut v_toPure_6194_: *mut LeanObject,
    mut v_toBind_6195_: *mut LeanObject,
    mut v___x_6196_: *mut LeanObject,
    mut v_a_6197_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6199_: *mut LeanObject = core::ptr::null_mut();
    v___f_6198_ = lean_alloc_closure(
        l_Lake_throwIfLogs___redArg___lam__1___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_6198_, 0, v_iniPos_6192_);
    lean_closure_set(v___f_6198_, 1, v_inst_6193_);
    lean_closure_set(v___f_6198_, 2, v_toPure_6194_);
    lean_closure_set(v___f_6198_, 3, v_a_6197_);
    v___x_6199_ = lean_apply_4(
        v_toBind_6195_,
        lean_box(0),
        lean_box(0),
        v___x_6196_,
        v___f_6198_,
    );
    return v___x_6199_;
}
pub unsafe fn l_Lake_throwIfLogs___redArg___lam__2(
    mut v_inst_6200_: *mut LeanObject,
    mut v_toPure_6201_: *mut LeanObject,
    mut v_toBind_6202_: *mut LeanObject,
    mut v___x_6203_: *mut LeanObject,
    mut v_x_6204_: *mut LeanObject,
    mut v_iniPos_6205_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6207_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_toBind_6202_);
    v___f_6206_ = lean_alloc_closure(
        l_Lake_throwIfLogs___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_6206_, 0, v_iniPos_6205_);
    lean_closure_set(v___f_6206_, 1, v_inst_6200_);
    lean_closure_set(v___f_6206_, 2, v_toPure_6201_);
    lean_closure_set(v___f_6206_, 3, v_toBind_6202_);
    lean_closure_set(v___f_6206_, 4, v___x_6203_);
    v___x_6207_ = lean_apply_4(
        v_toBind_6202_,
        lean_box(0),
        lean_box(0),
        v_x_6204_,
        v___f_6206_,
    );
    return v___x_6207_;
}
pub unsafe fn l_Lake_throwIfLogs___redArg(
    mut v_inst_6208_: *mut LeanObject,
    mut v_inst_6209_: *mut LeanObject,
    mut v_inst_6210_: *mut LeanObject,
    mut v_x_6211_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_6212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_6213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_6214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_6215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_6216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_get_6217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6221_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_6212_ = lean_ctor_get(v_inst_6208_, 0);
    lean_inc_ref(v_toApplicative_6212_);
    v_toFunctor_6213_ = lean_ctor_get(v_toApplicative_6212_, 0);
    lean_inc_ref(v_toFunctor_6213_);
    v_toBind_6214_ = lean_ctor_get(v_inst_6208_, 1);
    lean_inc_n(v_toBind_6214_, 2);
    lean_dec_ref(v_inst_6208_);
    v_toPure_6215_ = lean_ctor_get(v_toApplicative_6212_, 1);
    lean_inc(v_toPure_6215_);
    lean_dec_ref(v_toApplicative_6212_);
    v_map_6216_ = lean_ctor_get(v_toFunctor_6213_, 0);
    lean_inc(v_map_6216_);
    lean_dec_ref(v_toFunctor_6213_);
    v_get_6217_ = lean_ctor_get(v_inst_6209_, 0);
    lean_inc(v_get_6217_);
    lean_dec_ref(v_inst_6209_);
    v___f_6218_ = l_Lake_getLogPos___redArg___closed__0;
    v___x_6219_ = lean_apply_4(
        v_map_6216_,
        lean_box(0),
        lean_box(0),
        v___f_6218_,
        v_get_6217_,
    );
    lean_inc(v___x_6219_);
    v___f_6220_ = lean_alloc_closure(
        l_Lake_throwIfLogs___redArg___lam__2 as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_6220_, 0, v_inst_6210_);
    lean_closure_set(v___f_6220_, 1, v_toPure_6215_);
    lean_closure_set(v___f_6220_, 2, v_toBind_6214_);
    lean_closure_set(v___f_6220_, 3, v___x_6219_);
    lean_closure_set(v___f_6220_, 4, v_x_6211_);
    v___x_6221_ = lean_apply_4(
        v_toBind_6214_,
        lean_box(0),
        lean_box(0),
        v___x_6219_,
        v___f_6220_,
    );
    return v___x_6221_;
}
pub unsafe fn l_Lake_throwIfLogs(
    mut v_m_6222_: *mut LeanObject,
    mut v_00_u03b1_6223_: *mut LeanObject,
    mut v_inst_6224_: *mut LeanObject,
    mut v_inst_6225_: *mut LeanObject,
    mut v_inst_6226_: *mut LeanObject,
    mut v_x_6227_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_6228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_6229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_6230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_6231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_6232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_get_6233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6237_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_6228_ = lean_ctor_get(v_inst_6224_, 0);
    lean_inc_ref(v_toApplicative_6228_);
    v_toFunctor_6229_ = lean_ctor_get(v_toApplicative_6228_, 0);
    lean_inc_ref(v_toFunctor_6229_);
    v_toBind_6230_ = lean_ctor_get(v_inst_6224_, 1);
    lean_inc_n(v_toBind_6230_, 2);
    lean_dec_ref(v_inst_6224_);
    v_toPure_6231_ = lean_ctor_get(v_toApplicative_6228_, 1);
    lean_inc(v_toPure_6231_);
    lean_dec_ref(v_toApplicative_6228_);
    v_map_6232_ = lean_ctor_get(v_toFunctor_6229_, 0);
    lean_inc(v_map_6232_);
    lean_dec_ref(v_toFunctor_6229_);
    v_get_6233_ = lean_ctor_get(v_inst_6225_, 0);
    lean_inc(v_get_6233_);
    lean_dec_ref(v_inst_6225_);
    v___f_6234_ = l_Lake_getLogPos___redArg___closed__0;
    v___x_6235_ = lean_apply_4(
        v_map_6232_,
        lean_box(0),
        lean_box(0),
        v___f_6234_,
        v_get_6233_,
    );
    lean_inc(v___x_6235_);
    v___f_6236_ = lean_alloc_closure(
        l_Lake_throwIfLogs___redArg___lam__2 as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_6236_, 0, v_inst_6226_);
    lean_closure_set(v___f_6236_, 1, v_toPure_6231_);
    lean_closure_set(v___f_6236_, 2, v_toBind_6230_);
    lean_closure_set(v___f_6236_, 3, v___x_6235_);
    lean_closure_set(v___f_6236_, 4, v_x_6227_);
    v___x_6237_ = lean_apply_4(
        v_toBind_6230_,
        lean_box(0),
        lean_box(0),
        v___x_6235_,
        v___f_6236_,
    );
    return v___x_6237_;
}
pub unsafe fn l_Lake_withLogErrorPos___redArg___lam__1(
    mut v_throw_6238_: *mut LeanObject,
    mut v_iniPos_6239_: *mut LeanObject,
    mut v_x_6240_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6241_: *mut LeanObject = core::ptr::null_mut();
    v___x_6241_ = lean_apply_2(v_throw_6238_, lean_box(0), v_iniPos_6239_);
    return v___x_6241_;
}
pub unsafe fn l_Lake_withLogErrorPos___redArg___lam__1___boxed(
    mut v_throw_6242_: *mut LeanObject,
    mut v_iniPos_6243_: *mut LeanObject,
    mut v_x_6244_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6245_: *mut LeanObject = core::ptr::null_mut();
    v_res_6245_ =
        l_Lake_withLogErrorPos___redArg___lam__1(v_throw_6242_, v_iniPos_6243_, v_x_6244_);
    lean_dec(v_x_6244_);
    return v_res_6245_;
}
pub unsafe fn l_Lake_withLogErrorPos___redArg___lam__0(
    mut v_inst_6246_: *mut LeanObject,
    mut v_self_6247_: *mut LeanObject,
    mut v_iniPos_6248_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_throw_6249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tryCatch_6250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6252_: *mut LeanObject = core::ptr::null_mut();
    v_throw_6249_ = lean_ctor_get(v_inst_6246_, 0);
    lean_inc(v_throw_6249_);
    v_tryCatch_6250_ = lean_ctor_get(v_inst_6246_, 1);
    lean_inc(v_tryCatch_6250_);
    lean_dec_ref(v_inst_6246_);
    v___f_6251_ = lean_alloc_closure(
        l_Lake_withLogErrorPos___redArg___lam__1___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_6251_, 0, v_throw_6249_);
    lean_closure_set(v___f_6251_, 1, v_iniPos_6248_);
    v___x_6252_ = lean_apply_3(v_tryCatch_6250_, lean_box(0), v_self_6247_, v___f_6251_);
    return v___x_6252_;
}
pub unsafe fn l_Lake_withLogErrorPos___redArg(
    mut v_inst_6253_: *mut LeanObject,
    mut v_inst_6254_: *mut LeanObject,
    mut v_inst_6255_: *mut LeanObject,
    mut v_self_6256_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_6257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_6258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_6259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_6260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_get_6261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6265_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_6257_ = lean_ctor_get(v_inst_6253_, 0);
    v_toFunctor_6258_ = lean_ctor_get(v_toApplicative_6257_, 0);
    lean_inc_ref(v_toFunctor_6258_);
    v_toBind_6259_ = lean_ctor_get(v_inst_6253_, 1);
    lean_inc(v_toBind_6259_);
    lean_dec_ref(v_inst_6253_);
    v_map_6260_ = lean_ctor_get(v_toFunctor_6258_, 0);
    lean_inc(v_map_6260_);
    lean_dec_ref(v_toFunctor_6258_);
    v_get_6261_ = lean_ctor_get(v_inst_6254_, 0);
    lean_inc(v_get_6261_);
    lean_dec_ref(v_inst_6254_);
    v___f_6262_ = l_Lake_getLogPos___redArg___closed__0;
    v___f_6263_ = lean_alloc_closure(
        l_Lake_withLogErrorPos___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_6263_, 0, v_inst_6255_);
    lean_closure_set(v___f_6263_, 1, v_self_6256_);
    v___x_6264_ = lean_apply_4(
        v_map_6260_,
        lean_box(0),
        lean_box(0),
        v___f_6262_,
        v_get_6261_,
    );
    v___x_6265_ = lean_apply_4(
        v_toBind_6259_,
        lean_box(0),
        lean_box(0),
        v___x_6264_,
        v___f_6263_,
    );
    return v___x_6265_;
}
pub unsafe fn l_Lake_withLogErrorPos(
    mut v_m_6266_: *mut LeanObject,
    mut v_00_u03b1_6267_: *mut LeanObject,
    mut v_inst_6268_: *mut LeanObject,
    mut v_inst_6269_: *mut LeanObject,
    mut v_inst_6270_: *mut LeanObject,
    mut v_self_6271_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_6272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_6273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_6274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_6275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_get_6276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6280_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_6272_ = lean_ctor_get(v_inst_6268_, 0);
    v_toFunctor_6273_ = lean_ctor_get(v_toApplicative_6272_, 0);
    lean_inc_ref(v_toFunctor_6273_);
    v_toBind_6274_ = lean_ctor_get(v_inst_6268_, 1);
    lean_inc(v_toBind_6274_);
    lean_dec_ref(v_inst_6268_);
    v_map_6275_ = lean_ctor_get(v_toFunctor_6273_, 0);
    lean_inc(v_map_6275_);
    lean_dec_ref(v_toFunctor_6273_);
    v_get_6276_ = lean_ctor_get(v_inst_6269_, 0);
    lean_inc(v_get_6276_);
    lean_dec_ref(v_inst_6269_);
    v___f_6277_ = l_Lake_getLogPos___redArg___closed__0;
    v___f_6278_ = lean_alloc_closure(
        l_Lake_withLogErrorPos___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_6278_, 0, v_inst_6270_);
    lean_closure_set(v___f_6278_, 1, v_self_6271_);
    v___x_6279_ = lean_apply_4(
        v_map_6275_,
        lean_box(0),
        lean_box(0),
        v___f_6277_,
        v_get_6276_,
    );
    v___x_6280_ = lean_apply_4(
        v_toBind_6274_,
        lean_box(0),
        lean_box(0),
        v___x_6279_,
        v___f_6278_,
    );
    return v___x_6280_;
}
pub unsafe fn l_Lake_errorWithLog___redArg___lam__1(
    mut v_toPure_6281_: *mut LeanObject,
    mut v_x_6282_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6284_: *mut LeanObject = core::ptr::null_mut();
    v___x_6283_ = lean_box(0);
    v___x_6284_ = lean_apply_2(v_toPure_6281_, lean_box(0), v___x_6283_);
    return v___x_6284_;
}
pub unsafe fn l_Lake_errorWithLog___redArg___lam__1___boxed(
    mut v_toPure_6285_: *mut LeanObject,
    mut v_x_6286_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6287_: *mut LeanObject = core::ptr::null_mut();
    v_res_6287_ = l_Lake_errorWithLog___redArg___lam__1(v_toPure_6285_, v_x_6286_);
    lean_dec(v_x_6286_);
    return v_res_6287_;
}
pub unsafe fn l_Lake_errorWithLog___redArg___lam__0(
    mut v_throw_6288_: *mut LeanObject,
    mut v_iniPos_6289_: *mut LeanObject,
    mut v_____r_6290_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6291_: *mut LeanObject = core::ptr::null_mut();
    v___x_6291_ = lean_apply_2(v_throw_6288_, lean_box(0), v_iniPos_6289_);
    return v___x_6291_;
}
pub unsafe fn l_Lake_errorWithLog___redArg___lam__2(
    mut v_inst_6292_: *mut LeanObject,
    mut v_self_6293_: *mut LeanObject,
    mut v___f_6294_: *mut LeanObject,
    mut v_toBind_6295_: *mut LeanObject,
    mut v_iniPos_6296_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_throw_6297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tryCatch_6298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6301_: *mut LeanObject = core::ptr::null_mut();
    v_throw_6297_ = lean_ctor_get(v_inst_6292_, 0);
    lean_inc(v_throw_6297_);
    v_tryCatch_6298_ = lean_ctor_get(v_inst_6292_, 1);
    lean_inc(v_tryCatch_6298_);
    lean_dec_ref(v_inst_6292_);
    v___f_6299_ = lean_alloc_closure(
        l_Lake_errorWithLog___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_6299_, 0, v_throw_6297_);
    lean_closure_set(v___f_6299_, 1, v_iniPos_6296_);
    v___x_6300_ = lean_apply_3(v_tryCatch_6298_, lean_box(0), v_self_6293_, v___f_6294_);
    v___x_6301_ = lean_apply_4(
        v_toBind_6295_,
        lean_box(0),
        lean_box(0),
        v___x_6300_,
        v___f_6299_,
    );
    return v___x_6301_;
}
pub unsafe fn l_Lake_errorWithLog___redArg(
    mut v_inst_6302_: *mut LeanObject,
    mut v_inst_6303_: *mut LeanObject,
    mut v_inst_6304_: *mut LeanObject,
    mut v_self_6305_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_6306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_6307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_6308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_6309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_6310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_get_6311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6316_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_6306_ = lean_ctor_get(v_inst_6302_, 0);
    lean_inc_ref(v_toApplicative_6306_);
    v_toFunctor_6307_ = lean_ctor_get(v_toApplicative_6306_, 0);
    lean_inc_ref(v_toFunctor_6307_);
    v_toBind_6308_ = lean_ctor_get(v_inst_6302_, 1);
    lean_inc_n(v_toBind_6308_, 2);
    lean_dec_ref(v_inst_6302_);
    v_toPure_6309_ = lean_ctor_get(v_toApplicative_6306_, 1);
    lean_inc(v_toPure_6309_);
    lean_dec_ref(v_toApplicative_6306_);
    v_map_6310_ = lean_ctor_get(v_toFunctor_6307_, 0);
    lean_inc(v_map_6310_);
    lean_dec_ref(v_toFunctor_6307_);
    v_get_6311_ = lean_ctor_get(v_inst_6303_, 0);
    lean_inc(v_get_6311_);
    lean_dec_ref(v_inst_6303_);
    v___f_6312_ = l_Lake_getLogPos___redArg___closed__0;
    v___f_6313_ = lean_alloc_closure(
        l_Lake_errorWithLog___redArg___lam__1___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_6313_, 0, v_toPure_6309_);
    v___f_6314_ = lean_alloc_closure(
        l_Lake_errorWithLog___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_6314_, 0, v_inst_6304_);
    lean_closure_set(v___f_6314_, 1, v_self_6305_);
    lean_closure_set(v___f_6314_, 2, v___f_6313_);
    lean_closure_set(v___f_6314_, 3, v_toBind_6308_);
    v___x_6315_ = lean_apply_4(
        v_map_6310_,
        lean_box(0),
        lean_box(0),
        v___f_6312_,
        v_get_6311_,
    );
    v___x_6316_ = lean_apply_4(
        v_toBind_6308_,
        lean_box(0),
        lean_box(0),
        v___x_6315_,
        v___f_6314_,
    );
    return v___x_6316_;
}
pub unsafe fn l_Lake_errorWithLog(
    mut v_m_6317_: *mut LeanObject,
    mut v_00_u03b2_6318_: *mut LeanObject,
    mut v_inst_6319_: *mut LeanObject,
    mut v_inst_6320_: *mut LeanObject,
    mut v_inst_6321_: *mut LeanObject,
    mut v_self_6322_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_6323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_6324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_6325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_6326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_6327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_get_6328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6333_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_6323_ = lean_ctor_get(v_inst_6319_, 0);
    lean_inc_ref(v_toApplicative_6323_);
    v_toFunctor_6324_ = lean_ctor_get(v_toApplicative_6323_, 0);
    lean_inc_ref(v_toFunctor_6324_);
    v_toBind_6325_ = lean_ctor_get(v_inst_6319_, 1);
    lean_inc_n(v_toBind_6325_, 2);
    lean_dec_ref(v_inst_6319_);
    v_toPure_6326_ = lean_ctor_get(v_toApplicative_6323_, 1);
    lean_inc(v_toPure_6326_);
    lean_dec_ref(v_toApplicative_6323_);
    v_map_6327_ = lean_ctor_get(v_toFunctor_6324_, 0);
    lean_inc(v_map_6327_);
    lean_dec_ref(v_toFunctor_6324_);
    v_get_6328_ = lean_ctor_get(v_inst_6320_, 0);
    lean_inc(v_get_6328_);
    lean_dec_ref(v_inst_6320_);
    v___f_6329_ = l_Lake_getLogPos___redArg___closed__0;
    v___f_6330_ = lean_alloc_closure(
        l_Lake_errorWithLog___redArg___lam__1___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_6330_, 0, v_toPure_6326_);
    v___f_6331_ = lean_alloc_closure(
        l_Lake_errorWithLog___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_6331_, 0, v_inst_6321_);
    lean_closure_set(v___f_6331_, 1, v_self_6322_);
    lean_closure_set(v___f_6331_, 2, v___f_6330_);
    lean_closure_set(v___f_6331_, 3, v_toBind_6325_);
    v___x_6332_ = lean_apply_4(
        v_map_6327_,
        lean_box(0),
        lean_box(0),
        v___f_6329_,
        v_get_6328_,
    );
    v___x_6333_ = lean_apply_4(
        v_toBind_6325_,
        lean_box(0),
        lean_box(0),
        v___x_6332_,
        v___f_6331_,
    );
    return v___x_6333_;
}
pub unsafe fn l_Lake_withLoggedIO___redArg___lam__0(
    mut v_x_6334_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_6335_: *mut LeanObject = core::ptr::null_mut();
    v_fst_6335_ = lean_ctor_get(v_x_6334_, 0);
    lean_inc(v_fst_6335_);
    return v_fst_6335_;
}
pub unsafe fn l_Lake_withLoggedIO___redArg___lam__0___boxed(
    mut v_x_6336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6337_: *mut LeanObject = core::ptr::null_mut();
    v_res_6337_ = l_Lake_withLoggedIO___redArg___lam__0(v_x_6336_);
    lean_dec_ref(v_x_6336_);
    return v_res_6337_;
}
pub unsafe fn l_Lake_withLoggedIO___redArg___lam__1(
    mut v_buf_6338_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6340_: *mut LeanObject = core::ptr::null_mut();
    v___x_6340_ = lean_st_ref_get(v_buf_6338_);
    return v___x_6340_;
}
pub unsafe fn l_Lake_withLoggedIO___redArg___lam__1___boxed(
    mut v_buf_6341_: *mut LeanObject,
    mut v___y_6342_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6343_: *mut LeanObject = core::ptr::null_mut();
    v_res_6343_ = l_Lake_withLoggedIO___redArg___lam__1(v_buf_6341_);
    lean_dec(v_buf_6341_);
    return v_res_6343_;
}
pub unsafe fn l_Lake_withLoggedIO___redArg___lam__2(
    mut v_toPure_6344_: *mut LeanObject,
    mut v_a_6345_: *mut LeanObject,
    mut v_____r_6346_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6347_: *mut LeanObject = core::ptr::null_mut();
    v___x_6347_ = lean_apply_2(v_toPure_6344_, lean_box(0), v_a_6345_);
    return v___x_6347_;
}
pub unsafe fn _init_l_Lake_withLoggedIO___redArg___lam__3___closed__4() -> *mut LeanObject {
    let mut v___x_6352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6357_: *mut LeanObject = core::ptr::null_mut();
    v___x_6352_ = l_Lake_withLoggedIO___redArg___lam__3___closed__3;
    v___x_6353_ = lean_unsigned_to_nat(46);
    v___x_6354_ = lean_unsigned_to_nat(193);
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
    mut v___x_6358_: *mut LeanObject,
    mut v_inst_6359_: *mut LeanObject,
    mut v_toBind_6360_: *mut LeanObject,
    mut v___f_6361_: *mut LeanObject,
    mut v_toPure_6362_: *mut LeanObject,
    mut v_a_6363_: *mut LeanObject,
    mut v_buf_6364_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_6366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6368_: u8 = 0;
    let mut v___x_6369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6374_: u8 = 0;
    let mut v___x_6375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_6379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6380_: u8 = 0;
    let mut v___x_6381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6384_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_data_6379_ = lean_ctor_get(v_buf_6364_, 0);
                lean_inc_ref(v_data_6379_);
                lean_dec_ref(v_buf_6364_);
                v___x_6380_ = lean_string_validate_utf8(v_data_6379_);
                if v___x_6380_ == 0 {
                    lean_dec_ref(v_data_6379_);
                    v___x_6381_ = l_Lake_instInhabitedLogEntry_default___closed__0;
                    v___x_6382_ = lean_obj_once(
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
                    lean_dec(v_a_6363_);
                    lean_dec(v_toPure_6362_);
                    v___x_6369_ = l_Lake_withLoggedIO___redArg___lam__3___closed__0;
                    v___x_6370_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_6370_, 0, v___y_6366_);
                    lean_ctor_set(v___x_6370_, 1, v___x_6358_);
                    lean_ctor_set(v___x_6370_, 2, v___x_6367_);
                    v___x_6371_ = l_String_Slice_trimAscii(v___x_6370_);
                    v___x_6372_ = l_String_Slice_toString(v___x_6371_);
                    lean_dec_ref(v___x_6371_);
                    v___x_6373_ = lean_string_append(v___x_6369_, v___x_6372_);
                    lean_dec_ref(v___x_6372_);
                    v___x_6374_ = 1;
                    v___x_6375_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v___x_6375_, 0, v___x_6373_);
                    lean_ctor_set_uint8(
                        v___x_6375_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___x_6374_,
                    );
                    v___x_6376_ = lean_apply_1(v_inst_6359_, v___x_6375_);
                    v___x_6377_ = lean_apply_4(
                        v_toBind_6360_,
                        lean_box(0),
                        lean_box(0),
                        v___x_6376_,
                        v___f_6361_,
                    );
                    return v___x_6377_;
                } else {
                    lean_dec_ref(v___y_6366_);
                    lean_dec(v___f_6361_);
                    lean_dec(v_toBind_6360_);
                    lean_dec(v_inst_6359_);
                    lean_dec(v___x_6358_);
                    v___x_6378_ = lean_apply_2(v_toPure_6362_, lean_box(0), v_a_6363_);
                    return v___x_6378_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_withLoggedIO___redArg___lam__4(
    mut v_toPure_6385_: *mut LeanObject,
    mut v___x_6386_: *mut LeanObject,
    mut v_inst_6387_: *mut LeanObject,
    mut v_toBind_6388_: *mut LeanObject,
    mut v_inst_6389_: *mut LeanObject,
    mut v___f_6390_: *mut LeanObject,
    mut v_a_6391_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6395_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_6391_);
    lean_inc(v_toPure_6385_);
    v___f_6392_ = lean_alloc_closure(
        l_Lake_withLoggedIO___redArg___lam__2 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_6392_, 0, v_toPure_6385_);
    lean_closure_set(v___f_6392_, 1, v_a_6391_);
    lean_inc(v_toBind_6388_);
    v___f_6393_ = lean_alloc_closure(
        l_Lake_withLoggedIO___redArg___lam__3 as *mut core::ffi::c_void,
        7,
        6,
    );
    lean_closure_set(v___f_6393_, 0, v___x_6386_);
    lean_closure_set(v___f_6393_, 1, v_inst_6387_);
    lean_closure_set(v___f_6393_, 2, v_toBind_6388_);
    lean_closure_set(v___f_6393_, 3, v___f_6392_);
    lean_closure_set(v___f_6393_, 4, v_toPure_6385_);
    lean_closure_set(v___f_6393_, 5, v_a_6391_);
    v___x_6394_ = lean_apply_2(v_inst_6389_, lean_box(0), v___f_6390_);
    v___x_6395_ = lean_apply_4(
        v_toBind_6388_,
        lean_box(0),
        lean_box(0),
        v___x_6394_,
        v___f_6393_,
    );
    return v___x_6395_;
}
pub unsafe fn l_Lake_withLoggedIO___redArg___lam__5(
    mut v_stderr_6396_: *mut LeanObject,
    mut v_inst_6397_: *mut LeanObject,
    mut v_mapConst_6398_: *mut LeanObject,
    mut v_____r_6399_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6403_: *mut LeanObject = core::ptr::null_mut();
    v___x_6400_ = lean_alloc_closure(l_IO_setStderr___boxed as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___x_6400_, 0, v_stderr_6396_);
    v___x_6401_ = lean_apply_2(v_inst_6397_, lean_box(0), v___x_6400_);
    v___x_6402_ = lean_box(0);
    v___x_6403_ = lean_apply_4(
        v_mapConst_6398_,
        lean_box(0),
        lean_box(0),
        v___x_6402_,
        v___x_6401_,
    );
    return v___x_6403_;
}
pub unsafe fn l_Lake_withLoggedIO___redArg___lam__6(
    mut v___x_6404_: *mut LeanObject,
    mut v_x_6405_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v___x_6404_);
    return v___x_6404_;
}
pub unsafe fn l_Lake_withLoggedIO___redArg___lam__6___boxed(
    mut v___x_6406_: *mut LeanObject,
    mut v_x_6407_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6408_: *mut LeanObject = core::ptr::null_mut();
    v_res_6408_ = l_Lake_withLoggedIO___redArg___lam__6(v___x_6406_, v_x_6407_);
    lean_dec(v_x_6407_);
    lean_dec(v___x_6406_);
    return v_res_6408_;
}
pub unsafe fn l_Lake_withLoggedIO___redArg___lam__7(
    mut v_toFunctor_6409_: *mut LeanObject,
    mut v_inst_6410_: *mut LeanObject,
    mut v_stdout_6411_: *mut LeanObject,
    mut v_toBind_6412_: *mut LeanObject,
    mut v_inst_6413_: *mut LeanObject,
    mut v_x_6414_: *mut LeanObject,
    mut v___f_6415_: *mut LeanObject,
    mut v___f_6416_: *mut LeanObject,
    mut v_stderr_6417_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_6418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mapConst_6419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_6427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6429_: *mut LeanObject = core::ptr::null_mut();
    v_map_6418_ = lean_ctor_get(v_toFunctor_6409_, 0);
    lean_inc(v_map_6418_);
    v_mapConst_6419_ = lean_ctor_get(v_toFunctor_6409_, 1);
    lean_inc_n(v_mapConst_6419_, 2);
    lean_dec_ref(v_toFunctor_6409_);
    lean_inc(v_inst_6410_);
    v___f_6420_ = lean_alloc_closure(
        l_Lake_withLoggedIO___redArg___lam__5 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_6420_, 0, v_stderr_6417_);
    lean_closure_set(v___f_6420_, 1, v_inst_6410_);
    lean_closure_set(v___f_6420_, 2, v_mapConst_6419_);
    v___x_6421_ = lean_alloc_closure(l_IO_setStdout___boxed as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___x_6421_, 0, v_stdout_6411_);
    v___x_6422_ = lean_apply_2(v_inst_6410_, lean_box(0), v___x_6421_);
    v___x_6423_ = lean_box(0);
    v___x_6424_ = lean_apply_4(
        v_mapConst_6419_,
        lean_box(0),
        lean_box(0),
        v___x_6423_,
        v___x_6422_,
    );
    lean_inc(v_toBind_6412_);
    v___x_6425_ = lean_apply_4(
        v_toBind_6412_,
        lean_box(0),
        lean_box(0),
        v___x_6424_,
        v___f_6420_,
    );
    v___f_6426_ = lean_alloc_closure(
        l_Lake_withLoggedIO___redArg___lam__6___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_6426_, 0, v___x_6425_);
    v_y_6427_ = lean_apply_4(
        v_inst_6413_,
        lean_box(0),
        lean_box(0),
        v_x_6414_,
        v___f_6426_,
    );
    v___x_6428_ = lean_apply_4(
        v_map_6418_,
        lean_box(0),
        lean_box(0),
        v___f_6415_,
        v_y_6427_,
    );
    v___x_6429_ = lean_apply_4(
        v_toBind_6412_,
        lean_box(0),
        lean_box(0),
        v___x_6428_,
        v___f_6416_,
    );
    return v___x_6429_;
}
pub unsafe fn l_Lake_withLoggedIO___redArg___lam__8(
    mut v_toFunctor_6430_: *mut LeanObject,
    mut v_inst_6431_: *mut LeanObject,
    mut v_toBind_6432_: *mut LeanObject,
    mut v_inst_6433_: *mut LeanObject,
    mut v_x_6434_: *mut LeanObject,
    mut v___f_6435_: *mut LeanObject,
    mut v___f_6436_: *mut LeanObject,
    mut v___x_6437_: *mut LeanObject,
    mut v_stdout_6438_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6442_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_toBind_6432_);
    lean_inc(v_inst_6431_);
    v___f_6439_ = lean_alloc_closure(
        l_Lake_withLoggedIO___redArg___lam__7 as *mut core::ffi::c_void,
        9,
        8,
    );
    lean_closure_set(v___f_6439_, 0, v_toFunctor_6430_);
    lean_closure_set(v___f_6439_, 1, v_inst_6431_);
    lean_closure_set(v___f_6439_, 2, v_stdout_6438_);
    lean_closure_set(v___f_6439_, 3, v_toBind_6432_);
    lean_closure_set(v___f_6439_, 4, v_inst_6433_);
    lean_closure_set(v___f_6439_, 5, v_x_6434_);
    lean_closure_set(v___f_6439_, 6, v___f_6435_);
    lean_closure_set(v___f_6439_, 7, v___f_6436_);
    v___x_6440_ = lean_alloc_closure(l_IO_setStderr___boxed as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___x_6440_, 0, v___x_6437_);
    v___x_6441_ = lean_apply_2(v_inst_6431_, lean_box(0), v___x_6440_);
    v___x_6442_ = lean_apply_4(
        v_toBind_6432_,
        lean_box(0),
        lean_box(0),
        v___x_6441_,
        v___f_6439_,
    );
    return v___x_6442_;
}
pub unsafe fn l_Lake_withLoggedIO___redArg___lam__9(
    mut v_toPure_6443_: *mut LeanObject,
    mut v___x_6444_: *mut LeanObject,
    mut v_inst_6445_: *mut LeanObject,
    mut v_toBind_6446_: *mut LeanObject,
    mut v_inst_6447_: *mut LeanObject,
    mut v_toFunctor_6448_: *mut LeanObject,
    mut v_inst_6449_: *mut LeanObject,
    mut v_x_6450_: *mut LeanObject,
    mut v___f_6451_: *mut LeanObject,
    mut v_buf_6452_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6459_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_buf_6452_);
    v___f_6453_ = lean_alloc_closure(
        l_Lake_withLoggedIO___redArg___lam__1___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_6453_, 0, v_buf_6452_);
    lean_inc_n(v_inst_6447_, 2);
    lean_inc_n(v_toBind_6446_, 2);
    v___f_6454_ = lean_alloc_closure(
        l_Lake_withLoggedIO___redArg___lam__4 as *mut core::ffi::c_void,
        7,
        6,
    );
    lean_closure_set(v___f_6454_, 0, v_toPure_6443_);
    lean_closure_set(v___f_6454_, 1, v___x_6444_);
    lean_closure_set(v___f_6454_, 2, v_inst_6445_);
    lean_closure_set(v___f_6454_, 3, v_toBind_6446_);
    lean_closure_set(v___f_6454_, 4, v_inst_6447_);
    lean_closure_set(v___f_6454_, 5, v___f_6453_);
    v___x_6455_ = l_IO_FS_Stream_ofBuffer(v_buf_6452_);
    lean_inc_ref(v___x_6455_);
    v___f_6456_ = lean_alloc_closure(
        l_Lake_withLoggedIO___redArg___lam__8 as *mut core::ffi::c_void,
        9,
        8,
    );
    lean_closure_set(v___f_6456_, 0, v_toFunctor_6448_);
    lean_closure_set(v___f_6456_, 1, v_inst_6447_);
    lean_closure_set(v___f_6456_, 2, v_toBind_6446_);
    lean_closure_set(v___f_6456_, 3, v_inst_6449_);
    lean_closure_set(v___f_6456_, 4, v_x_6450_);
    lean_closure_set(v___f_6456_, 5, v___f_6451_);
    lean_closure_set(v___f_6456_, 6, v___f_6454_);
    lean_closure_set(v___f_6456_, 7, v___x_6455_);
    v___x_6457_ = lean_alloc_closure(l_IO_setStdout___boxed as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___x_6457_, 0, v___x_6455_);
    v___x_6458_ = lean_apply_2(v_inst_6447_, lean_box(0), v___x_6457_);
    v___x_6459_ = lean_apply_4(
        v_toBind_6446_,
        lean_box(0),
        lean_box(0),
        v___x_6458_,
        v___f_6456_,
    );
    return v___x_6459_;
}
pub unsafe fn _init_l_Lake_withLoggedIO___redArg___closed__1() -> *mut LeanObject {
    let mut v___x_6461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6463_: *mut LeanObject = core::ptr::null_mut();
    v___x_6461_ = lean_unsigned_to_nat(0);
    v___x_6462_ = l_ByteArray_empty;
    v___x_6463_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_6463_, 0, v___x_6462_);
    lean_ctor_set(v___x_6463_, 1, v___x_6461_);
    return v___x_6463_;
}
pub unsafe fn _init_l_Lake_withLoggedIO___redArg___closed__2() -> *mut LeanObject {
    let mut v___x_6464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6465_: *mut LeanObject = core::ptr::null_mut();
    v___x_6464_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_withLoggedIO___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lake_withLoggedIO___redArg___closed__1_once),
        _init_l_Lake_withLoggedIO___redArg___closed__1,
    );
    v___x_6465_ = lean_alloc_closure(l_IO_mkRef___boxed as *mut core::ffi::c_void, 3, 2);
    lean_closure_set(v___x_6465_, 0, lean_box(0));
    lean_closure_set(v___x_6465_, 1, v___x_6464_);
    return v___x_6465_;
}
pub unsafe fn l_Lake_withLoggedIO___redArg(
    mut v_inst_6466_: *mut LeanObject,
    mut v_inst_6467_: *mut LeanObject,
    mut v_inst_6468_: *mut LeanObject,
    mut v_inst_6469_: *mut LeanObject,
    mut v_x_6470_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_6471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_6472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_6473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_6474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6480_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_6471_ = lean_ctor_get(v_inst_6466_, 0);
    lean_inc_ref(v_toApplicative_6471_);
    v_toBind_6472_ = lean_ctor_get(v_inst_6466_, 1);
    lean_inc_n(v_toBind_6472_, 2);
    lean_dec_ref(v_inst_6466_);
    v_toFunctor_6473_ = lean_ctor_get(v_toApplicative_6471_, 0);
    lean_inc_ref(v_toFunctor_6473_);
    v_toPure_6474_ = lean_ctor_get(v_toApplicative_6471_, 1);
    lean_inc(v_toPure_6474_);
    lean_dec_ref(v_toApplicative_6471_);
    v___f_6475_ = l_Lake_withLoggedIO___redArg___closed__0;
    v___x_6476_ = lean_unsigned_to_nat(0);
    v___x_6477_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_withLoggedIO___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Lake_withLoggedIO___redArg___closed__2_once),
        _init_l_Lake_withLoggedIO___redArg___closed__2,
    );
    lean_inc(v_inst_6467_);
    v___x_6478_ = lean_apply_2(v_inst_6467_, lean_box(0), v___x_6477_);
    v___f_6479_ = lean_alloc_closure(
        l_Lake_withLoggedIO___redArg___lam__9 as *mut core::ffi::c_void,
        10,
        9,
    );
    lean_closure_set(v___f_6479_, 0, v_toPure_6474_);
    lean_closure_set(v___f_6479_, 1, v___x_6476_);
    lean_closure_set(v___f_6479_, 2, v_inst_6468_);
    lean_closure_set(v___f_6479_, 3, v_toBind_6472_);
    lean_closure_set(v___f_6479_, 4, v_inst_6467_);
    lean_closure_set(v___f_6479_, 5, v_toFunctor_6473_);
    lean_closure_set(v___f_6479_, 6, v_inst_6469_);
    lean_closure_set(v___f_6479_, 7, v_x_6470_);
    lean_closure_set(v___f_6479_, 8, v___f_6475_);
    v___x_6480_ = lean_apply_4(
        v_toBind_6472_,
        lean_box(0),
        lean_box(0),
        v___x_6478_,
        v___f_6479_,
    );
    return v___x_6480_;
}
pub unsafe fn l_Lake_withLoggedIO(
    mut v_m_6481_: *mut LeanObject,
    mut v_00_u03b1_6482_: *mut LeanObject,
    mut v_inst_6483_: *mut LeanObject,
    mut v_inst_6484_: *mut LeanObject,
    mut v_inst_6485_: *mut LeanObject,
    mut v_inst_6486_: *mut LeanObject,
    mut v_x_6487_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_6488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_6489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_6490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_6491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6497_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_6488_ = lean_ctor_get(v_inst_6483_, 0);
    lean_inc_ref(v_toApplicative_6488_);
    v_toBind_6489_ = lean_ctor_get(v_inst_6483_, 1);
    lean_inc_n(v_toBind_6489_, 2);
    lean_dec_ref(v_inst_6483_);
    v_toFunctor_6490_ = lean_ctor_get(v_toApplicative_6488_, 0);
    lean_inc_ref(v_toFunctor_6490_);
    v_toPure_6491_ = lean_ctor_get(v_toApplicative_6488_, 1);
    lean_inc(v_toPure_6491_);
    lean_dec_ref(v_toApplicative_6488_);
    v___f_6492_ = l_Lake_withLoggedIO___redArg___closed__0;
    v___x_6493_ = lean_unsigned_to_nat(0);
    v___x_6494_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_withLoggedIO___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Lake_withLoggedIO___redArg___closed__2_once),
        _init_l_Lake_withLoggedIO___redArg___closed__2,
    );
    lean_inc(v_inst_6484_);
    v___x_6495_ = lean_apply_2(v_inst_6484_, lean_box(0), v___x_6494_);
    v___f_6496_ = lean_alloc_closure(
        l_Lake_withLoggedIO___redArg___lam__9 as *mut core::ffi::c_void,
        10,
        9,
    );
    lean_closure_set(v___f_6496_, 0, v_toPure_6491_);
    lean_closure_set(v___f_6496_, 1, v___x_6493_);
    lean_closure_set(v___f_6496_, 2, v_inst_6485_);
    lean_closure_set(v___f_6496_, 3, v_toBind_6489_);
    lean_closure_set(v___f_6496_, 4, v_inst_6484_);
    lean_closure_set(v___f_6496_, 5, v_toFunctor_6490_);
    lean_closure_set(v___f_6496_, 6, v_inst_6486_);
    lean_closure_set(v___f_6496_, 7, v_x_6487_);
    lean_closure_set(v___f_6496_, 8, v___f_6492_);
    v___x_6497_ = lean_apply_4(
        v_toBind_6489_,
        lean_box(0),
        lean_box(0),
        v___x_6495_,
        v___f_6496_,
    );
    return v___x_6497_;
}
pub unsafe fn l_Lake_ELog_error___redArg___lam__3(
    mut v_inst_6498_: *mut LeanObject,
    mut v___x_6499_: *mut LeanObject,
    mut v___f_6500_: *mut LeanObject,
    mut v_toBind_6501_: *mut LeanObject,
    mut v_iniPos_6502_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_throw_6503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tryCatch_6504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6507_: *mut LeanObject = core::ptr::null_mut();
    v_throw_6503_ = lean_ctor_get(v_inst_6498_, 0);
    lean_inc(v_throw_6503_);
    v_tryCatch_6504_ = lean_ctor_get(v_inst_6498_, 1);
    lean_inc(v_tryCatch_6504_);
    lean_dec_ref(v_inst_6498_);
    v___f_6505_ = lean_alloc_closure(
        l_Lake_errorWithLog___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_6505_, 0, v_throw_6503_);
    lean_closure_set(v___f_6505_, 1, v_iniPos_6502_);
    v___x_6506_ = lean_apply_3(v_tryCatch_6504_, lean_box(0), v___x_6499_, v___f_6500_);
    v___x_6507_ = lean_apply_4(
        v_toBind_6501_,
        lean_box(0),
        lean_box(0),
        v___x_6506_,
        v___f_6505_,
    );
    return v___x_6507_;
}
pub unsafe fn l_Lake_ELog_error___redArg(
    mut v_inst_6508_: *mut LeanObject,
    mut v_inst_6509_: *mut LeanObject,
    mut v_inst_6510_: *mut LeanObject,
    mut v_inst_6511_: *mut LeanObject,
    mut v_msg_6512_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_6513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_6514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_6515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_6516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_6517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_get_6518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6520_: u8 = 0;
    let mut v___x_6521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6526_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_6513_ = lean_ctor_get(v_inst_6508_, 0);
    lean_inc_ref(v_toApplicative_6513_);
    v_toFunctor_6514_ = lean_ctor_get(v_toApplicative_6513_, 0);
    lean_inc_ref(v_toFunctor_6514_);
    v_toBind_6515_ = lean_ctor_get(v_inst_6508_, 1);
    lean_inc_n(v_toBind_6515_, 2);
    lean_dec_ref(v_inst_6508_);
    v_toPure_6516_ = lean_ctor_get(v_toApplicative_6513_, 1);
    lean_inc(v_toPure_6516_);
    lean_dec_ref(v_toApplicative_6513_);
    v_map_6517_ = lean_ctor_get(v_toFunctor_6514_, 0);
    lean_inc(v_map_6517_);
    lean_dec_ref(v_toFunctor_6514_);
    v_get_6518_ = lean_ctor_get(v_inst_6510_, 0);
    lean_inc(v_get_6518_);
    lean_dec_ref(v_inst_6510_);
    v___f_6519_ = l_Lake_getLogPos___redArg___closed__0;
    v___x_6520_ = 3;
    v___x_6521_ = lean_alloc_ctor(0, 1, (1) as u32);
    lean_ctor_set(v___x_6521_, 0, v_msg_6512_);
    lean_ctor_set_uint8(
        v___x_6521_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_6520_,
    );
    v___x_6522_ = lean_apply_1(v_inst_6509_, v___x_6521_);
    v___f_6523_ = lean_alloc_closure(
        l_Lake_errorWithLog___redArg___lam__1___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_6523_, 0, v_toPure_6516_);
    v___f_6524_ = lean_alloc_closure(
        l_Lake_ELog_error___redArg___lam__3 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_6524_, 0, v_inst_6511_);
    lean_closure_set(v___f_6524_, 1, v___x_6522_);
    lean_closure_set(v___f_6524_, 2, v___f_6523_);
    lean_closure_set(v___f_6524_, 3, v_toBind_6515_);
    v___x_6525_ = lean_apply_4(
        v_map_6517_,
        lean_box(0),
        lean_box(0),
        v___f_6519_,
        v_get_6518_,
    );
    v___x_6526_ = lean_apply_4(
        v_toBind_6515_,
        lean_box(0),
        lean_box(0),
        v___x_6525_,
        v___f_6524_,
    );
    return v___x_6526_;
}
pub unsafe fn l_Lake_ELog_error(
    mut v_m_6527_: *mut LeanObject,
    mut v_00_u03b1_6528_: *mut LeanObject,
    mut v_inst_6529_: *mut LeanObject,
    mut v_inst_6530_: *mut LeanObject,
    mut v_inst_6531_: *mut LeanObject,
    mut v_inst_6532_: *mut LeanObject,
    mut v_msg_6533_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_6534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_6535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_6536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_6537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_6538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_get_6539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6541_: u8 = 0;
    let mut v___x_6542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6547_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_6534_ = lean_ctor_get(v_inst_6529_, 0);
    lean_inc_ref(v_toApplicative_6534_);
    v_toFunctor_6535_ = lean_ctor_get(v_toApplicative_6534_, 0);
    lean_inc_ref(v_toFunctor_6535_);
    v_toBind_6536_ = lean_ctor_get(v_inst_6529_, 1);
    lean_inc_n(v_toBind_6536_, 2);
    lean_dec_ref(v_inst_6529_);
    v_toPure_6537_ = lean_ctor_get(v_toApplicative_6534_, 1);
    lean_inc(v_toPure_6537_);
    lean_dec_ref(v_toApplicative_6534_);
    v_map_6538_ = lean_ctor_get(v_toFunctor_6535_, 0);
    lean_inc(v_map_6538_);
    lean_dec_ref(v_toFunctor_6535_);
    v_get_6539_ = lean_ctor_get(v_inst_6531_, 0);
    lean_inc(v_get_6539_);
    lean_dec_ref(v_inst_6531_);
    v___f_6540_ = l_Lake_getLogPos___redArg___closed__0;
    v___x_6541_ = 3;
    v___x_6542_ = lean_alloc_ctor(0, 1, (1) as u32);
    lean_ctor_set(v___x_6542_, 0, v_msg_6533_);
    lean_ctor_set_uint8(
        v___x_6542_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_6541_,
    );
    v___x_6543_ = lean_apply_1(v_inst_6530_, v___x_6542_);
    v___f_6544_ = lean_alloc_closure(
        l_Lake_errorWithLog___redArg___lam__1___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_6544_, 0, v_toPure_6537_);
    v___f_6545_ = lean_alloc_closure(
        l_Lake_ELog_error___redArg___lam__3 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_6545_, 0, v_inst_6532_);
    lean_closure_set(v___f_6545_, 1, v___x_6543_);
    lean_closure_set(v___f_6545_, 2, v___f_6544_);
    lean_closure_set(v___f_6545_, 3, v_toBind_6536_);
    v___x_6546_ = lean_apply_4(
        v_map_6538_,
        lean_box(0),
        lean_box(0),
        v___f_6540_,
        v_get_6539_,
    );
    v___x_6547_ = lean_apply_4(
        v_toBind_6536_,
        lean_box(0),
        lean_box(0),
        v___x_6546_,
        v___f_6545_,
    );
    return v___x_6547_;
}
pub unsafe fn l_Lake_ELog_monadError___redArg___lam__4(
    mut v_inst_6548_: *mut LeanObject,
    mut v_inst_6549_: *mut LeanObject,
    mut v_inst_6550_: *mut LeanObject,
    mut v_inst_6551_: *mut LeanObject,
    mut v___f_6552_: *mut LeanObject,
    mut v_00_u03b1_6553_: *mut LeanObject,
    mut v___y_6554_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_6555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_6556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_6557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_6558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_6559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_get_6560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6561_: u8 = 0;
    let mut v___x_6562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6567_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_6555_ = lean_ctor_get(v_inst_6548_, 0);
    lean_inc_ref(v_toApplicative_6555_);
    v_toFunctor_6556_ = lean_ctor_get(v_toApplicative_6555_, 0);
    lean_inc_ref(v_toFunctor_6556_);
    v_toBind_6557_ = lean_ctor_get(v_inst_6548_, 1);
    lean_inc_n(v_toBind_6557_, 2);
    lean_dec_ref(v_inst_6548_);
    v_toPure_6558_ = lean_ctor_get(v_toApplicative_6555_, 1);
    lean_inc(v_toPure_6558_);
    lean_dec_ref(v_toApplicative_6555_);
    v_map_6559_ = lean_ctor_get(v_toFunctor_6556_, 0);
    lean_inc(v_map_6559_);
    lean_dec_ref(v_toFunctor_6556_);
    v_get_6560_ = lean_ctor_get(v_inst_6549_, 0);
    lean_inc(v_get_6560_);
    lean_dec_ref(v_inst_6549_);
    v___x_6561_ = 3;
    v___x_6562_ = lean_alloc_ctor(0, 1, (1) as u32);
    lean_ctor_set(v___x_6562_, 0, v___y_6554_);
    lean_ctor_set_uint8(
        v___x_6562_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_6561_,
    );
    v___x_6563_ = lean_apply_1(v_inst_6550_, v___x_6562_);
    v___f_6564_ = lean_alloc_closure(
        l_Lake_errorWithLog___redArg___lam__1___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_6564_, 0, v_toPure_6558_);
    v___f_6565_ = lean_alloc_closure(
        l_Lake_ELog_error___redArg___lam__3 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_6565_, 0, v_inst_6551_);
    lean_closure_set(v___f_6565_, 1, v___x_6563_);
    lean_closure_set(v___f_6565_, 2, v___f_6564_);
    lean_closure_set(v___f_6565_, 3, v_toBind_6557_);
    v___x_6566_ = lean_apply_4(
        v_map_6559_,
        lean_box(0),
        lean_box(0),
        v___f_6552_,
        v_get_6560_,
    );
    v___x_6567_ = lean_apply_4(
        v_toBind_6557_,
        lean_box(0),
        lean_box(0),
        v___x_6566_,
        v___f_6565_,
    );
    return v___x_6567_;
}
pub unsafe fn l_Lake_ELog_monadError___redArg(
    mut v_inst_6568_: *mut LeanObject,
    mut v_inst_6569_: *mut LeanObject,
    mut v_inst_6570_: *mut LeanObject,
    mut v_inst_6571_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6573_: *mut LeanObject = core::ptr::null_mut();
    v___f_6572_ = l_Lake_getLogPos___redArg___closed__0;
    v___f_6573_ = lean_alloc_closure(
        l_Lake_ELog_monadError___redArg___lam__4 as *mut core::ffi::c_void,
        7,
        5,
    );
    lean_closure_set(v___f_6573_, 0, v_inst_6568_);
    lean_closure_set(v___f_6573_, 1, v_inst_6570_);
    lean_closure_set(v___f_6573_, 2, v_inst_6569_);
    lean_closure_set(v___f_6573_, 3, v_inst_6571_);
    lean_closure_set(v___f_6573_, 4, v___f_6572_);
    return v___f_6573_;
}
pub unsafe fn l_Lake_ELog_monadError(
    mut v_m_6574_: *mut LeanObject,
    mut v_inst_6575_: *mut LeanObject,
    mut v_inst_6576_: *mut LeanObject,
    mut v_inst_6577_: *mut LeanObject,
    mut v_inst_6578_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6580_: *mut LeanObject = core::ptr::null_mut();
    v___f_6579_ = l_Lake_getLogPos___redArg___closed__0;
    v___f_6580_ = lean_alloc_closure(
        l_Lake_ELog_monadError___redArg___lam__4 as *mut core::ffi::c_void,
        7,
        5,
    );
    lean_closure_set(v___f_6580_, 0, v_inst_6575_);
    lean_closure_set(v___f_6580_, 1, v_inst_6577_);
    lean_closure_set(v___f_6580_, 2, v_inst_6576_);
    lean_closure_set(v___f_6580_, 3, v_inst_6578_);
    lean_closure_set(v___f_6580_, 4, v___f_6579_);
    return v___f_6580_;
}
pub unsafe fn l_Lake_ELog_failure___redArg___lam__1(
    mut v_inst_6581_: *mut LeanObject,
    mut v_____do__lift_6582_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_throw_6583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6584_: *mut LeanObject = core::ptr::null_mut();
    v_throw_6583_ = lean_ctor_get(v_inst_6581_, 0);
    lean_inc(v_throw_6583_);
    lean_dec_ref(v_inst_6581_);
    v___x_6584_ = lean_apply_2(v_throw_6583_, lean_box(0), v_____do__lift_6582_);
    return v___x_6584_;
}
pub unsafe fn l_Lake_ELog_failure___redArg(
    mut v_inst_6585_: *mut LeanObject,
    mut v_inst_6586_: *mut LeanObject,
    mut v_inst_6587_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_6588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_6589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_6590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_6591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_get_6592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6596_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_6588_ = lean_ctor_get(v_inst_6585_, 0);
    v_toFunctor_6589_ = lean_ctor_get(v_toApplicative_6588_, 0);
    lean_inc_ref(v_toFunctor_6589_);
    v_toBind_6590_ = lean_ctor_get(v_inst_6585_, 1);
    lean_inc(v_toBind_6590_);
    lean_dec_ref(v_inst_6585_);
    v_map_6591_ = lean_ctor_get(v_toFunctor_6589_, 0);
    lean_inc(v_map_6591_);
    lean_dec_ref(v_toFunctor_6589_);
    v_get_6592_ = lean_ctor_get(v_inst_6586_, 0);
    lean_inc(v_get_6592_);
    lean_dec_ref(v_inst_6586_);
    v___f_6593_ = l_Lake_getLogPos___redArg___closed__0;
    v___f_6594_ = lean_alloc_closure(
        l_Lake_ELog_failure___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_6594_, 0, v_inst_6587_);
    v___x_6595_ = lean_apply_4(
        v_map_6591_,
        lean_box(0),
        lean_box(0),
        v___f_6593_,
        v_get_6592_,
    );
    v___x_6596_ = lean_apply_4(
        v_toBind_6590_,
        lean_box(0),
        lean_box(0),
        v___x_6595_,
        v___f_6594_,
    );
    return v___x_6596_;
}
pub unsafe fn l_Lake_ELog_failure(
    mut v_m_6597_: *mut LeanObject,
    mut v_00_u03b1_6598_: *mut LeanObject,
    mut v_inst_6599_: *mut LeanObject,
    mut v_inst_6600_: *mut LeanObject,
    mut v_inst_6601_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_6602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_6603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_6604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_6605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_get_6606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6610_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_6602_ = lean_ctor_get(v_inst_6599_, 0);
    v_toFunctor_6603_ = lean_ctor_get(v_toApplicative_6602_, 0);
    lean_inc_ref(v_toFunctor_6603_);
    v_toBind_6604_ = lean_ctor_get(v_inst_6599_, 1);
    lean_inc(v_toBind_6604_);
    lean_dec_ref(v_inst_6599_);
    v_map_6605_ = lean_ctor_get(v_toFunctor_6603_, 0);
    lean_inc(v_map_6605_);
    lean_dec_ref(v_toFunctor_6603_);
    v_get_6606_ = lean_ctor_get(v_inst_6600_, 0);
    lean_inc(v_get_6606_);
    lean_dec_ref(v_inst_6600_);
    v___f_6607_ = l_Lake_getLogPos___redArg___closed__0;
    v___f_6608_ = lean_alloc_closure(
        l_Lake_ELog_failure___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_6608_, 0, v_inst_6601_);
    v___x_6609_ = lean_apply_4(
        v_map_6605_,
        lean_box(0),
        lean_box(0),
        v___f_6607_,
        v_get_6606_,
    );
    v___x_6610_ = lean_apply_4(
        v_toBind_6604_,
        lean_box(0),
        lean_box(0),
        v___x_6609_,
        v___f_6608_,
    );
    return v___x_6610_;
}
pub unsafe fn l_Lake_ELog_orElse___redArg___lam__0(
    mut v_y_6611_: *mut LeanObject,
    mut v_____r_6612_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6614_: *mut LeanObject = core::ptr::null_mut();
    v___x_6613_ = lean_box(0);
    v___x_6614_ = lean_apply_1(v_y_6611_, v___x_6613_);
    return v___x_6614_;
}
pub unsafe fn l_Lake_ELog_orElse___redArg___lam__1(
    mut v_errPos_6615_: *mut LeanObject,
    mut v_s_6616_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6619_: *mut LeanObject = core::ptr::null_mut();
    v___x_6617_ = lean_box(0);
    v___x_6618_ = l_Array_shrink___redArg(v_s_6616_, v_errPos_6615_);
    v___x_6619_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_6619_, 0, v___x_6617_);
    lean_ctor_set(v___x_6619_, 1, v___x_6618_);
    return v___x_6619_;
}
pub unsafe fn l_Lake_ELog_orElse___redArg___lam__1___boxed(
    mut v_errPos_6620_: *mut LeanObject,
    mut v_s_6621_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6622_: *mut LeanObject = core::ptr::null_mut();
    v_res_6622_ = l_Lake_ELog_orElse___redArg___lam__1(v_errPos_6620_, v_s_6621_);
    lean_dec(v_errPos_6620_);
    return v_res_6622_;
}
pub unsafe fn l_Lake_ELog_orElse___redArg___lam__2(
    mut v_inst_6623_: *mut LeanObject,
    mut v_toBind_6624_: *mut LeanObject,
    mut v___f_6625_: *mut LeanObject,
    mut v_errPos_6626_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_modifyGet_6627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6630_: *mut LeanObject = core::ptr::null_mut();
    v_modifyGet_6627_ = lean_ctor_get(v_inst_6623_, 2);
    lean_inc(v_modifyGet_6627_);
    lean_dec_ref(v_inst_6623_);
    v___f_6628_ = lean_alloc_closure(
        l_Lake_ELog_orElse___redArg___lam__1___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_6628_, 0, v_errPos_6626_);
    v___x_6629_ = lean_apply_2(v_modifyGet_6627_, lean_box(0), v___f_6628_);
    v___x_6630_ = lean_apply_4(
        v_toBind_6624_,
        lean_box(0),
        lean_box(0),
        v___x_6629_,
        v___f_6625_,
    );
    return v___x_6630_;
}
pub unsafe fn l_Lake_ELog_orElse___redArg(
    mut v_inst_6631_: *mut LeanObject,
    mut v_inst_6632_: *mut LeanObject,
    mut v_inst_6633_: *mut LeanObject,
    mut v_x_6634_: *mut LeanObject,
    mut v_y_6635_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_6636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tryCatch_6637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6640_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_6636_ = lean_ctor_get(v_inst_6631_, 1);
    lean_inc(v_toBind_6636_);
    lean_dec_ref(v_inst_6631_);
    v_tryCatch_6637_ = lean_ctor_get(v_inst_6633_, 1);
    lean_inc(v_tryCatch_6637_);
    lean_dec_ref(v_inst_6633_);
    v___f_6638_ = lean_alloc_closure(
        l_Lake_ELog_orElse___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_6638_, 0, v_y_6635_);
    v___f_6639_ = lean_alloc_closure(
        l_Lake_ELog_orElse___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_6639_, 0, v_inst_6632_);
    lean_closure_set(v___f_6639_, 1, v_toBind_6636_);
    lean_closure_set(v___f_6639_, 2, v___f_6638_);
    v___x_6640_ = lean_apply_3(v_tryCatch_6637_, lean_box(0), v_x_6634_, v___f_6639_);
    return v___x_6640_;
}
pub unsafe fn l_Lake_ELog_orElse(
    mut v_m_6641_: *mut LeanObject,
    mut v_00_u03b1_6642_: *mut LeanObject,
    mut v_inst_6643_: *mut LeanObject,
    mut v_inst_6644_: *mut LeanObject,
    mut v_inst_6645_: *mut LeanObject,
    mut v_x_6646_: *mut LeanObject,
    mut v_y_6647_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_6648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tryCatch_6649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6652_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_6648_ = lean_ctor_get(v_inst_6643_, 1);
    lean_inc(v_toBind_6648_);
    lean_dec_ref(v_inst_6643_);
    v_tryCatch_6649_ = lean_ctor_get(v_inst_6645_, 1);
    lean_inc(v_tryCatch_6649_);
    lean_dec_ref(v_inst_6645_);
    v___f_6650_ = lean_alloc_closure(
        l_Lake_ELog_orElse___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_6650_, 0, v_y_6647_);
    v___f_6651_ = lean_alloc_closure(
        l_Lake_ELog_orElse___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_6651_, 0, v_inst_6644_);
    lean_closure_set(v___f_6651_, 1, v_toBind_6648_);
    lean_closure_set(v___f_6651_, 2, v___f_6650_);
    v___x_6652_ = lean_apply_3(v_tryCatch_6649_, lean_box(0), v_x_6646_, v___f_6651_);
    return v___x_6652_;
}
pub unsafe fn l_Lake_ELog_alternative___redArg___lam__2(
    mut v_toApplicative_6653_: *mut LeanObject,
    mut v_inst_6654_: *mut LeanObject,
    mut v___f_6655_: *mut LeanObject,
    mut v_toBind_6656_: *mut LeanObject,
    mut v___f_6657_: *mut LeanObject,
    mut v_00_u03b1_6658_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toFunctor_6659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_6660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_get_6661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6663_: *mut LeanObject = core::ptr::null_mut();
    v_toFunctor_6659_ = lean_ctor_get(v_toApplicative_6653_, 0);
    lean_inc_ref(v_toFunctor_6659_);
    lean_dec_ref(v_toApplicative_6653_);
    v_map_6660_ = lean_ctor_get(v_toFunctor_6659_, 0);
    lean_inc(v_map_6660_);
    lean_dec_ref(v_toFunctor_6659_);
    v_get_6661_ = lean_ctor_get(v_inst_6654_, 0);
    lean_inc(v_get_6661_);
    lean_dec_ref(v_inst_6654_);
    v___x_6662_ = lean_apply_4(
        v_map_6660_,
        lean_box(0),
        lean_box(0),
        v___f_6655_,
        v_get_6661_,
    );
    v___x_6663_ = lean_apply_4(
        v_toBind_6656_,
        lean_box(0),
        lean_box(0),
        v___x_6662_,
        v___f_6657_,
    );
    return v___x_6663_;
}
pub unsafe fn l_Lake_ELog_alternative___redArg___lam__0(
    mut v___y_6664_: *mut LeanObject,
    mut v_____r_6665_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6667_: *mut LeanObject = core::ptr::null_mut();
    v___x_6666_ = lean_box(0);
    v___x_6667_ = lean_apply_1(v___y_6664_, v___x_6666_);
    return v___x_6667_;
}
pub unsafe fn l_Lake_ELog_alternative___redArg___lam__4(
    mut v_inst_6668_: *mut LeanObject,
    mut v_inst_6669_: *mut LeanObject,
    mut v_toBind_6670_: *mut LeanObject,
    mut v_00_u03b1_6671_: *mut LeanObject,
    mut v___y_6672_: *mut LeanObject,
    mut v___y_6673_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_tryCatch_6674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6677_: *mut LeanObject = core::ptr::null_mut();
    v_tryCatch_6674_ = lean_ctor_get(v_inst_6668_, 1);
    lean_inc(v_tryCatch_6674_);
    lean_dec_ref(v_inst_6668_);
    v___f_6675_ = lean_alloc_closure(
        l_Lake_ELog_alternative___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_6675_, 0, v___y_6673_);
    v___f_6676_ = lean_alloc_closure(
        l_Lake_ELog_orElse___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_6676_, 0, v_inst_6669_);
    lean_closure_set(v___f_6676_, 1, v_toBind_6670_);
    lean_closure_set(v___f_6676_, 2, v___f_6675_);
    v___x_6677_ = lean_apply_3(v_tryCatch_6674_, lean_box(0), v___y_6672_, v___f_6676_);
    return v___x_6677_;
}
pub unsafe fn l_Lake_ELog_alternative___redArg(
    mut v_inst_6678_: *mut LeanObject,
    mut v_inst_6679_: *mut LeanObject,
    mut v_inst_6680_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_6681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_6682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6687_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_6681_ = lean_ctor_get(v_inst_6678_, 0);
    lean_inc_ref_n(v_toApplicative_6681_, 2);
    v_toBind_6682_ = lean_ctor_get(v_inst_6678_, 1);
    lean_inc_n(v_toBind_6682_, 2);
    lean_dec_ref(v_inst_6678_);
    v___f_6683_ = l_Lake_getLogPos___redArg___closed__0;
    lean_inc_ref(v_inst_6680_);
    v___f_6684_ = lean_alloc_closure(
        l_Lake_ELog_failure___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_6684_, 0, v_inst_6680_);
    lean_inc_ref(v_inst_6679_);
    v___f_6685_ = lean_alloc_closure(
        l_Lake_ELog_alternative___redArg___lam__2 as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_6685_, 0, v_toApplicative_6681_);
    lean_closure_set(v___f_6685_, 1, v_inst_6679_);
    lean_closure_set(v___f_6685_, 2, v___f_6683_);
    lean_closure_set(v___f_6685_, 3, v_toBind_6682_);
    lean_closure_set(v___f_6685_, 4, v___f_6684_);
    v___f_6686_ = lean_alloc_closure(
        l_Lake_ELog_alternative___redArg___lam__4 as *mut core::ffi::c_void,
        6,
        3,
    );
    lean_closure_set(v___f_6686_, 0, v_inst_6680_);
    lean_closure_set(v___f_6686_, 1, v_inst_6679_);
    lean_closure_set(v___f_6686_, 2, v_toBind_6682_);
    v___x_6687_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_6687_, 0, v_toApplicative_6681_);
    lean_ctor_set(v___x_6687_, 1, v___f_6685_);
    lean_ctor_set(v___x_6687_, 2, v___f_6686_);
    return v___x_6687_;
}
pub unsafe fn l_Lake_ELog_alternative(
    mut v_m_6688_: *mut LeanObject,
    mut v_inst_6689_: *mut LeanObject,
    mut v_inst_6690_: *mut LeanObject,
    mut v_inst_6691_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_6692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_6693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6698_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_6692_ = lean_ctor_get(v_inst_6689_, 0);
    lean_inc_ref_n(v_toApplicative_6692_, 2);
    v_toBind_6693_ = lean_ctor_get(v_inst_6689_, 1);
    lean_inc_n(v_toBind_6693_, 2);
    lean_dec_ref(v_inst_6689_);
    v___f_6694_ = l_Lake_getLogPos___redArg___closed__0;
    lean_inc_ref(v_inst_6691_);
    v___f_6695_ = lean_alloc_closure(
        l_Lake_ELog_failure___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_6695_, 0, v_inst_6691_);
    lean_inc_ref(v_inst_6690_);
    v___f_6696_ = lean_alloc_closure(
        l_Lake_ELog_alternative___redArg___lam__2 as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_6696_, 0, v_toApplicative_6692_);
    lean_closure_set(v___f_6696_, 1, v_inst_6690_);
    lean_closure_set(v___f_6696_, 2, v___f_6694_);
    lean_closure_set(v___f_6696_, 3, v_toBind_6693_);
    lean_closure_set(v___f_6696_, 4, v___f_6695_);
    v___f_6697_ = lean_alloc_closure(
        l_Lake_ELog_alternative___redArg___lam__4 as *mut core::ffi::c_void,
        6,
        3,
    );
    lean_closure_set(v___f_6697_, 0, v_inst_6691_);
    lean_closure_set(v___f_6697_, 1, v_inst_6690_);
    lean_closure_set(v___f_6697_, 2, v_toBind_6693_);
    v___x_6698_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_6698_, 0, v_toApplicative_6692_);
    lean_ctor_set(v___x_6698_, 1, v___f_6696_);
    lean_ctor_set(v___x_6698_, 2, v___f_6697_);
    return v___x_6698_;
}
pub unsafe fn l_Lake_instMonadLogLogTOfMonad___redArg(
    mut v_inst_6699_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6701_: *mut LeanObject = core::ptr::null_mut();
    v___x_6700_ = l_instMonadStateOfStateTOfMonad___redArg(v_inst_6699_);
    v___x_6701_ = lean_alloc_closure(l_Lake_pushLogEntry as *mut core::ffi::c_void, 3, 2);
    lean_closure_set(v___x_6701_, 0, lean_box(0));
    lean_closure_set(v___x_6701_, 1, v___x_6700_);
    return v___x_6701_;
}
pub unsafe fn l_Lake_instMonadLogLogTOfMonad(
    mut v_m_6702_: *mut LeanObject,
    mut v_inst_6703_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6704_: *mut LeanObject = core::ptr::null_mut();
    v___x_6704_ = l_Lake_instMonadLogLogTOfMonad___redArg(v_inst_6703_);
    return v___x_6704_;
}
pub unsafe fn l_Lake_LogT_run___redArg(
    mut v_self_6705_: *mut LeanObject,
    mut v_log_6706_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6707_: *mut LeanObject = core::ptr::null_mut();
    v___x_6707_ = lean_apply_1(v_self_6705_, v_log_6706_);
    return v___x_6707_;
}
pub unsafe fn l_Lake_LogT_run(
    mut v_m_6708_: *mut LeanObject,
    mut v_00_u03b1_6709_: *mut LeanObject,
    mut v_self_6710_: *mut LeanObject,
    mut v_log_6711_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6712_: *mut LeanObject = core::ptr::null_mut();
    v___x_6712_ = lean_apply_1(v_self_6710_, v_log_6711_);
    return v___x_6712_;
}
pub unsafe fn l_Lake_LogT_run_x27___redArg___lam__0(
    mut v_x_6713_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_6714_: *mut LeanObject = core::ptr::null_mut();
    v_fst_6714_ = lean_ctor_get(v_x_6713_, 0);
    lean_inc(v_fst_6714_);
    return v_fst_6714_;
}
pub unsafe fn l_Lake_LogT_run_x27___redArg___lam__0___boxed(
    mut v_x_6715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6716_: *mut LeanObject = core::ptr::null_mut();
    v_res_6716_ = l_Lake_LogT_run_x27___redArg___lam__0(v_x_6715_);
    lean_dec_ref(v_x_6715_);
    return v_res_6716_;
}
pub unsafe fn l_Lake_LogT_run_x27___redArg(
    mut v_inst_6718_: *mut LeanObject,
    mut v_self_6719_: *mut LeanObject,
    mut v_log_6720_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_6721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6724_: *mut LeanObject = core::ptr::null_mut();
    v_map_6721_ = lean_ctor_get(v_inst_6718_, 0);
    lean_inc(v_map_6721_);
    lean_dec_ref(v_inst_6718_);
    v___f_6722_ = l_Lake_LogT_run_x27___redArg___closed__0;
    v___x_6723_ = lean_apply_1(v_self_6719_, v_log_6720_);
    v___x_6724_ = lean_apply_4(
        v_map_6721_,
        lean_box(0),
        lean_box(0),
        v___f_6722_,
        v___x_6723_,
    );
    return v___x_6724_;
}
pub unsafe fn l_Lake_LogT_run_x27(
    mut v_m_6725_: *mut LeanObject,
    mut v_00_u03b1_6726_: *mut LeanObject,
    mut v_inst_6727_: *mut LeanObject,
    mut v_self_6728_: *mut LeanObject,
    mut v_log_6729_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_6730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6733_: *mut LeanObject = core::ptr::null_mut();
    v_map_6730_ = lean_ctor_get(v_inst_6727_, 0);
    lean_inc(v_map_6730_);
    lean_dec_ref(v_inst_6727_);
    v___f_6731_ = l_Lake_LogT_run_x27___redArg___closed__0;
    v___x_6732_ = lean_apply_1(v_self_6728_, v_log_6729_);
    v___x_6733_ = lean_apply_4(
        v_map_6730_,
        lean_box(0),
        lean_box(0),
        v___f_6731_,
        v___x_6732_,
    );
    return v___x_6733_;
}
pub unsafe fn l_Lake_LogT_takeAndRun___redArg___lam__1(
    mut v_toPure_6734_: *mut LeanObject,
    mut v_fst_6735_: *mut LeanObject,
    mut v_____r_6736_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6737_: *mut LeanObject = core::ptr::null_mut();
    v___x_6737_ = lean_apply_2(v_toPure_6734_, lean_box(0), v_fst_6735_);
    return v___x_6737_;
}
pub unsafe fn l_Lake_LogT_takeAndRun___redArg___lam__0(
    mut v_toPure_6738_: *mut LeanObject,
    mut v_set_6739_: *mut LeanObject,
    mut v_toBind_6740_: *mut LeanObject,
    mut v_____x_6741_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_6742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6746_: *mut LeanObject = core::ptr::null_mut();
    v_fst_6742_ = lean_ctor_get(v_____x_6741_, 0);
    lean_inc(v_fst_6742_);
    v_snd_6743_ = lean_ctor_get(v_____x_6741_, 1);
    lean_inc(v_snd_6743_);
    lean_dec_ref(v_____x_6741_);
    v___f_6744_ = lean_alloc_closure(
        l_Lake_LogT_takeAndRun___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_6744_, 0, v_toPure_6738_);
    lean_closure_set(v___f_6744_, 1, v_fst_6742_);
    v___x_6745_ = lean_apply_1(v_set_6739_, v_snd_6743_);
    v___x_6746_ = lean_apply_4(
        v_toBind_6740_,
        lean_box(0),
        lean_box(0),
        v___x_6745_,
        v___f_6744_,
    );
    return v___x_6746_;
}
pub unsafe fn l_Lake_LogT_takeAndRun___redArg___lam__2(
    mut v_self_6747_: *mut LeanObject,
    mut v_inst_6748_: *mut LeanObject,
    mut v_toBind_6749_: *mut LeanObject,
    mut v___f_6750_: *mut LeanObject,
    mut v_____do__lift_6751_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6754_: *mut LeanObject = core::ptr::null_mut();
    v___x_6752_ = lean_apply_1(v_self_6747_, v_____do__lift_6751_);
    v___x_6753_ = lean_apply_2(v_inst_6748_, lean_box(0), v___x_6752_);
    v___x_6754_ = lean_apply_4(
        v_toBind_6749_,
        lean_box(0),
        lean_box(0),
        v___x_6753_,
        v___f_6750_,
    );
    return v___x_6754_;
}
pub unsafe fn l_Lake_LogT_takeAndRun___redArg(
    mut v_inst_6755_: *mut LeanObject,
    mut v_inst_6756_: *mut LeanObject,
    mut v_inst_6757_: *mut LeanObject,
    mut v_self_6758_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_6759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_6760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_set_6761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_6762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_6763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6768_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_6759_ = lean_ctor_get(v_inst_6755_, 0);
    lean_inc_ref(v_toApplicative_6759_);
    v_toBind_6760_ = lean_ctor_get(v_inst_6755_, 1);
    lean_inc_n(v_toBind_6760_, 3);
    lean_dec_ref(v_inst_6755_);
    v_set_6761_ = lean_ctor_get(v_inst_6756_, 1);
    lean_inc(v_set_6761_);
    v_modifyGet_6762_ = lean_ctor_get(v_inst_6756_, 2);
    lean_inc(v_modifyGet_6762_);
    lean_dec_ref(v_inst_6756_);
    v_toPure_6763_ = lean_ctor_get(v_toApplicative_6759_, 1);
    lean_inc(v_toPure_6763_);
    lean_dec_ref(v_toApplicative_6759_);
    v___f_6764_ = l_Lake_takeLog___redArg___closed__0;
    v___x_6765_ = lean_apply_2(v_modifyGet_6762_, lean_box(0), v___f_6764_);
    v___f_6766_ = lean_alloc_closure(
        l_Lake_LogT_takeAndRun___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_6766_, 0, v_toPure_6763_);
    lean_closure_set(v___f_6766_, 1, v_set_6761_);
    lean_closure_set(v___f_6766_, 2, v_toBind_6760_);
    v___f_6767_ = lean_alloc_closure(
        l_Lake_LogT_takeAndRun___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_6767_, 0, v_self_6758_);
    lean_closure_set(v___f_6767_, 1, v_inst_6757_);
    lean_closure_set(v___f_6767_, 2, v_toBind_6760_);
    lean_closure_set(v___f_6767_, 3, v___f_6766_);
    v___x_6768_ = lean_apply_4(
        v_toBind_6760_,
        lean_box(0),
        lean_box(0),
        v___x_6765_,
        v___f_6767_,
    );
    return v___x_6768_;
}
pub unsafe fn l_Lake_LogT_takeAndRun(
    mut v_n_6769_: *mut LeanObject,
    mut v_m_6770_: *mut LeanObject,
    mut v_00_u03b1_6771_: *mut LeanObject,
    mut v_inst_6772_: *mut LeanObject,
    mut v_inst_6773_: *mut LeanObject,
    mut v_inst_6774_: *mut LeanObject,
    mut v_inst_6775_: *mut LeanObject,
    mut v_self_6776_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_6777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_6778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_set_6779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_6780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_6781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6786_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_6777_ = lean_ctor_get(v_inst_6772_, 0);
    lean_inc_ref(v_toApplicative_6777_);
    v_toBind_6778_ = lean_ctor_get(v_inst_6772_, 1);
    lean_inc_n(v_toBind_6778_, 3);
    lean_dec_ref(v_inst_6772_);
    v_set_6779_ = lean_ctor_get(v_inst_6773_, 1);
    lean_inc(v_set_6779_);
    v_modifyGet_6780_ = lean_ctor_get(v_inst_6773_, 2);
    lean_inc(v_modifyGet_6780_);
    lean_dec_ref(v_inst_6773_);
    v_toPure_6781_ = lean_ctor_get(v_toApplicative_6777_, 1);
    lean_inc(v_toPure_6781_);
    lean_dec_ref(v_toApplicative_6777_);
    v___f_6782_ = l_Lake_takeLog___redArg___closed__0;
    v___x_6783_ = lean_apply_2(v_modifyGet_6780_, lean_box(0), v___f_6782_);
    v___f_6784_ = lean_alloc_closure(
        l_Lake_LogT_takeAndRun___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_6784_, 0, v_toPure_6781_);
    lean_closure_set(v___f_6784_, 1, v_set_6779_);
    lean_closure_set(v___f_6784_, 2, v_toBind_6778_);
    v___f_6785_ = lean_alloc_closure(
        l_Lake_LogT_takeAndRun___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_6785_, 0, v_self_6776_);
    lean_closure_set(v___f_6785_, 1, v_inst_6774_);
    lean_closure_set(v___f_6785_, 2, v_toBind_6778_);
    lean_closure_set(v___f_6785_, 3, v___f_6784_);
    v___x_6786_ = lean_apply_4(
        v_toBind_6778_,
        lean_box(0),
        lean_box(0),
        v___x_6783_,
        v___f_6785_,
    );
    return v___x_6786_;
}
pub unsafe fn l_Lake_LogT_takeAndRun___boxed(
    mut v_n_6787_: *mut LeanObject,
    mut v_m_6788_: *mut LeanObject,
    mut v_00_u03b1_6789_: *mut LeanObject,
    mut v_inst_6790_: *mut LeanObject,
    mut v_inst_6791_: *mut LeanObject,
    mut v_inst_6792_: *mut LeanObject,
    mut v_inst_6793_: *mut LeanObject,
    mut v_self_6794_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6795_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_inst_6793_);
    return v_res_6795_;
}
pub unsafe fn l_Lake_LogT_replayLog___redArg___lam__2(
    mut v_toPure_6796_: *mut LeanObject,
    mut v___x_6797_: *mut LeanObject,
    mut v_toBind_6798_: *mut LeanObject,
    mut v_inst_6799_: *mut LeanObject,
    mut v___f_6800_: *mut LeanObject,
    mut v_____x_6801_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_6802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6807_: u8 = 0;
    v_fst_6802_ = lean_ctor_get(v_____x_6801_, 0);
    lean_inc(v_fst_6802_);
    v_snd_6803_ = lean_ctor_get(v_____x_6801_, 1);
    lean_inc(v_snd_6803_);
    lean_dec_ref(v_____x_6801_);
    lean_inc(v_toPure_6796_);
    v___f_6804_ = lean_alloc_closure(
        l_Lake_LogT_takeAndRun___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_6804_, 0, v_toPure_6796_);
    lean_closure_set(v___f_6804_, 1, v_fst_6802_);
    v___x_6805_ = lean_array_get_size(v_snd_6803_);
    v___x_6806_ = lean_box(0);
    v___x_6807_ = lean_nat_dec_lt(v___x_6797_, v___x_6805_);
    if v___x_6807_ == 0 {
        let mut v___x_6808_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6809_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_snd_6803_);
        lean_dec(v___f_6800_);
        lean_dec_ref(v_inst_6799_);
        v___x_6808_ = lean_apply_2(v_toPure_6796_, lean_box(0), v___x_6806_);
        v___x_6809_ = lean_apply_4(
            v_toBind_6798_,
            lean_box(0),
            lean_box(0),
            v___x_6808_,
            v___f_6804_,
        );
        return v___x_6809_;
    } else {
        let mut v___x_6810_: u8 = 0;
        v___x_6810_ = lean_nat_dec_le(v___x_6805_, v___x_6805_);
        if v___x_6810_ == 0 {
            if v___x_6807_ == 0 {
                let mut v___x_6811_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_6812_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_snd_6803_);
                lean_dec(v___f_6800_);
                lean_dec_ref(v_inst_6799_);
                v___x_6811_ = lean_apply_2(v_toPure_6796_, lean_box(0), v___x_6806_);
                v___x_6812_ = lean_apply_4(
                    v_toBind_6798_,
                    lean_box(0),
                    lean_box(0),
                    v___x_6811_,
                    v___f_6804_,
                );
                return v___x_6812_;
            } else {
                let mut v___x_6813_: usize = 0;
                let mut v___x_6814_: usize = 0;
                let mut v___x_6815_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_6816_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_toPure_6796_);
                v___x_6813_ = 0usize;
                v___x_6814_ = lean_usize_of_nat(v___x_6805_);
                v___x_6815_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    v_inst_6799_,
                    v___f_6800_,
                    v_snd_6803_,
                    v___x_6813_,
                    v___x_6814_,
                    v___x_6806_,
                );
                v___x_6816_ = lean_apply_4(
                    v_toBind_6798_,
                    lean_box(0),
                    lean_box(0),
                    v___x_6815_,
                    v___f_6804_,
                );
                return v___x_6816_;
            }
        } else {
            let mut v___x_6817_: usize = 0;
            let mut v___x_6818_: usize = 0;
            let mut v___x_6819_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6820_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_toPure_6796_);
            v___x_6817_ = 0usize;
            v___x_6818_ = lean_usize_of_nat(v___x_6805_);
            v___x_6819_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
                v_inst_6799_,
                v___f_6800_,
                v_snd_6803_,
                v___x_6817_,
                v___x_6818_,
                v___x_6806_,
            );
            v___x_6820_ = lean_apply_4(
                v_toBind_6798_,
                lean_box(0),
                lean_box(0),
                v___x_6819_,
                v___f_6804_,
            );
            return v___x_6820_;
        }
    }
}
pub unsafe fn l_Lake_LogT_replayLog___redArg___lam__2___boxed(
    mut v_toPure_6821_: *mut LeanObject,
    mut v___x_6822_: *mut LeanObject,
    mut v_toBind_6823_: *mut LeanObject,
    mut v_inst_6824_: *mut LeanObject,
    mut v___f_6825_: *mut LeanObject,
    mut v_____x_6826_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6827_: *mut LeanObject = core::ptr::null_mut();
    v_res_6827_ = l_Lake_LogT_replayLog___redArg___lam__2(
        v_toPure_6821_,
        v___x_6822_,
        v_toBind_6823_,
        v_inst_6824_,
        v___f_6825_,
        v_____x_6826_,
    );
    lean_dec(v___x_6822_);
    return v_res_6827_;
}
pub unsafe fn l_Lake_LogT_replayLog___redArg(
    mut v_inst_6828_: *mut LeanObject,
    mut v_logger_6829_: *mut LeanObject,
    mut v_inst_6830_: *mut LeanObject,
    mut v_self_6831_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_6832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_6833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_6834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6841_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_6832_ = lean_ctor_get(v_inst_6828_, 0);
    v_toBind_6833_ = lean_ctor_get(v_inst_6828_, 1);
    lean_inc_n(v_toBind_6833_, 2);
    v_toPure_6834_ = lean_ctor_get(v_toApplicative_6832_, 1);
    lean_inc(v_toPure_6834_);
    v___f_6835_ = lean_alloc_closure(
        l_Lake_Log_replay___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_6835_, 0, v_logger_6829_);
    v___x_6836_ = lean_unsigned_to_nat(0);
    v___x_6837_ = l_Lake_Log_empty___closed__0;
    v___x_6838_ = lean_apply_1(v_self_6831_, v___x_6837_);
    v___x_6839_ = lean_apply_2(v_inst_6830_, lean_box(0), v___x_6838_);
    v___f_6840_ = lean_alloc_closure(
        l_Lake_LogT_replayLog___redArg___lam__2___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_6840_, 0, v_toPure_6834_);
    lean_closure_set(v___f_6840_, 1, v___x_6836_);
    lean_closure_set(v___f_6840_, 2, v_toBind_6833_);
    lean_closure_set(v___f_6840_, 3, v_inst_6828_);
    lean_closure_set(v___f_6840_, 4, v___f_6835_);
    v___x_6841_ = lean_apply_4(
        v_toBind_6833_,
        lean_box(0),
        lean_box(0),
        v___x_6839_,
        v___f_6840_,
    );
    return v___x_6841_;
}
pub unsafe fn l_Lake_LogT_replayLog(
    mut v_n_6842_: *mut LeanObject,
    mut v_m_6843_: *mut LeanObject,
    mut v_00_u03b1_6844_: *mut LeanObject,
    mut v_inst_6845_: *mut LeanObject,
    mut v_logger_6846_: *mut LeanObject,
    mut v_inst_6847_: *mut LeanObject,
    mut v_self_6848_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_6849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_6850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_6851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6858_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_6849_ = lean_ctor_get(v_inst_6845_, 0);
    v_toBind_6850_ = lean_ctor_get(v_inst_6845_, 1);
    lean_inc_n(v_toBind_6850_, 2);
    v_toPure_6851_ = lean_ctor_get(v_toApplicative_6849_, 1);
    lean_inc(v_toPure_6851_);
    v___f_6852_ = lean_alloc_closure(
        l_Lake_Log_replay___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_6852_, 0, v_logger_6846_);
    v___x_6853_ = lean_unsigned_to_nat(0);
    v___x_6854_ = l_Lake_Log_empty___closed__0;
    v___x_6855_ = lean_apply_1(v_self_6848_, v___x_6854_);
    v___x_6856_ = lean_apply_2(v_inst_6847_, lean_box(0), v___x_6855_);
    v___f_6857_ = lean_alloc_closure(
        l_Lake_LogT_replayLog___redArg___lam__2___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_6857_, 0, v_toPure_6851_);
    lean_closure_set(v___f_6857_, 1, v___x_6853_);
    lean_closure_set(v___f_6857_, 2, v_toBind_6850_);
    lean_closure_set(v___f_6857_, 3, v_inst_6845_);
    lean_closure_set(v___f_6857_, 4, v___f_6852_);
    v___x_6858_ = lean_apply_4(
        v_toBind_6850_,
        lean_box(0),
        lean_box(0),
        v___x_6856_,
        v___f_6857_,
    );
    return v___x_6858_;
}
pub unsafe fn l_Lake_instMonadLogELogTOfMonad___redArg(
    mut v_inst_6859_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_6860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_6861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6863_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_6860_ = lean_ctor_get(v_inst_6859_, 0);
    lean_inc_ref(v_toApplicative_6860_);
    lean_dec_ref(v_inst_6859_);
    v_toPure_6861_ = lean_ctor_get(v_toApplicative_6860_, 1);
    lean_inc(v_toPure_6861_);
    lean_dec_ref(v_toApplicative_6860_);
    v___x_6862_ = l_Lake_EStateT_instMonadStateOfOfPure___redArg(v_toPure_6861_);
    v___x_6863_ = lean_alloc_closure(l_Lake_pushLogEntry as *mut core::ffi::c_void, 3, 2);
    lean_closure_set(v___x_6863_, 0, lean_box(0));
    lean_closure_set(v___x_6863_, 1, v___x_6862_);
    return v___x_6863_;
}
pub unsafe fn l_Lake_instMonadLogELogTOfMonad(
    mut v_m_6864_: *mut LeanObject,
    mut v_inst_6865_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6866_: *mut LeanObject = core::ptr::null_mut();
    v___x_6866_ = l_Lake_instMonadLogELogTOfMonad___redArg(v_inst_6865_);
    return v___x_6866_;
}
pub unsafe fn l_Lake_instMonadErrorELogTOfMonad___redArg___lam__0(
    mut v_x_6867_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_6868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6872_: u8 = 0;
    let mut v___x_6873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6877_: u8 = 0;
    let mut v_a_6878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6882_: u8 = 0;
    let mut v___x_6884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6886_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6867_) == 0 {
                    v_a_6868_ = lean_ctor_get(v_x_6867_, 0);
                    v_a_6869_ = lean_ctor_get(v_x_6867_, 1);
                    v_isSharedCheck_6877_ = (!lean_is_exclusive(v_x_6867_)) as u8;
                    if v_isSharedCheck_6877_ == 0 {
                        v___x_6871_ = v_x_6867_;
                        v_isShared_6872_ = v_isSharedCheck_6877_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6869_);
                        lean_inc(v_a_6868_);
                        lean_dec(v_x_6867_);
                        v___x_6871_ = lean_box(0);
                        v_isShared_6872_ = v_isSharedCheck_6877_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6878_ = lean_ctor_get(v_x_6867_, 0);
                    v_a_6879_ = lean_ctor_get(v_x_6867_, 1);
                    v_isSharedCheck_6886_ = (!lean_is_exclusive(v_x_6867_)) as u8;
                    if v_isSharedCheck_6886_ == 0 {
                        v___x_6881_ = v_x_6867_;
                        v_isShared_6882_ = v_isSharedCheck_6886_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6879_);
                        lean_inc(v_a_6878_);
                        lean_dec(v_x_6867_);
                        v___x_6881_ = lean_box(0);
                        v_isShared_6882_ = v_isSharedCheck_6886_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6873_ = lean_array_get_size(v_a_6868_);
                lean_dec(v_a_6868_);
                if v_isShared_6872_ == 0 {
                    lean_ctor_set(v___x_6871_, 0, v___x_6873_);
                    v___x_6875_ = v___x_6871_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6876_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6876_, 0, v___x_6873_);
                    lean_ctor_set(v_reuseFailAlloc_6876_, 1, v_a_6869_);
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
                    v_reuseFailAlloc_6885_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6885_, 0, v_a_6878_);
                    lean_ctor_set(v_reuseFailAlloc_6885_, 1, v_a_6879_);
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
    mut v_a_6887_: *mut LeanObject,
    mut v_toPure_6888_: *mut LeanObject,
    mut v_____do__lift_6889_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_6890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6893_: u8 = 0;
    let mut v___x_6895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6898_: u8 = 0;
    let mut v_unused_6899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6904_: u8 = 0;
    let mut v___x_6906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6909_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_____do__lift_6889_) == 0 {
                    v_a_6890_ = lean_ctor_get(v_____do__lift_6889_, 1);
                    v_isSharedCheck_6898_ = (!lean_is_exclusive(v_____do__lift_6889_)) as u8;
                    if v_isSharedCheck_6898_ == 0 {
                        v_unused_6899_ = lean_ctor_get(v_____do__lift_6889_, 0);
                        lean_dec(v_unused_6899_);
                        v___x_6892_ = v_____do__lift_6889_;
                        v_isShared_6893_ = v_isSharedCheck_6898_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6890_);
                        lean_dec(v_____do__lift_6889_);
                        v___x_6892_ = lean_box(0);
                        v_isShared_6893_ = v_isSharedCheck_6898_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_a_6887_);
                    v_a_6900_ = lean_ctor_get(v_____do__lift_6889_, 0);
                    v_a_6901_ = lean_ctor_get(v_____do__lift_6889_, 1);
                    v_isSharedCheck_6909_ = (!lean_is_exclusive(v_____do__lift_6889_)) as u8;
                    if v_isSharedCheck_6909_ == 0 {
                        v___x_6903_ = v_____do__lift_6889_;
                        v_isShared_6904_ = v_isSharedCheck_6909_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6901_);
                        lean_inc(v_a_6900_);
                        lean_dec(v_____do__lift_6889_);
                        v___x_6903_ = lean_box(0);
                        v_isShared_6904_ = v_isSharedCheck_6909_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6893_ == 0 {
                    lean_ctor_set_tag(v___x_6892_, 1);
                    lean_ctor_set(v___x_6892_, 0, v_a_6887_);
                    v___x_6895_ = v___x_6892_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6897_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6897_, 0, v_a_6887_);
                    lean_ctor_set(v_reuseFailAlloc_6897_, 1, v_a_6890_);
                    v___x_6895_ = v_reuseFailAlloc_6897_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6896_ = lean_apply_2(v_toPure_6888_, lean_box(0), v___x_6895_);
                return v___x_6896_;
            }
            3 => {
                if v_isShared_6904_ == 0 {
                    v___x_6906_ = v___x_6903_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6908_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6908_, 0, v_a_6900_);
                    lean_ctor_set(v_reuseFailAlloc_6908_, 1, v_a_6901_);
                    v___x_6906_ = v_reuseFailAlloc_6908_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6907_ = lean_apply_2(v_toPure_6888_, lean_box(0), v___x_6906_);
                return v___x_6907_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instMonadErrorELogTOfMonad___redArg___lam__2(
    mut v_toPure_6910_: *mut LeanObject,
    mut v___x_6911_: *mut LeanObject,
    mut v_____do__lift_6912_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6917_: u8 = 0;
    let mut v___x_6919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6922_: u8 = 0;
    let mut v_unused_6923_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_____do__lift_6912_) == 0 {
                    v___x_6913_ = lean_apply_2(v_toPure_6910_, lean_box(0), v_____do__lift_6912_);
                    return v___x_6913_;
                } else {
                    v_a_6914_ = lean_ctor_get(v_____do__lift_6912_, 1);
                    v_isSharedCheck_6922_ = (!lean_is_exclusive(v_____do__lift_6912_)) as u8;
                    if v_isSharedCheck_6922_ == 0 {
                        v_unused_6923_ = lean_ctor_get(v_____do__lift_6912_, 0);
                        lean_dec(v_unused_6923_);
                        v___x_6916_ = v_____do__lift_6912_;
                        v_isShared_6917_ = v_isSharedCheck_6922_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6914_);
                        lean_dec(v_____do__lift_6912_);
                        v___x_6916_ = lean_box(0);
                        v_isShared_6917_ = v_isSharedCheck_6922_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6917_ == 0 {
                    lean_ctor_set_tag(v___x_6916_, 0);
                    lean_ctor_set(v___x_6916_, 0, v___x_6911_);
                    v___x_6919_ = v___x_6916_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6921_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6921_, 0, v___x_6911_);
                    lean_ctor_set(v_reuseFailAlloc_6921_, 1, v_a_6914_);
                    v___x_6919_ = v_reuseFailAlloc_6921_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6920_ = lean_apply_2(v_toPure_6910_, lean_box(0), v___x_6919_);
                return v___x_6920_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instMonadErrorELogTOfMonad___redArg___lam__3(
    mut v_toPure_6924_: *mut LeanObject,
    mut v___x_6925_: *mut LeanObject,
    mut v_toBind_6926_: *mut LeanObject,
    mut v_____do__lift_6927_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_6928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6932_: u8 = 0;
    let mut v___f_6933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6943_: u8 = 0;
    let mut v_a_6944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6948_: u8 = 0;
    let mut v___x_6950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6953_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_____do__lift_6927_) == 0 {
                    v_a_6928_ = lean_ctor_get(v_____do__lift_6927_, 0);
                    v_a_6929_ = lean_ctor_get(v_____do__lift_6927_, 1);
                    v_isSharedCheck_6943_ = (!lean_is_exclusive(v_____do__lift_6927_)) as u8;
                    if v_isSharedCheck_6943_ == 0 {
                        v___x_6931_ = v_____do__lift_6927_;
                        v_isShared_6932_ = v_isSharedCheck_6943_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6929_);
                        lean_inc(v_a_6928_);
                        lean_dec(v_____do__lift_6927_);
                        v___x_6931_ = lean_box(0);
                        v_isShared_6932_ = v_isSharedCheck_6943_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_toBind_6926_);
                    lean_dec_ref(v___x_6925_);
                    v_a_6944_ = lean_ctor_get(v_____do__lift_6927_, 0);
                    v_a_6945_ = lean_ctor_get(v_____do__lift_6927_, 1);
                    v_isSharedCheck_6953_ = (!lean_is_exclusive(v_____do__lift_6927_)) as u8;
                    if v_isSharedCheck_6953_ == 0 {
                        v___x_6947_ = v_____do__lift_6927_;
                        v_isShared_6948_ = v_isSharedCheck_6953_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6945_);
                        lean_inc(v_a_6944_);
                        lean_dec(v_____do__lift_6927_);
                        v___x_6947_ = lean_box(0);
                        v_isShared_6948_ = v_isSharedCheck_6953_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_n(v_toPure_6924_, 2);
                v___f_6933_ = lean_alloc_closure(
                    l_Lake_instMonadErrorELogTOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_6933_, 0, v_a_6928_);
                lean_closure_set(v___f_6933_, 1, v_toPure_6924_);
                v___x_6934_ = lean_box(0);
                v___f_6935_ = lean_alloc_closure(
                    l_Lake_instMonadErrorELogTOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_6935_, 0, v_toPure_6924_);
                lean_closure_set(v___f_6935_, 1, v___x_6934_);
                v___x_6936_ = lean_array_push(v_a_6929_, v___x_6925_);
                if v_isShared_6932_ == 0 {
                    lean_ctor_set(v___x_6931_, 1, v___x_6936_);
                    lean_ctor_set(v___x_6931_, 0, v___x_6934_);
                    v___x_6938_ = v___x_6931_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6942_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6942_, 0, v___x_6934_);
                    lean_ctor_set(v_reuseFailAlloc_6942_, 1, v___x_6936_);
                    v___x_6938_ = v_reuseFailAlloc_6942_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6939_ = lean_apply_2(v_toPure_6924_, lean_box(0), v___x_6938_);
                lean_inc(v_toBind_6926_);
                v___x_6940_ = lean_apply_4(
                    v_toBind_6926_,
                    lean_box(0),
                    lean_box(0),
                    v___x_6939_,
                    v___f_6935_,
                );
                v___x_6941_ = lean_apply_4(
                    v_toBind_6926_,
                    lean_box(0),
                    lean_box(0),
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
                    v_reuseFailAlloc_6952_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6952_, 0, v_a_6944_);
                    lean_ctor_set(v_reuseFailAlloc_6952_, 1, v_a_6945_);
                    v___x_6950_ = v_reuseFailAlloc_6952_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6951_ = lean_apply_2(v_toPure_6924_, lean_box(0), v___x_6950_);
                return v___x_6951_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instMonadErrorELogTOfMonad___redArg___lam__4(
    mut v_toFunctor_6954_: *mut LeanObject,
    mut v_toPure_6955_: *mut LeanObject,
    mut v_toBind_6956_: *mut LeanObject,
    mut v___f_6957_: *mut LeanObject,
    mut v_00_u03b1_6958_: *mut LeanObject,
    mut v___y_6959_: *mut LeanObject,
    mut v___y_6960_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_6961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6964_: u8 = 0;
    let mut v___x_6965_: u8 = 0;
    let mut v___x_6966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6974_: u8 = 0;
    let mut v_unused_6975_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_6961_ = lean_ctor_get(v_toFunctor_6954_, 0);
                v_isSharedCheck_6974_ = (!lean_is_exclusive(v_toFunctor_6954_)) as u8;
                if v_isSharedCheck_6974_ == 0 {
                    v_unused_6975_ = lean_ctor_get(v_toFunctor_6954_, 1);
                    lean_dec(v_unused_6975_);
                    v___x_6963_ = v_toFunctor_6954_;
                    v_isShared_6964_ = v_isSharedCheck_6974_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_map_6961_);
                    lean_dec(v_toFunctor_6954_);
                    v___x_6963_ = lean_box(0);
                    v_isShared_6964_ = v_isSharedCheck_6974_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6965_ = 3;
                v___x_6966_ = lean_alloc_ctor(0, 1, (1) as u32);
                lean_ctor_set(v___x_6966_, 0, v___y_6959_);
                lean_ctor_set_uint8(
                    v___x_6966_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_6965_,
                );
                lean_inc(v_toBind_6956_);
                lean_inc(v_toPure_6955_);
                v___f_6967_ = lean_alloc_closure(
                    l_Lake_instMonadErrorELogTOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    4,
                    3,
                );
                lean_closure_set(v___f_6967_, 0, v_toPure_6955_);
                lean_closure_set(v___f_6967_, 1, v___x_6966_);
                lean_closure_set(v___f_6967_, 2, v_toBind_6956_);
                lean_inc_ref(v___y_6960_);
                if v_isShared_6964_ == 0 {
                    lean_ctor_set(v___x_6963_, 1, v___y_6960_);
                    lean_ctor_set(v___x_6963_, 0, v___y_6960_);
                    v___x_6969_ = v___x_6963_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6973_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6973_, 0, v___y_6960_);
                    lean_ctor_set(v_reuseFailAlloc_6973_, 1, v___y_6960_);
                    v___x_6969_ = v_reuseFailAlloc_6973_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6970_ = lean_apply_2(v_toPure_6955_, lean_box(0), v___x_6969_);
                v___x_6971_ = lean_apply_4(
                    v_map_6961_,
                    lean_box(0),
                    lean_box(0),
                    v___f_6957_,
                    v___x_6970_,
                );
                v___x_6972_ = lean_apply_4(
                    v_toBind_6956_,
                    lean_box(0),
                    lean_box(0),
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
    mut v_inst_6977_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_6978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_6979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_6980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_6981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6983_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_6978_ = lean_ctor_get(v_inst_6977_, 0);
    lean_inc_ref(v_toApplicative_6978_);
    v_toBind_6979_ = lean_ctor_get(v_inst_6977_, 1);
    lean_inc(v_toBind_6979_);
    lean_dec_ref(v_inst_6977_);
    v_toFunctor_6980_ = lean_ctor_get(v_toApplicative_6978_, 0);
    lean_inc_ref(v_toFunctor_6980_);
    v_toPure_6981_ = lean_ctor_get(v_toApplicative_6978_, 1);
    lean_inc(v_toPure_6981_);
    lean_dec_ref(v_toApplicative_6978_);
    v___f_6982_ = l_Lake_instMonadErrorELogTOfMonad___redArg___closed__0;
    v___f_6983_ = lean_alloc_closure(
        l_Lake_instMonadErrorELogTOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
        7,
        4,
    );
    lean_closure_set(v___f_6983_, 0, v_toFunctor_6980_);
    lean_closure_set(v___f_6983_, 1, v_toPure_6981_);
    lean_closure_set(v___f_6983_, 2, v_toBind_6979_);
    lean_closure_set(v___f_6983_, 3, v___f_6982_);
    return v___f_6983_;
}
pub unsafe fn l_Lake_instMonadErrorELogTOfMonad(
    mut v_m_6984_: *mut LeanObject,
    mut v_inst_6985_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6986_: *mut LeanObject = core::ptr::null_mut();
    v___x_6986_ = l_Lake_instMonadErrorELogTOfMonad___redArg(v_inst_6985_);
    return v___x_6986_;
}
pub unsafe fn l_Lake_instAlternativeELogTOfMonad___redArg___lam__1(
    mut v___y_6987_: *mut LeanObject,
    mut v___x_6988_: *mut LeanObject,
    mut v_toPure_6989_: *mut LeanObject,
    mut v_____do__lift_6990_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_6991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6997_: u8 = 0;
    let mut v___x_6999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7002_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_____do__lift_6990_) == 0 {
                    lean_dec(v_toPure_6989_);
                    v_a_6991_ = lean_ctor_get(v_____do__lift_6990_, 1);
                    lean_inc(v_a_6991_);
                    lean_dec_ref_known(v_____do__lift_6990_, 2);
                    v___x_6992_ = lean_apply_2(v___y_6987_, v___x_6988_, v_a_6991_);
                    return v___x_6992_;
                } else {
                    lean_dec(v___y_6987_);
                    v_a_6993_ = lean_ctor_get(v_____do__lift_6990_, 0);
                    v_a_6994_ = lean_ctor_get(v_____do__lift_6990_, 1);
                    v_isSharedCheck_7002_ = (!lean_is_exclusive(v_____do__lift_6990_)) as u8;
                    if v_isSharedCheck_7002_ == 0 {
                        v___x_6996_ = v_____do__lift_6990_;
                        v_isShared_6997_ = v_isSharedCheck_7002_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6994_);
                        lean_inc(v_a_6993_);
                        lean_dec(v_____do__lift_6990_);
                        v___x_6996_ = lean_box(0);
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
                    v_reuseFailAlloc_7001_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7001_, 0, v_a_6993_);
                    lean_ctor_set(v_reuseFailAlloc_7001_, 1, v_a_6994_);
                    v___x_6999_ = v_reuseFailAlloc_7001_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7000_ = lean_apply_2(v_toPure_6989_, lean_box(0), v___x_6999_);
                return v___x_7000_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instAlternativeELogTOfMonad___redArg___lam__0(
    mut v_toPure_7003_: *mut LeanObject,
    mut v___y_7004_: *mut LeanObject,
    mut v_toBind_7005_: *mut LeanObject,
    mut v_____do__lift_7006_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7012_: u8 = 0;
    let mut v___x_7013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7021_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_____do__lift_7006_) == 0 {
                    lean_dec(v_toBind_7005_);
                    lean_dec(v___y_7004_);
                    v___x_7007_ = lean_apply_2(v_toPure_7003_, lean_box(0), v_____do__lift_7006_);
                    return v___x_7007_;
                } else {
                    v_a_7008_ = lean_ctor_get(v_____do__lift_7006_, 0);
                    v_a_7009_ = lean_ctor_get(v_____do__lift_7006_, 1);
                    v_isSharedCheck_7021_ = (!lean_is_exclusive(v_____do__lift_7006_)) as u8;
                    if v_isSharedCheck_7021_ == 0 {
                        v___x_7011_ = v_____do__lift_7006_;
                        v_isShared_7012_ = v_isSharedCheck_7021_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7009_);
                        lean_inc(v_a_7008_);
                        lean_dec(v_____do__lift_7006_);
                        v___x_7011_ = lean_box(0);
                        v_isShared_7012_ = v_isSharedCheck_7021_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7013_ = lean_box(0);
                lean_inc(v_toPure_7003_);
                v___f_7014_ = lean_alloc_closure(
                    l_Lake_instAlternativeELogTOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    4,
                    3,
                );
                lean_closure_set(v___f_7014_, 0, v___y_7004_);
                lean_closure_set(v___f_7014_, 1, v___x_7013_);
                lean_closure_set(v___f_7014_, 2, v_toPure_7003_);
                v___x_7015_ = l_Array_shrink___redArg(v_a_7009_, v_a_7008_);
                lean_dec(v_a_7008_);
                if v_isShared_7012_ == 0 {
                    lean_ctor_set_tag(v___x_7011_, 0);
                    lean_ctor_set(v___x_7011_, 1, v___x_7015_);
                    lean_ctor_set(v___x_7011_, 0, v___x_7013_);
                    v___x_7017_ = v___x_7011_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7020_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7020_, 0, v___x_7013_);
                    lean_ctor_set(v_reuseFailAlloc_7020_, 1, v___x_7015_);
                    v___x_7017_ = v_reuseFailAlloc_7020_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7018_ = lean_apply_2(v_toPure_7003_, lean_box(0), v___x_7017_);
                v___x_7019_ = lean_apply_4(
                    v_toBind_7005_,
                    lean_box(0),
                    lean_box(0),
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
    mut v_toPure_7022_: *mut LeanObject,
    mut v_toBind_7023_: *mut LeanObject,
    mut v_00_u03b1_7024_: *mut LeanObject,
    mut v___y_7025_: *mut LeanObject,
    mut v___y_7026_: *mut LeanObject,
    mut v___y_7027_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7030_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_toBind_7023_);
    v___f_7028_ = lean_alloc_closure(
        l_Lake_instAlternativeELogTOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_7028_, 0, v_toPure_7022_);
    lean_closure_set(v___f_7028_, 1, v___y_7026_);
    lean_closure_set(v___f_7028_, 2, v_toBind_7023_);
    v___x_7029_ = lean_apply_1(v___y_7025_, v___y_7027_);
    v___x_7030_ = lean_apply_4(
        v_toBind_7023_,
        lean_box(0),
        lean_box(0),
        v___x_7029_,
        v___f_7028_,
    );
    return v___x_7030_;
}
pub unsafe fn l_Lake_instAlternativeELogTOfMonad___redArg___lam__3(
    mut v_toPure_7031_: *mut LeanObject,
    mut v_____do__lift_7032_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_7033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7037_: u8 = 0;
    let mut v___x_7039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7042_: u8 = 0;
    let mut v_a_7043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7047_: u8 = 0;
    let mut v___x_7049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7052_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_____do__lift_7032_) == 0 {
                    v_a_7033_ = lean_ctor_get(v_____do__lift_7032_, 0);
                    v_a_7034_ = lean_ctor_get(v_____do__lift_7032_, 1);
                    v_isSharedCheck_7042_ = (!lean_is_exclusive(v_____do__lift_7032_)) as u8;
                    if v_isSharedCheck_7042_ == 0 {
                        v___x_7036_ = v_____do__lift_7032_;
                        v_isShared_7037_ = v_isSharedCheck_7042_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7034_);
                        lean_inc(v_a_7033_);
                        lean_dec(v_____do__lift_7032_);
                        v___x_7036_ = lean_box(0);
                        v_isShared_7037_ = v_isSharedCheck_7042_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7043_ = lean_ctor_get(v_____do__lift_7032_, 0);
                    v_a_7044_ = lean_ctor_get(v_____do__lift_7032_, 1);
                    v_isSharedCheck_7052_ = (!lean_is_exclusive(v_____do__lift_7032_)) as u8;
                    if v_isSharedCheck_7052_ == 0 {
                        v___x_7046_ = v_____do__lift_7032_;
                        v_isShared_7047_ = v_isSharedCheck_7052_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_7044_);
                        lean_inc(v_a_7043_);
                        lean_dec(v_____do__lift_7032_);
                        v___x_7046_ = lean_box(0);
                        v_isShared_7047_ = v_isSharedCheck_7052_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7037_ == 0 {
                    lean_ctor_set_tag(v___x_7036_, 1);
                    v___x_7039_ = v___x_7036_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7041_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7041_, 0, v_a_7033_);
                    lean_ctor_set(v_reuseFailAlloc_7041_, 1, v_a_7034_);
                    v___x_7039_ = v_reuseFailAlloc_7041_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7040_ = lean_apply_2(v_toPure_7031_, lean_box(0), v___x_7039_);
                return v___x_7040_;
            }
            3 => {
                if v_isShared_7047_ == 0 {
                    v___x_7049_ = v___x_7046_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7051_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7051_, 0, v_a_7043_);
                    lean_ctor_set(v_reuseFailAlloc_7051_, 1, v_a_7044_);
                    v___x_7049_ = v_reuseFailAlloc_7051_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_7050_ = lean_apply_2(v_toPure_7031_, lean_box(0), v___x_7049_);
                return v___x_7050_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instAlternativeELogTOfMonad___redArg___lam__4(
    mut v_toFunctor_7053_: *mut LeanObject,
    mut v_toPure_7054_: *mut LeanObject,
    mut v___f_7055_: *mut LeanObject,
    mut v_toBind_7056_: *mut LeanObject,
    mut v___f_7057_: *mut LeanObject,
    mut v_00_u03b1_7058_: *mut LeanObject,
    mut v___y_7059_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_7060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7063_: u8 = 0;
    let mut v___x_7065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7070_: u8 = 0;
    let mut v_unused_7071_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_7060_ = lean_ctor_get(v_toFunctor_7053_, 0);
                v_isSharedCheck_7070_ = (!lean_is_exclusive(v_toFunctor_7053_)) as u8;
                if v_isSharedCheck_7070_ == 0 {
                    v_unused_7071_ = lean_ctor_get(v_toFunctor_7053_, 1);
                    lean_dec(v_unused_7071_);
                    v___x_7062_ = v_toFunctor_7053_;
                    v_isShared_7063_ = v_isSharedCheck_7070_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_map_7060_);
                    lean_dec(v_toFunctor_7053_);
                    v___x_7062_ = lean_box(0);
                    v_isShared_7063_ = v_isSharedCheck_7070_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc_ref(v___y_7059_);
                if v_isShared_7063_ == 0 {
                    lean_ctor_set(v___x_7062_, 1, v___y_7059_);
                    lean_ctor_set(v___x_7062_, 0, v___y_7059_);
                    v___x_7065_ = v___x_7062_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7069_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7069_, 0, v___y_7059_);
                    lean_ctor_set(v_reuseFailAlloc_7069_, 1, v___y_7059_);
                    v___x_7065_ = v_reuseFailAlloc_7069_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7066_ = lean_apply_2(v_toPure_7054_, lean_box(0), v___x_7065_);
                v___x_7067_ = lean_apply_4(
                    v_map_7060_,
                    lean_box(0),
                    lean_box(0),
                    v___f_7055_,
                    v___x_7066_,
                );
                v___x_7068_ = lean_apply_4(
                    v_toBind_7056_,
                    lean_box(0),
                    lean_box(0),
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
    mut v_inst_7072_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_7073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_7074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_7075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_7076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7079_: u8 = 0;
    let mut v___f_7080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7094_: u8 = 0;
    let mut v_unused_7095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_7096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_7097_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_7073_ = lean_ctor_get(v_inst_7072_, 0);
                lean_inc_ref(v_toApplicative_7073_);
                v_toBind_7074_ = lean_ctor_get(v_inst_7072_, 1);
                lean_inc(v_toBind_7074_);
                lean_dec_ref(v_inst_7072_);
                v_toFunctor_7075_ = lean_ctor_get(v_toApplicative_7073_, 0);
                v_toPure_7076_ = lean_ctor_get(v_toApplicative_7073_, 1);
                v_isSharedCheck_7094_ = (!lean_is_exclusive(v_toApplicative_7073_)) as u8;
                if v_isSharedCheck_7094_ == 0 {
                    v_unused_7095_ = lean_ctor_get(v_toApplicative_7073_, 4);
                    lean_dec(v_unused_7095_);
                    v_unused_7096_ = lean_ctor_get(v_toApplicative_7073_, 3);
                    lean_dec(v_unused_7096_);
                    v_unused_7097_ = lean_ctor_get(v_toApplicative_7073_, 2);
                    lean_dec(v_unused_7097_);
                    v___x_7078_ = v_toApplicative_7073_;
                    v_isShared_7079_ = v_isSharedCheck_7094_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toPure_7076_);
                    lean_inc(v_toFunctor_7075_);
                    lean_dec(v_toApplicative_7073_);
                    v___x_7078_ = lean_box(0);
                    v_isShared_7079_ = v_isSharedCheck_7094_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_7080_ = l_Lake_instMonadErrorELogTOfMonad___redArg___closed__0;
                lean_inc_n(v_toBind_7074_, 4);
                lean_inc_n(v_toPure_7076_, 7);
                v___f_7081_ = lean_alloc_closure(
                    l_Lake_instAlternativeELogTOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
                    6,
                    2,
                );
                lean_closure_set(v___f_7081_, 0, v_toPure_7076_);
                lean_closure_set(v___f_7081_, 1, v_toBind_7074_);
                v___f_7082_ = lean_alloc_closure(
                    l_Lake_instAlternativeELogTOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_7082_, 0, v_toPure_7076_);
                lean_inc_ref_n(v_toFunctor_7075_, 2);
                v___f_7083_ = lean_alloc_closure(
                    l_Lake_instAlternativeELogTOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    7,
                    5,
                );
                lean_closure_set(v___f_7083_, 0, v_toFunctor_7075_);
                lean_closure_set(v___f_7083_, 1, v_toPure_7076_);
                lean_closure_set(v___f_7083_, 2, v___f_7080_);
                lean_closure_set(v___f_7083_, 3, v_toBind_7074_);
                lean_closure_set(v___f_7083_, 4, v___f_7082_);
                v___f_7084_ = lean_alloc_closure(
                    l_Lake_EStateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    7,
                    2,
                );
                lean_closure_set(v___f_7084_, 0, v_toPure_7076_);
                lean_closure_set(v___f_7084_, 1, v_toBind_7074_);
                v___f_7085_ = lean_alloc_closure(
                    l_Lake_EStateT_instMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    7,
                    2,
                );
                lean_closure_set(v___f_7085_, 0, v_toPure_7076_);
                lean_closure_set(v___f_7085_, 1, v_toBind_7074_);
                v___f_7086_ = lean_alloc_closure(
                    l_Lake_EStateT_instMonad___redArg___lam__5 as *mut core::ffi::c_void,
                    7,
                    2,
                );
                lean_closure_set(v___f_7086_, 0, v_toPure_7076_);
                lean_closure_set(v___f_7086_, 1, v___f_7084_);
                v___f_7087_ = lean_alloc_closure(
                    l_Lake_EStateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
                    8,
                    3,
                );
                lean_closure_set(v___f_7087_, 0, v_toFunctor_7075_);
                lean_closure_set(v___f_7087_, 1, v_toPure_7076_);
                lean_closure_set(v___f_7087_, 2, v_toBind_7074_);
                v___x_7088_ = l_Lake_EStateT_instFunctor___redArg(v_toFunctor_7075_);
                v___f_7089_ = lean_alloc_closure(
                    l_Lake_EStateT_instPure___redArg___lam__0 as *mut core::ffi::c_void,
                    4,
                    1,
                );
                lean_closure_set(v___f_7089_, 0, v_toPure_7076_);
                if v_isShared_7079_ == 0 {
                    lean_ctor_set(v___x_7078_, 4, v___f_7085_);
                    lean_ctor_set(v___x_7078_, 3, v___f_7086_);
                    lean_ctor_set(v___x_7078_, 2, v___f_7087_);
                    lean_ctor_set(v___x_7078_, 1, v___f_7089_);
                    lean_ctor_set(v___x_7078_, 0, v___x_7088_);
                    v___x_7091_ = v___x_7078_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7093_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7093_, 0, v___x_7088_);
                    lean_ctor_set(v_reuseFailAlloc_7093_, 1, v___f_7089_);
                    lean_ctor_set(v_reuseFailAlloc_7093_, 2, v___f_7087_);
                    lean_ctor_set(v_reuseFailAlloc_7093_, 3, v___f_7086_);
                    lean_ctor_set(v_reuseFailAlloc_7093_, 4, v___f_7085_);
                    v___x_7091_ = v_reuseFailAlloc_7093_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7092_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_7092_, 0, v___x_7091_);
                lean_ctor_set(v___x_7092_, 1, v___f_7083_);
                lean_ctor_set(v___x_7092_, 2, v___f_7081_);
                return v___x_7092_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instAlternativeELogTOfMonad(
    mut v_m_7098_: *mut LeanObject,
    mut v_inst_7099_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7100_: *mut LeanObject = core::ptr::null_mut();
    v___x_7100_ = l_Lake_instAlternativeELogTOfMonad___redArg(v_inst_7099_);
    return v___x_7100_;
}
pub unsafe fn l_Lake_ELogT_run___redArg(
    mut v_self_7101_: *mut LeanObject,
    mut v_log_7102_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7103_: *mut LeanObject = core::ptr::null_mut();
    v___x_7103_ = lean_apply_1(v_self_7101_, v_log_7102_);
    return v___x_7103_;
}
pub unsafe fn l_Lake_ELogT_run(
    mut v_m_7104_: *mut LeanObject,
    mut v_00_u03b1_7105_: *mut LeanObject,
    mut v_self_7106_: *mut LeanObject,
    mut v_log_7107_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7108_: *mut LeanObject = core::ptr::null_mut();
    v___x_7108_ = lean_apply_1(v_self_7106_, v_log_7107_);
    return v___x_7108_;
}
pub unsafe fn l_Lake_ELogT_run_x27___redArg(
    mut v_inst_7110_: *mut LeanObject,
    mut v_self_7111_: *mut LeanObject,
    mut v_log_7112_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_7113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7116_: *mut LeanObject = core::ptr::null_mut();
    v_map_7113_ = lean_ctor_get(v_inst_7110_, 0);
    lean_inc(v_map_7113_);
    lean_dec_ref(v_inst_7110_);
    v___x_7114_ = l_Lake_ELogT_run_x27___redArg___closed__0;
    v___x_7115_ = lean_apply_1(v_self_7111_, v_log_7112_);
    v___x_7116_ = lean_apply_4(
        v_map_7113_,
        lean_box(0),
        lean_box(0),
        v___x_7114_,
        v___x_7115_,
    );
    return v___x_7116_;
}
pub unsafe fn l_Lake_ELogT_run_x27(
    mut v_m_7117_: *mut LeanObject,
    mut v_00_u03b1_7118_: *mut LeanObject,
    mut v_inst_7119_: *mut LeanObject,
    mut v_self_7120_: *mut LeanObject,
    mut v_log_7121_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_7122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7125_: *mut LeanObject = core::ptr::null_mut();
    v_map_7122_ = lean_ctor_get(v_inst_7119_, 0);
    lean_inc(v_map_7122_);
    lean_dec_ref(v_inst_7119_);
    v___x_7123_ = l_Lake_ELogT_run_x27___redArg___closed__0;
    v___x_7124_ = lean_apply_1(v_self_7120_, v_log_7121_);
    v___x_7125_ = lean_apply_4(
        v_map_7122_,
        lean_box(0),
        lean_box(0),
        v___x_7123_,
        v___x_7124_,
    );
    return v___x_7125_;
}
pub unsafe fn l_Lake_ELogT_toLogT___redArg(
    mut v_inst_7127_: *mut LeanObject,
    mut v_self_7128_: *mut LeanObject,
    mut v_a_7129_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_7130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7133_: *mut LeanObject = core::ptr::null_mut();
    v_map_7130_ = lean_ctor_get(v_inst_7127_, 0);
    lean_inc(v_map_7130_);
    lean_dec_ref(v_inst_7127_);
    v___x_7131_ = l_Lake_ELogT_toLogT___redArg___closed__0;
    v___x_7132_ = lean_apply_1(v_self_7128_, v_a_7129_);
    v___x_7133_ = lean_apply_4(
        v_map_7130_,
        lean_box(0),
        lean_box(0),
        v___x_7131_,
        v___x_7132_,
    );
    return v___x_7133_;
}
pub unsafe fn l_Lake_ELogT_toLogT(
    mut v_m_7134_: *mut LeanObject,
    mut v_00_u03b1_7135_: *mut LeanObject,
    mut v_inst_7136_: *mut LeanObject,
    mut v_self_7137_: *mut LeanObject,
    mut v_a_7138_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_7139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7142_: *mut LeanObject = core::ptr::null_mut();
    v_map_7139_ = lean_ctor_get(v_inst_7136_, 0);
    lean_inc(v_map_7139_);
    lean_dec_ref(v_inst_7136_);
    v___x_7140_ = l_Lake_ELogT_toLogT___redArg___closed__0;
    v___x_7141_ = lean_apply_1(v_self_7137_, v_a_7138_);
    v___x_7142_ = lean_apply_4(
        v_map_7139_,
        lean_box(0),
        lean_box(0),
        v___x_7140_,
        v___x_7141_,
    );
    return v___x_7142_;
}
pub unsafe fn l_Lake_ELogT_toLogT_x3f___redArg(
    mut v_inst_7144_: *mut LeanObject,
    mut v_self_7145_: *mut LeanObject,
    mut v_a_7146_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_7147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7150_: *mut LeanObject = core::ptr::null_mut();
    v_map_7147_ = lean_ctor_get(v_inst_7144_, 0);
    lean_inc(v_map_7147_);
    lean_dec_ref(v_inst_7144_);
    v___x_7148_ = l_Lake_ELogT_toLogT_x3f___redArg___closed__0;
    v___x_7149_ = lean_apply_1(v_self_7145_, v_a_7146_);
    v___x_7150_ = lean_apply_4(
        v_map_7147_,
        lean_box(0),
        lean_box(0),
        v___x_7148_,
        v___x_7149_,
    );
    return v___x_7150_;
}
pub unsafe fn l_Lake_ELogT_toLogT_x3f(
    mut v_m_7151_: *mut LeanObject,
    mut v_00_u03b1_7152_: *mut LeanObject,
    mut v_inst_7153_: *mut LeanObject,
    mut v_self_7154_: *mut LeanObject,
    mut v_a_7155_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_7156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7159_: *mut LeanObject = core::ptr::null_mut();
    v_map_7156_ = lean_ctor_get(v_inst_7153_, 0);
    lean_inc(v_map_7156_);
    lean_dec_ref(v_inst_7153_);
    v___x_7157_ = l_Lake_ELogT_toLogT_x3f___redArg___closed__0;
    v___x_7158_ = lean_apply_1(v_self_7154_, v_a_7155_);
    v___x_7159_ = lean_apply_4(
        v_map_7156_,
        lean_box(0),
        lean_box(0),
        v___x_7157_,
        v___x_7158_,
    );
    return v___x_7159_;
}
pub unsafe fn l_Lake_ELogT_run_x3f___redArg(
    mut v_inst_7160_: *mut LeanObject,
    mut v_self_7161_: *mut LeanObject,
    mut v_log_7162_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_7163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7166_: *mut LeanObject = core::ptr::null_mut();
    v_map_7163_ = lean_ctor_get(v_inst_7160_, 0);
    lean_inc(v_map_7163_);
    lean_dec_ref(v_inst_7160_);
    v___x_7164_ = l_Lake_ELogT_toLogT_x3f___redArg___closed__0;
    v___x_7165_ = lean_apply_1(v_self_7161_, v_log_7162_);
    v___x_7166_ = lean_apply_4(
        v_map_7163_,
        lean_box(0),
        lean_box(0),
        v___x_7164_,
        v___x_7165_,
    );
    return v___x_7166_;
}
pub unsafe fn l_Lake_ELogT_run_x3f(
    mut v_m_7167_: *mut LeanObject,
    mut v_00_u03b1_7168_: *mut LeanObject,
    mut v_inst_7169_: *mut LeanObject,
    mut v_self_7170_: *mut LeanObject,
    mut v_log_7171_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_7172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7175_: *mut LeanObject = core::ptr::null_mut();
    v_map_7172_ = lean_ctor_get(v_inst_7169_, 0);
    lean_inc(v_map_7172_);
    lean_dec_ref(v_inst_7169_);
    v___x_7173_ = l_Lake_ELogT_toLogT_x3f___redArg___closed__0;
    v___x_7174_ = lean_apply_1(v_self_7170_, v_log_7171_);
    v___x_7175_ = lean_apply_4(
        v_map_7172_,
        lean_box(0),
        lean_box(0),
        v___x_7173_,
        v___x_7174_,
    );
    return v___x_7175_;
}
pub unsafe fn l_Lake_ELogT_run_x3f_x27___redArg(
    mut v_inst_7177_: *mut LeanObject,
    mut v_self_7178_: *mut LeanObject,
    mut v_log_7179_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_7180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7183_: *mut LeanObject = core::ptr::null_mut();
    v_map_7180_ = lean_ctor_get(v_inst_7177_, 0);
    lean_inc(v_map_7180_);
    lean_dec_ref(v_inst_7177_);
    v___x_7181_ = l_Lake_ELogT_run_x3f_x27___redArg___closed__0;
    v___x_7182_ = lean_apply_1(v_self_7178_, v_log_7179_);
    v___x_7183_ = lean_apply_4(
        v_map_7180_,
        lean_box(0),
        lean_box(0),
        v___x_7181_,
        v___x_7182_,
    );
    return v___x_7183_;
}
pub unsafe fn l_Lake_ELogT_run_x3f_x27(
    mut v_m_7184_: *mut LeanObject,
    mut v_00_u03b1_7185_: *mut LeanObject,
    mut v_inst_7186_: *mut LeanObject,
    mut v_self_7187_: *mut LeanObject,
    mut v_log_7188_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_7189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7192_: *mut LeanObject = core::ptr::null_mut();
    v_map_7189_ = lean_ctor_get(v_inst_7186_, 0);
    lean_inc(v_map_7189_);
    lean_dec_ref(v_inst_7186_);
    v___x_7190_ = l_Lake_ELogT_run_x3f_x27___redArg___closed__0;
    v___x_7191_ = lean_apply_1(v_self_7187_, v_log_7188_);
    v___x_7192_ = lean_apply_4(
        v_map_7189_,
        lean_box(0),
        lean_box(0),
        v___x_7190_,
        v___x_7191_,
    );
    return v___x_7192_;
}
pub unsafe fn l_Lake_ELogT_catchLog___redArg___lam__0(
    mut v_f_7193_: *mut LeanObject,
    mut v_____x_7194_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_7195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7197_: *mut LeanObject = core::ptr::null_mut();
    v_fst_7195_ = lean_ctor_get(v_____x_7194_, 0);
    lean_inc(v_fst_7195_);
    v_snd_7196_ = lean_ctor_get(v_____x_7194_, 1);
    lean_inc(v_snd_7196_);
    lean_dec_ref(v_____x_7194_);
    v___x_7197_ = lean_apply_2(v_f_7193_, v_fst_7195_, v_snd_7196_);
    return v___x_7197_;
}
pub unsafe fn l_Lake_ELogT_catchLog___redArg___lam__1(
    mut v_toPure_7198_: *mut LeanObject,
    mut v_toBind_7199_: *mut LeanObject,
    mut v___f_7200_: *mut LeanObject,
    mut v_____do__lift_7201_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_7202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7206_: u8 = 0;
    let mut v___x_7208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7211_: u8 = 0;
    let mut v_a_7212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7216_: u8 = 0;
    let mut v___x_7217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7225_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_____do__lift_7201_) == 0 {
                    lean_dec(v___f_7200_);
                    lean_dec(v_toBind_7199_);
                    v_a_7202_ = lean_ctor_get(v_____do__lift_7201_, 0);
                    v_a_7203_ = lean_ctor_get(v_____do__lift_7201_, 1);
                    v_isSharedCheck_7211_ = (!lean_is_exclusive(v_____do__lift_7201_)) as u8;
                    if v_isSharedCheck_7211_ == 0 {
                        v___x_7205_ = v_____do__lift_7201_;
                        v_isShared_7206_ = v_isSharedCheck_7211_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7203_);
                        lean_inc(v_a_7202_);
                        lean_dec(v_____do__lift_7201_);
                        v___x_7205_ = lean_box(0);
                        v_isShared_7206_ = v_isSharedCheck_7211_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7212_ = lean_ctor_get(v_____do__lift_7201_, 0);
                    v_a_7213_ = lean_ctor_get(v_____do__lift_7201_, 1);
                    v_isSharedCheck_7225_ = (!lean_is_exclusive(v_____do__lift_7201_)) as u8;
                    if v_isSharedCheck_7225_ == 0 {
                        v___x_7215_ = v_____do__lift_7201_;
                        v_isShared_7216_ = v_isSharedCheck_7225_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_7213_);
                        lean_inc(v_a_7212_);
                        lean_dec(v_____do__lift_7201_);
                        v___x_7215_ = lean_box(0);
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
                    v_reuseFailAlloc_7210_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7210_, 0, v_a_7202_);
                    lean_ctor_set(v_reuseFailAlloc_7210_, 1, v_a_7203_);
                    v___x_7208_ = v_reuseFailAlloc_7210_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7209_ = lean_apply_2(v_toPure_7198_, lean_box(0), v___x_7208_);
                return v___x_7209_;
            }
            3 => {
                v___x_7217_ = lean_array_get_size(v_a_7213_);
                lean_inc(v_a_7212_);
                v___x_7218_ = l_Array_extract___redArg(v_a_7213_, v_a_7212_, v___x_7217_);
                v___x_7219_ = l_Array_shrink___redArg(v_a_7213_, v_a_7212_);
                lean_dec(v_a_7212_);
                if v_isShared_7216_ == 0 {
                    lean_ctor_set_tag(v___x_7215_, 0);
                    lean_ctor_set(v___x_7215_, 1, v___x_7219_);
                    lean_ctor_set(v___x_7215_, 0, v___x_7218_);
                    v___x_7221_ = v___x_7215_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7224_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7224_, 0, v___x_7218_);
                    lean_ctor_set(v_reuseFailAlloc_7224_, 1, v___x_7219_);
                    v___x_7221_ = v_reuseFailAlloc_7224_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_7222_ = lean_apply_2(v_toPure_7198_, lean_box(0), v___x_7221_);
                v___x_7223_ = lean_apply_4(
                    v_toBind_7199_,
                    lean_box(0),
                    lean_box(0),
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
    mut v_inst_7226_: *mut LeanObject,
    mut v_f_7227_: *mut LeanObject,
    mut v_self_7228_: *mut LeanObject,
    mut v_a_7229_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_7230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_7231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_7232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7236_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_7230_ = lean_ctor_get(v_inst_7226_, 0);
    lean_inc_ref(v_toApplicative_7230_);
    v_toBind_7231_ = lean_ctor_get(v_inst_7226_, 1);
    lean_inc_n(v_toBind_7231_, 2);
    lean_dec_ref(v_inst_7226_);
    v_toPure_7232_ = lean_ctor_get(v_toApplicative_7230_, 1);
    lean_inc(v_toPure_7232_);
    lean_dec_ref(v_toApplicative_7230_);
    v___f_7233_ = lean_alloc_closure(
        l_Lake_ELogT_catchLog___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_7233_, 0, v_f_7227_);
    v___x_7234_ = lean_apply_1(v_self_7228_, v_a_7229_);
    v___f_7235_ = lean_alloc_closure(
        l_Lake_ELogT_catchLog___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_7235_, 0, v_toPure_7232_);
    lean_closure_set(v___f_7235_, 1, v_toBind_7231_);
    lean_closure_set(v___f_7235_, 2, v___f_7233_);
    v___x_7236_ = lean_apply_4(
        v_toBind_7231_,
        lean_box(0),
        lean_box(0),
        v___x_7234_,
        v___f_7235_,
    );
    return v___x_7236_;
}
pub unsafe fn l_Lake_ELogT_catchLog(
    mut v_m_7237_: *mut LeanObject,
    mut v_00_u03b1_7238_: *mut LeanObject,
    mut v_inst_7239_: *mut LeanObject,
    mut v_f_7240_: *mut LeanObject,
    mut v_self_7241_: *mut LeanObject,
    mut v_a_7242_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_7243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_7244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_7245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7249_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_7243_ = lean_ctor_get(v_inst_7239_, 0);
    lean_inc_ref(v_toApplicative_7243_);
    v_toBind_7244_ = lean_ctor_get(v_inst_7239_, 1);
    lean_inc_n(v_toBind_7244_, 2);
    lean_dec_ref(v_inst_7239_);
    v_toPure_7245_ = lean_ctor_get(v_toApplicative_7243_, 1);
    lean_inc(v_toPure_7245_);
    lean_dec_ref(v_toApplicative_7243_);
    v___f_7246_ = lean_alloc_closure(
        l_Lake_ELogT_catchLog___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_7246_, 0, v_f_7240_);
    v___x_7247_ = lean_apply_1(v_self_7241_, v_a_7242_);
    v___f_7248_ = lean_alloc_closure(
        l_Lake_ELogT_catchLog___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_7248_, 0, v_toPure_7245_);
    lean_closure_set(v___f_7248_, 1, v_toBind_7244_);
    lean_closure_set(v___f_7248_, 2, v___f_7246_);
    v___x_7249_ = lean_apply_4(
        v_toBind_7244_,
        lean_box(0),
        lean_box(0),
        v___x_7247_,
        v___f_7248_,
    );
    return v___x_7249_;
}
pub unsafe fn l_Lake_ELogT_takeAndRun___redArg___lam__1(
    mut v_toPure_7250_: *mut LeanObject,
    mut v_a_7251_: *mut LeanObject,
    mut v_____r_7252_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7253_: *mut LeanObject = core::ptr::null_mut();
    v___x_7253_ = lean_apply_2(v_toPure_7250_, lean_box(0), v_a_7251_);
    return v___x_7253_;
}
pub unsafe fn l_Lake_ELogT_takeAndRun___redArg___lam__0(
    mut v_inst_7254_: *mut LeanObject,
    mut v_a_7255_: *mut LeanObject,
    mut v_____r_7256_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_throw_7257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7258_: *mut LeanObject = core::ptr::null_mut();
    v_throw_7257_ = lean_ctor_get(v_inst_7254_, 0);
    lean_inc(v_throw_7257_);
    lean_dec_ref(v_inst_7254_);
    v___x_7258_ = lean_apply_2(v_throw_7257_, lean_box(0), v_a_7255_);
    return v___x_7258_;
}
pub unsafe fn l_Lake_ELogT_takeAndRun___redArg___lam__2(
    mut v_toPure_7259_: *mut LeanObject,
    mut v_set_7260_: *mut LeanObject,
    mut v_toBind_7261_: *mut LeanObject,
    mut v_inst_7262_: *mut LeanObject,
    mut v_____do__lift_7263_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_7263_) == 0 {
        let mut v_a_7264_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_7265_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_7266_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7267_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7268_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_inst_7262_);
        v_a_7264_ = lean_ctor_get(v_____do__lift_7263_, 0);
        lean_inc(v_a_7264_);
        v_a_7265_ = lean_ctor_get(v_____do__lift_7263_, 1);
        lean_inc(v_a_7265_);
        lean_dec_ref_known(v_____do__lift_7263_, 2);
        v___f_7266_ = lean_alloc_closure(
            l_Lake_ELogT_takeAndRun___redArg___lam__1 as *mut core::ffi::c_void,
            3,
            2,
        );
        lean_closure_set(v___f_7266_, 0, v_toPure_7259_);
        lean_closure_set(v___f_7266_, 1, v_a_7264_);
        v___x_7267_ = lean_apply_1(v_set_7260_, v_a_7265_);
        v___x_7268_ = lean_apply_4(
            v_toBind_7261_,
            lean_box(0),
            lean_box(0),
            v___x_7267_,
            v___f_7266_,
        );
        return v___x_7268_;
    } else {
        let mut v_a_7269_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_7270_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_7271_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7272_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7273_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_7259_);
        v_a_7269_ = lean_ctor_get(v_____do__lift_7263_, 0);
        lean_inc(v_a_7269_);
        v_a_7270_ = lean_ctor_get(v_____do__lift_7263_, 1);
        lean_inc(v_a_7270_);
        lean_dec_ref_known(v_____do__lift_7263_, 2);
        v___f_7271_ = lean_alloc_closure(
            l_Lake_ELogT_takeAndRun___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            2,
        );
        lean_closure_set(v___f_7271_, 0, v_inst_7262_);
        lean_closure_set(v___f_7271_, 1, v_a_7269_);
        v___x_7272_ = lean_apply_1(v_set_7260_, v_a_7270_);
        v___x_7273_ = lean_apply_4(
            v_toBind_7261_,
            lean_box(0),
            lean_box(0),
            v___x_7272_,
            v___f_7271_,
        );
        return v___x_7273_;
    }
}
pub unsafe fn l_Lake_ELogT_takeAndRun___redArg___lam__3(
    mut v_self_7274_: *mut LeanObject,
    mut v_inst_7275_: *mut LeanObject,
    mut v_toBind_7276_: *mut LeanObject,
    mut v___f_7277_: *mut LeanObject,
    mut v_____do__lift_7278_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7281_: *mut LeanObject = core::ptr::null_mut();
    v___x_7279_ = lean_apply_1(v_self_7274_, v_____do__lift_7278_);
    v___x_7280_ = lean_apply_2(v_inst_7275_, lean_box(0), v___x_7279_);
    v___x_7281_ = lean_apply_4(
        v_toBind_7276_,
        lean_box(0),
        lean_box(0),
        v___x_7280_,
        v___f_7277_,
    );
    return v___x_7281_;
}
pub unsafe fn l_Lake_ELogT_takeAndRun___redArg(
    mut v_inst_7282_: *mut LeanObject,
    mut v_inst_7283_: *mut LeanObject,
    mut v_inst_7284_: *mut LeanObject,
    mut v_inst_7285_: *mut LeanObject,
    mut v_self_7286_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_7287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_7288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_set_7289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_7290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_7291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7296_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_7287_ = lean_ctor_get(v_inst_7282_, 0);
    lean_inc_ref(v_toApplicative_7287_);
    v_toBind_7288_ = lean_ctor_get(v_inst_7282_, 1);
    lean_inc_n(v_toBind_7288_, 3);
    lean_dec_ref(v_inst_7282_);
    v_set_7289_ = lean_ctor_get(v_inst_7283_, 1);
    lean_inc(v_set_7289_);
    v_modifyGet_7290_ = lean_ctor_get(v_inst_7283_, 2);
    lean_inc(v_modifyGet_7290_);
    lean_dec_ref(v_inst_7283_);
    v_toPure_7291_ = lean_ctor_get(v_toApplicative_7287_, 1);
    lean_inc(v_toPure_7291_);
    lean_dec_ref(v_toApplicative_7287_);
    v___f_7292_ = l_Lake_takeLog___redArg___closed__0;
    v___x_7293_ = lean_apply_2(v_modifyGet_7290_, lean_box(0), v___f_7292_);
    v___f_7294_ = lean_alloc_closure(
        l_Lake_ELogT_takeAndRun___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_7294_, 0, v_toPure_7291_);
    lean_closure_set(v___f_7294_, 1, v_set_7289_);
    lean_closure_set(v___f_7294_, 2, v_toBind_7288_);
    lean_closure_set(v___f_7294_, 3, v_inst_7284_);
    v___f_7295_ = lean_alloc_closure(
        l_Lake_ELogT_takeAndRun___redArg___lam__3 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_7295_, 0, v_self_7286_);
    lean_closure_set(v___f_7295_, 1, v_inst_7285_);
    lean_closure_set(v___f_7295_, 2, v_toBind_7288_);
    lean_closure_set(v___f_7295_, 3, v___f_7294_);
    v___x_7296_ = lean_apply_4(
        v_toBind_7288_,
        lean_box(0),
        lean_box(0),
        v___x_7293_,
        v___f_7295_,
    );
    return v___x_7296_;
}
pub unsafe fn l_Lake_ELogT_takeAndRun(
    mut v_n_7297_: *mut LeanObject,
    mut v_m_7298_: *mut LeanObject,
    mut v_00_u03b1_7299_: *mut LeanObject,
    mut v_inst_7300_: *mut LeanObject,
    mut v_inst_7301_: *mut LeanObject,
    mut v_inst_7302_: *mut LeanObject,
    mut v_inst_7303_: *mut LeanObject,
    mut v_self_7304_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_7305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_7306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_set_7307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_7308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_7309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7314_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_7305_ = lean_ctor_get(v_inst_7300_, 0);
    lean_inc_ref(v_toApplicative_7305_);
    v_toBind_7306_ = lean_ctor_get(v_inst_7300_, 1);
    lean_inc_n(v_toBind_7306_, 3);
    lean_dec_ref(v_inst_7300_);
    v_set_7307_ = lean_ctor_get(v_inst_7301_, 1);
    lean_inc(v_set_7307_);
    v_modifyGet_7308_ = lean_ctor_get(v_inst_7301_, 2);
    lean_inc(v_modifyGet_7308_);
    lean_dec_ref(v_inst_7301_);
    v_toPure_7309_ = lean_ctor_get(v_toApplicative_7305_, 1);
    lean_inc(v_toPure_7309_);
    lean_dec_ref(v_toApplicative_7305_);
    v___f_7310_ = l_Lake_takeLog___redArg___closed__0;
    v___x_7311_ = lean_apply_2(v_modifyGet_7308_, lean_box(0), v___f_7310_);
    v___f_7312_ = lean_alloc_closure(
        l_Lake_ELogT_takeAndRun___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_7312_, 0, v_toPure_7309_);
    lean_closure_set(v___f_7312_, 1, v_set_7307_);
    lean_closure_set(v___f_7312_, 2, v_toBind_7306_);
    lean_closure_set(v___f_7312_, 3, v_inst_7302_);
    v___f_7313_ = lean_alloc_closure(
        l_Lake_ELogT_takeAndRun___redArg___lam__3 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_7313_, 0, v_self_7304_);
    lean_closure_set(v___f_7313_, 1, v_inst_7303_);
    lean_closure_set(v___f_7313_, 2, v_toBind_7306_);
    lean_closure_set(v___f_7313_, 3, v___f_7312_);
    v___x_7314_ = lean_apply_4(
        v_toBind_7306_,
        lean_box(0),
        lean_box(0),
        v___x_7311_,
        v___f_7313_,
    );
    return v___x_7314_;
}
pub unsafe fn l_Lake_ELogT_replayLog_x3f___redArg___lam__2(
    mut v_toPure_7315_: *mut LeanObject,
    mut v_x_7316_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7318_: *mut LeanObject = core::ptr::null_mut();
    v___x_7317_ = lean_box(0);
    v___x_7318_ = lean_apply_2(v_toPure_7315_, lean_box(0), v___x_7317_);
    return v___x_7318_;
}
pub unsafe fn l_Lake_ELogT_replayLog_x3f___redArg___lam__0(
    mut v_a_7319_: *mut LeanObject,
    mut v_toPure_7320_: *mut LeanObject,
    mut v_x_7321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7323_: *mut LeanObject = core::ptr::null_mut();
    v___x_7322_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_7322_, 0, v_a_7319_);
    v___x_7323_ = lean_apply_2(v_toPure_7320_, lean_box(0), v___x_7322_);
    return v___x_7323_;
}
pub unsafe fn l_Lake_ELogT_replayLog_x3f___redArg___lam__1(
    mut v_toPure_7324_: *mut LeanObject,
    mut v___x_7325_: *mut LeanObject,
    mut v_toSeqRight_7326_: *mut LeanObject,
    mut v_inst_7327_: *mut LeanObject,
    mut v___f_7328_: *mut LeanObject,
    mut v___f_7329_: *mut LeanObject,
    mut v___f_7330_: *mut LeanObject,
    mut v_____do__lift_7331_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_7331_) == 0 {
        let mut v_a_7332_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_7333_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_7334_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7335_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7336_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7337_: u8 = 0;
        lean_dec(v___f_7330_);
        lean_dec(v___f_7329_);
        v_a_7332_ = lean_ctor_get(v_____do__lift_7331_, 0);
        lean_inc(v_a_7332_);
        v_a_7333_ = lean_ctor_get(v_____do__lift_7331_, 1);
        lean_inc(v_a_7333_);
        lean_dec_ref_known(v_____do__lift_7331_, 2);
        lean_inc(v_toPure_7324_);
        v___f_7334_ = lean_alloc_closure(
            l_Lake_ELogT_replayLog_x3f___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            2,
        );
        lean_closure_set(v___f_7334_, 0, v_a_7332_);
        lean_closure_set(v___f_7334_, 1, v_toPure_7324_);
        v___x_7335_ = lean_array_get_size(v_a_7333_);
        v___x_7336_ = lean_box(0);
        v___x_7337_ = lean_nat_dec_lt(v___x_7325_, v___x_7335_);
        if v___x_7337_ == 0 {
            let mut v___x_7338_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7339_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_a_7333_);
            lean_dec(v___f_7328_);
            lean_dec_ref(v_inst_7327_);
            v___x_7338_ = lean_apply_2(v_toPure_7324_, lean_box(0), v___x_7336_);
            v___x_7339_ = lean_apply_4(
                v_toSeqRight_7326_,
                lean_box(0),
                lean_box(0),
                v___x_7338_,
                v___f_7334_,
            );
            return v___x_7339_;
        } else {
            let mut v___x_7340_: u8 = 0;
            v___x_7340_ = lean_nat_dec_le(v___x_7335_, v___x_7335_);
            if v___x_7340_ == 0 {
                if v___x_7337_ == 0 {
                    let mut v___x_7341_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_7342_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec(v_a_7333_);
                    lean_dec(v___f_7328_);
                    lean_dec_ref(v_inst_7327_);
                    v___x_7341_ = lean_apply_2(v_toPure_7324_, lean_box(0), v___x_7336_);
                    v___x_7342_ = lean_apply_4(
                        v_toSeqRight_7326_,
                        lean_box(0),
                        lean_box(0),
                        v___x_7341_,
                        v___f_7334_,
                    );
                    return v___x_7342_;
                } else {
                    let mut v___x_7343_: usize = 0;
                    let mut v___x_7344_: usize = 0;
                    let mut v___x_7345_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_7346_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec(v_toPure_7324_);
                    v___x_7343_ = 0usize;
                    v___x_7344_ = lean_usize_of_nat(v___x_7335_);
                    v___x_7345_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                        lean_box(0),
                        lean_box(0),
                        lean_box(0),
                        v_inst_7327_,
                        v___f_7328_,
                        v_a_7333_,
                        v___x_7343_,
                        v___x_7344_,
                        v___x_7336_,
                    );
                    v___x_7346_ = lean_apply_4(
                        v_toSeqRight_7326_,
                        lean_box(0),
                        lean_box(0),
                        v___x_7345_,
                        v___f_7334_,
                    );
                    return v___x_7346_;
                }
            } else {
                let mut v___x_7347_: usize = 0;
                let mut v___x_7348_: usize = 0;
                let mut v___x_7349_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_7350_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_toPure_7324_);
                v___x_7347_ = 0usize;
                v___x_7348_ = lean_usize_of_nat(v___x_7335_);
                v___x_7349_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    v_inst_7327_,
                    v___f_7328_,
                    v_a_7333_,
                    v___x_7347_,
                    v___x_7348_,
                    v___x_7336_,
                );
                v___x_7350_ = lean_apply_4(
                    v_toSeqRight_7326_,
                    lean_box(0),
                    lean_box(0),
                    v___x_7349_,
                    v___f_7334_,
                );
                return v___x_7350_;
            }
        }
    } else {
        let mut v_a_7351_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7352_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7353_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7354_: u8 = 0;
        lean_dec(v___f_7328_);
        v_a_7351_ = lean_ctor_get(v_____do__lift_7331_, 1);
        lean_inc(v_a_7351_);
        lean_dec_ref_known(v_____do__lift_7331_, 2);
        v___x_7352_ = lean_array_get_size(v_a_7351_);
        v___x_7353_ = lean_box(0);
        v___x_7354_ = lean_nat_dec_lt(v___x_7325_, v___x_7352_);
        if v___x_7354_ == 0 {
            let mut v___x_7355_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7356_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_a_7351_);
            lean_dec(v___f_7330_);
            lean_dec_ref(v_inst_7327_);
            v___x_7355_ = lean_apply_2(v_toPure_7324_, lean_box(0), v___x_7353_);
            v___x_7356_ = lean_apply_4(
                v_toSeqRight_7326_,
                lean_box(0),
                lean_box(0),
                v___x_7355_,
                v___f_7329_,
            );
            return v___x_7356_;
        } else {
            let mut v___x_7357_: u8 = 0;
            v___x_7357_ = lean_nat_dec_le(v___x_7352_, v___x_7352_);
            if v___x_7357_ == 0 {
                if v___x_7354_ == 0 {
                    let mut v___x_7358_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_7359_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec(v_a_7351_);
                    lean_dec(v___f_7330_);
                    lean_dec_ref(v_inst_7327_);
                    v___x_7358_ = lean_apply_2(v_toPure_7324_, lean_box(0), v___x_7353_);
                    v___x_7359_ = lean_apply_4(
                        v_toSeqRight_7326_,
                        lean_box(0),
                        lean_box(0),
                        v___x_7358_,
                        v___f_7329_,
                    );
                    return v___x_7359_;
                } else {
                    let mut v___x_7360_: usize = 0;
                    let mut v___x_7361_: usize = 0;
                    let mut v___x_7362_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_7363_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec(v_toPure_7324_);
                    v___x_7360_ = 0usize;
                    v___x_7361_ = lean_usize_of_nat(v___x_7352_);
                    v___x_7362_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                        lean_box(0),
                        lean_box(0),
                        lean_box(0),
                        v_inst_7327_,
                        v___f_7330_,
                        v_a_7351_,
                        v___x_7360_,
                        v___x_7361_,
                        v___x_7353_,
                    );
                    v___x_7363_ = lean_apply_4(
                        v_toSeqRight_7326_,
                        lean_box(0),
                        lean_box(0),
                        v___x_7362_,
                        v___f_7329_,
                    );
                    return v___x_7363_;
                }
            } else {
                let mut v___x_7364_: usize = 0;
                let mut v___x_7365_: usize = 0;
                let mut v___x_7366_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_7367_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_toPure_7324_);
                v___x_7364_ = 0usize;
                v___x_7365_ = lean_usize_of_nat(v___x_7352_);
                v___x_7366_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    v_inst_7327_,
                    v___f_7330_,
                    v_a_7351_,
                    v___x_7364_,
                    v___x_7365_,
                    v___x_7353_,
                );
                v___x_7367_ = lean_apply_4(
                    v_toSeqRight_7326_,
                    lean_box(0),
                    lean_box(0),
                    v___x_7366_,
                    v___f_7329_,
                );
                return v___x_7367_;
            }
        }
    }
}
pub unsafe fn l_Lake_ELogT_replayLog_x3f___redArg___lam__1___boxed(
    mut v_toPure_7368_: *mut LeanObject,
    mut v___x_7369_: *mut LeanObject,
    mut v_toSeqRight_7370_: *mut LeanObject,
    mut v_inst_7371_: *mut LeanObject,
    mut v___f_7372_: *mut LeanObject,
    mut v___f_7373_: *mut LeanObject,
    mut v___f_7374_: *mut LeanObject,
    mut v_____do__lift_7375_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7376_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___x_7369_);
    return v_res_7376_;
}
pub unsafe fn l_Lake_ELogT_replayLog_x3f___redArg(
    mut v_inst_7377_: *mut LeanObject,
    mut v_logger_7378_: *mut LeanObject,
    mut v_inst_7379_: *mut LeanObject,
    mut v_self_7380_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_7381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_7382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_7383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_7384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7392_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_7381_ = lean_ctor_get(v_inst_7377_, 0);
    v_toBind_7382_ = lean_ctor_get(v_inst_7377_, 1);
    lean_inc(v_toBind_7382_);
    v_toPure_7383_ = lean_ctor_get(v_toApplicative_7381_, 1);
    lean_inc_n(v_toPure_7383_, 2);
    v_toSeqRight_7384_ = lean_ctor_get(v_toApplicative_7381_, 4);
    lean_inc(v_toSeqRight_7384_);
    v___f_7385_ = lean_alloc_closure(
        l_Lake_Log_replay___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_7385_, 0, v_logger_7378_);
    v___x_7386_ = lean_unsigned_to_nat(0);
    v___x_7387_ = l_Lake_Log_empty___closed__0;
    v___x_7388_ = lean_apply_1(v_self_7380_, v___x_7387_);
    v___x_7389_ = lean_apply_2(v_inst_7379_, lean_box(0), v___x_7388_);
    v___f_7390_ = lean_alloc_closure(
        l_Lake_ELogT_replayLog_x3f___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_7390_, 0, v_toPure_7383_);
    lean_inc_ref(v___f_7385_);
    v___f_7391_ = lean_alloc_closure(
        l_Lake_ELogT_replayLog_x3f___redArg___lam__1___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    lean_closure_set(v___f_7391_, 0, v_toPure_7383_);
    lean_closure_set(v___f_7391_, 1, v___x_7386_);
    lean_closure_set(v___f_7391_, 2, v_toSeqRight_7384_);
    lean_closure_set(v___f_7391_, 3, v_inst_7377_);
    lean_closure_set(v___f_7391_, 4, v___f_7385_);
    lean_closure_set(v___f_7391_, 5, v___f_7390_);
    lean_closure_set(v___f_7391_, 6, v___f_7385_);
    v___x_7392_ = lean_apply_4(
        v_toBind_7382_,
        lean_box(0),
        lean_box(0),
        v___x_7389_,
        v___f_7391_,
    );
    return v___x_7392_;
}
pub unsafe fn l_Lake_ELogT_replayLog_x3f(
    mut v_n_7393_: *mut LeanObject,
    mut v_m_7394_: *mut LeanObject,
    mut v_00_u03b1_7395_: *mut LeanObject,
    mut v_inst_7396_: *mut LeanObject,
    mut v_logger_7397_: *mut LeanObject,
    mut v_inst_7398_: *mut LeanObject,
    mut v_self_7399_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_7400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_7401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_7402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_7403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7411_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_7400_ = lean_ctor_get(v_inst_7396_, 0);
    v_toBind_7401_ = lean_ctor_get(v_inst_7396_, 1);
    lean_inc(v_toBind_7401_);
    v_toPure_7402_ = lean_ctor_get(v_toApplicative_7400_, 1);
    lean_inc_n(v_toPure_7402_, 2);
    v_toSeqRight_7403_ = lean_ctor_get(v_toApplicative_7400_, 4);
    lean_inc(v_toSeqRight_7403_);
    v___f_7404_ = lean_alloc_closure(
        l_Lake_Log_replay___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_7404_, 0, v_logger_7397_);
    v___x_7405_ = lean_unsigned_to_nat(0);
    v___x_7406_ = l_Lake_Log_empty___closed__0;
    v___x_7407_ = lean_apply_1(v_self_7399_, v___x_7406_);
    v___x_7408_ = lean_apply_2(v_inst_7398_, lean_box(0), v___x_7407_);
    v___f_7409_ = lean_alloc_closure(
        l_Lake_ELogT_replayLog_x3f___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_7409_, 0, v_toPure_7402_);
    lean_inc_ref(v___f_7404_);
    v___f_7410_ = lean_alloc_closure(
        l_Lake_ELogT_replayLog_x3f___redArg___lam__1___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    lean_closure_set(v___f_7410_, 0, v_toPure_7402_);
    lean_closure_set(v___f_7410_, 1, v___x_7405_);
    lean_closure_set(v___f_7410_, 2, v_toSeqRight_7403_);
    lean_closure_set(v___f_7410_, 3, v_inst_7396_);
    lean_closure_set(v___f_7410_, 4, v___f_7404_);
    lean_closure_set(v___f_7410_, 5, v___f_7409_);
    lean_closure_set(v___f_7410_, 6, v___f_7404_);
    v___x_7411_ = lean_apply_4(
        v_toBind_7401_,
        lean_box(0),
        lean_box(0),
        v___x_7408_,
        v___f_7410_,
    );
    return v___x_7411_;
}
pub unsafe fn l_Lake_ELogT_replayLog___redArg___lam__3(
    mut v_toPure_7412_: *mut LeanObject,
    mut v_a_7413_: *mut LeanObject,
    mut v_x_7414_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7415_: *mut LeanObject = core::ptr::null_mut();
    v___x_7415_ = lean_apply_2(v_toPure_7412_, lean_box(0), v_a_7413_);
    return v___x_7415_;
}
pub unsafe fn l_Lake_ELogT_replayLog___redArg___lam__0(
    mut v_toPure_7416_: *mut LeanObject,
    mut v___x_7417_: *mut LeanObject,
    mut v_toApplicative_7418_: *mut LeanObject,
    mut v_toSeqRight_7419_: *mut LeanObject,
    mut v_inst_7420_: *mut LeanObject,
    mut v___f_7421_: *mut LeanObject,
    mut v___f_7422_: *mut LeanObject,
    mut v___f_7423_: *mut LeanObject,
    mut v_____do__lift_7424_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_7424_) == 0 {
        let mut v_a_7425_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_7426_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_7427_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7428_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7429_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7430_: u8 = 0;
        lean_dec(v___f_7423_);
        lean_dec(v___f_7422_);
        v_a_7425_ = lean_ctor_get(v_____do__lift_7424_, 0);
        lean_inc(v_a_7425_);
        v_a_7426_ = lean_ctor_get(v_____do__lift_7424_, 1);
        lean_inc(v_a_7426_);
        lean_dec_ref_known(v_____do__lift_7424_, 2);
        v___f_7427_ = lean_alloc_closure(
            l_Lake_ELogT_replayLog___redArg___lam__3 as *mut core::ffi::c_void,
            3,
            2,
        );
        lean_closure_set(v___f_7427_, 0, v_toPure_7416_);
        lean_closure_set(v___f_7427_, 1, v_a_7425_);
        v___x_7428_ = lean_array_get_size(v_a_7426_);
        v___x_7429_ = lean_box(0);
        v___x_7430_ = lean_nat_dec_lt(v___x_7417_, v___x_7428_);
        if v___x_7430_ == 0 {
            let mut v_toPure_7431_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7432_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7433_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_a_7426_);
            lean_dec(v___f_7421_);
            lean_dec_ref(v_inst_7420_);
            v_toPure_7431_ = lean_ctor_get(v_toApplicative_7418_, 1);
            lean_inc(v_toPure_7431_);
            lean_dec_ref(v_toApplicative_7418_);
            v___x_7432_ = lean_apply_2(v_toPure_7431_, lean_box(0), v___x_7429_);
            v___x_7433_ = lean_apply_4(
                v_toSeqRight_7419_,
                lean_box(0),
                lean_box(0),
                v___x_7432_,
                v___f_7427_,
            );
            return v___x_7433_;
        } else {
            let mut v___x_7434_: u8 = 0;
            v___x_7434_ = lean_nat_dec_le(v___x_7428_, v___x_7428_);
            if v___x_7434_ == 0 {
                if v___x_7430_ == 0 {
                    let mut v_toPure_7435_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_7436_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_7437_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec(v_a_7426_);
                    lean_dec(v___f_7421_);
                    lean_dec_ref(v_inst_7420_);
                    v_toPure_7435_ = lean_ctor_get(v_toApplicative_7418_, 1);
                    lean_inc(v_toPure_7435_);
                    lean_dec_ref(v_toApplicative_7418_);
                    v___x_7436_ = lean_apply_2(v_toPure_7435_, lean_box(0), v___x_7429_);
                    v___x_7437_ = lean_apply_4(
                        v_toSeqRight_7419_,
                        lean_box(0),
                        lean_box(0),
                        v___x_7436_,
                        v___f_7427_,
                    );
                    return v___x_7437_;
                } else {
                    let mut v___x_7438_: usize = 0;
                    let mut v___x_7439_: usize = 0;
                    let mut v___x_7440_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_7441_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec_ref(v_toApplicative_7418_);
                    v___x_7438_ = 0usize;
                    v___x_7439_ = lean_usize_of_nat(v___x_7428_);
                    v___x_7440_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                        lean_box(0),
                        lean_box(0),
                        lean_box(0),
                        v_inst_7420_,
                        v___f_7421_,
                        v_a_7426_,
                        v___x_7438_,
                        v___x_7439_,
                        v___x_7429_,
                    );
                    v___x_7441_ = lean_apply_4(
                        v_toSeqRight_7419_,
                        lean_box(0),
                        lean_box(0),
                        v___x_7440_,
                        v___f_7427_,
                    );
                    return v___x_7441_;
                }
            } else {
                let mut v___x_7442_: usize = 0;
                let mut v___x_7443_: usize = 0;
                let mut v___x_7444_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_7445_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v_toApplicative_7418_);
                v___x_7442_ = 0usize;
                v___x_7443_ = lean_usize_of_nat(v___x_7428_);
                v___x_7444_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    v_inst_7420_,
                    v___f_7421_,
                    v_a_7426_,
                    v___x_7442_,
                    v___x_7443_,
                    v___x_7429_,
                );
                v___x_7445_ = lean_apply_4(
                    v_toSeqRight_7419_,
                    lean_box(0),
                    lean_box(0),
                    v___x_7444_,
                    v___f_7427_,
                );
                return v___x_7445_;
            }
        }
    } else {
        let mut v_a_7446_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7447_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7448_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7449_: u8 = 0;
        lean_dec(v___f_7421_);
        lean_dec(v_toPure_7416_);
        v_a_7446_ = lean_ctor_get(v_____do__lift_7424_, 1);
        lean_inc(v_a_7446_);
        lean_dec_ref_known(v_____do__lift_7424_, 2);
        v___x_7447_ = lean_array_get_size(v_a_7446_);
        v___x_7448_ = lean_box(0);
        v___x_7449_ = lean_nat_dec_lt(v___x_7417_, v___x_7447_);
        if v___x_7449_ == 0 {
            let mut v_toPure_7450_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7451_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7452_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_a_7446_);
            lean_dec(v___f_7423_);
            lean_dec_ref(v_inst_7420_);
            v_toPure_7450_ = lean_ctor_get(v_toApplicative_7418_, 1);
            lean_inc(v_toPure_7450_);
            lean_dec_ref(v_toApplicative_7418_);
            v___x_7451_ = lean_apply_2(v_toPure_7450_, lean_box(0), v___x_7448_);
            v___x_7452_ = lean_apply_4(
                v_toSeqRight_7419_,
                lean_box(0),
                lean_box(0),
                v___x_7451_,
                v___f_7422_,
            );
            return v___x_7452_;
        } else {
            let mut v___x_7453_: u8 = 0;
            v___x_7453_ = lean_nat_dec_le(v___x_7447_, v___x_7447_);
            if v___x_7453_ == 0 {
                if v___x_7449_ == 0 {
                    let mut v_toPure_7454_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_7455_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_7456_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec(v_a_7446_);
                    lean_dec(v___f_7423_);
                    lean_dec_ref(v_inst_7420_);
                    v_toPure_7454_ = lean_ctor_get(v_toApplicative_7418_, 1);
                    lean_inc(v_toPure_7454_);
                    lean_dec_ref(v_toApplicative_7418_);
                    v___x_7455_ = lean_apply_2(v_toPure_7454_, lean_box(0), v___x_7448_);
                    v___x_7456_ = lean_apply_4(
                        v_toSeqRight_7419_,
                        lean_box(0),
                        lean_box(0),
                        v___x_7455_,
                        v___f_7422_,
                    );
                    return v___x_7456_;
                } else {
                    let mut v___x_7457_: usize = 0;
                    let mut v___x_7458_: usize = 0;
                    let mut v___x_7459_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_7460_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec_ref(v_toApplicative_7418_);
                    v___x_7457_ = 0usize;
                    v___x_7458_ = lean_usize_of_nat(v___x_7447_);
                    v___x_7459_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                        lean_box(0),
                        lean_box(0),
                        lean_box(0),
                        v_inst_7420_,
                        v___f_7423_,
                        v_a_7446_,
                        v___x_7457_,
                        v___x_7458_,
                        v___x_7448_,
                    );
                    v___x_7460_ = lean_apply_4(
                        v_toSeqRight_7419_,
                        lean_box(0),
                        lean_box(0),
                        v___x_7459_,
                        v___f_7422_,
                    );
                    return v___x_7460_;
                }
            } else {
                let mut v___x_7461_: usize = 0;
                let mut v___x_7462_: usize = 0;
                let mut v___x_7463_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_7464_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v_toApplicative_7418_);
                v___x_7461_ = 0usize;
                v___x_7462_ = lean_usize_of_nat(v___x_7447_);
                v___x_7463_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    v_inst_7420_,
                    v___f_7423_,
                    v_a_7446_,
                    v___x_7461_,
                    v___x_7462_,
                    v___x_7448_,
                );
                v___x_7464_ = lean_apply_4(
                    v_toSeqRight_7419_,
                    lean_box(0),
                    lean_box(0),
                    v___x_7463_,
                    v___f_7422_,
                );
                return v___x_7464_;
            }
        }
    }
}
pub unsafe fn l_Lake_ELogT_replayLog___redArg___lam__0___boxed(
    mut v_toPure_7465_: *mut LeanObject,
    mut v___x_7466_: *mut LeanObject,
    mut v_toApplicative_7467_: *mut LeanObject,
    mut v_toSeqRight_7468_: *mut LeanObject,
    mut v_inst_7469_: *mut LeanObject,
    mut v___f_7470_: *mut LeanObject,
    mut v___f_7471_: *mut LeanObject,
    mut v___f_7472_: *mut LeanObject,
    mut v_____do__lift_7473_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7474_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___x_7466_);
    return v_res_7474_;
}
pub unsafe fn l_Lake_ELogT_replayLog___redArg(
    mut v_inst_7475_: *mut LeanObject,
    mut v_inst_7476_: *mut LeanObject,
    mut v_logger_7477_: *mut LeanObject,
    mut v_inst_7478_: *mut LeanObject,
    mut v_self_7479_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_7480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_7481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_7482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_failure_7483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_7484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_7485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7493_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_7480_ = lean_ctor_get(v_inst_7475_, 0);
    lean_inc_ref(v_toApplicative_7480_);
    v_toApplicative_7481_ = lean_ctor_get(v_inst_7476_, 0);
    lean_inc_ref(v_toApplicative_7481_);
    v_toBind_7482_ = lean_ctor_get(v_inst_7476_, 1);
    lean_inc(v_toBind_7482_);
    v_failure_7483_ = lean_ctor_get(v_inst_7475_, 1);
    lean_inc(v_failure_7483_);
    lean_dec_ref(v_inst_7475_);
    v_toPure_7484_ = lean_ctor_get(v_toApplicative_7480_, 1);
    lean_inc(v_toPure_7484_);
    v_toSeqRight_7485_ = lean_ctor_get(v_toApplicative_7480_, 4);
    lean_inc(v_toSeqRight_7485_);
    lean_dec_ref(v_toApplicative_7480_);
    v___f_7486_ = lean_alloc_closure(
        l_Lake_Log_replay___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_7486_, 0, v_logger_7477_);
    v___f_7487_ = lean_alloc_closure(
        l_Lake_MonadLog_error___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_7487_, 0, v_failure_7483_);
    v___x_7488_ = lean_unsigned_to_nat(0);
    v___x_7489_ = l_Lake_Log_empty___closed__0;
    v___x_7490_ = lean_apply_1(v_self_7479_, v___x_7489_);
    v___x_7491_ = lean_apply_2(v_inst_7478_, lean_box(0), v___x_7490_);
    lean_inc_ref(v___f_7486_);
    v___f_7492_ = lean_alloc_closure(
        l_Lake_ELogT_replayLog___redArg___lam__0___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    lean_closure_set(v___f_7492_, 0, v_toPure_7484_);
    lean_closure_set(v___f_7492_, 1, v___x_7488_);
    lean_closure_set(v___f_7492_, 2, v_toApplicative_7481_);
    lean_closure_set(v___f_7492_, 3, v_toSeqRight_7485_);
    lean_closure_set(v___f_7492_, 4, v_inst_7476_);
    lean_closure_set(v___f_7492_, 5, v___f_7486_);
    lean_closure_set(v___f_7492_, 6, v___f_7487_);
    lean_closure_set(v___f_7492_, 7, v___f_7486_);
    v___x_7493_ = lean_apply_4(
        v_toBind_7482_,
        lean_box(0),
        lean_box(0),
        v___x_7491_,
        v___f_7492_,
    );
    return v___x_7493_;
}
pub unsafe fn l_Lake_ELogT_replayLog(
    mut v_n_7494_: *mut LeanObject,
    mut v_m_7495_: *mut LeanObject,
    mut v_00_u03b1_7496_: *mut LeanObject,
    mut v_inst_7497_: *mut LeanObject,
    mut v_inst_7498_: *mut LeanObject,
    mut v_logger_7499_: *mut LeanObject,
    mut v_inst_7500_: *mut LeanObject,
    mut v_self_7501_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_7502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_7503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_7504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_failure_7505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_7506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_7507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7515_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_7502_ = lean_ctor_get(v_inst_7497_, 0);
    lean_inc_ref(v_toApplicative_7502_);
    v_toApplicative_7503_ = lean_ctor_get(v_inst_7498_, 0);
    lean_inc_ref(v_toApplicative_7503_);
    v_toBind_7504_ = lean_ctor_get(v_inst_7498_, 1);
    lean_inc(v_toBind_7504_);
    v_failure_7505_ = lean_ctor_get(v_inst_7497_, 1);
    lean_inc(v_failure_7505_);
    lean_dec_ref(v_inst_7497_);
    v_toPure_7506_ = lean_ctor_get(v_toApplicative_7502_, 1);
    lean_inc(v_toPure_7506_);
    v_toSeqRight_7507_ = lean_ctor_get(v_toApplicative_7502_, 4);
    lean_inc(v_toSeqRight_7507_);
    lean_dec_ref(v_toApplicative_7502_);
    v___f_7508_ = lean_alloc_closure(
        l_Lake_Log_replay___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_7508_, 0, v_logger_7499_);
    v___f_7509_ = lean_alloc_closure(
        l_Lake_MonadLog_error___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_7509_, 0, v_failure_7505_);
    v___x_7510_ = lean_unsigned_to_nat(0);
    v___x_7511_ = l_Lake_Log_empty___closed__0;
    v___x_7512_ = lean_apply_1(v_self_7501_, v___x_7511_);
    v___x_7513_ = lean_apply_2(v_inst_7500_, lean_box(0), v___x_7512_);
    lean_inc_ref(v___f_7508_);
    v___f_7514_ = lean_alloc_closure(
        l_Lake_ELogT_replayLog___redArg___lam__0___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    lean_closure_set(v___f_7514_, 0, v_toPure_7506_);
    lean_closure_set(v___f_7514_, 1, v___x_7510_);
    lean_closure_set(v___f_7514_, 2, v_toApplicative_7503_);
    lean_closure_set(v___f_7514_, 3, v_toSeqRight_7507_);
    lean_closure_set(v___f_7514_, 4, v_inst_7498_);
    lean_closure_set(v___f_7514_, 5, v___f_7508_);
    lean_closure_set(v___f_7514_, 6, v___f_7509_);
    lean_closure_set(v___f_7514_, 7, v___f_7508_);
    v___x_7515_ = lean_apply_4(
        v_toBind_7504_,
        lean_box(0),
        lean_box(0),
        v___x_7513_,
        v___f_7514_,
    );
    return v___x_7515_;
}
pub unsafe fn l_Lake_LogConfig_getLogger___redArg___lam__0(
    mut v_val_7516_: *mut LeanObject,
    mut v_outLv_7517_: u8,
    mut v_val_7518_: u8,
    mut v_inst_7519_: *mut LeanObject,
    mut v_e_7520_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7524_: *mut LeanObject = core::ptr::null_mut();
    v___x_7521_ = lean_box((v_outLv_7517_) as usize);
    v___x_7522_ = lean_box((v_val_7518_) as usize);
    v___x_7523_ = lean_alloc_closure(l_Lake_logToStream___boxed as *mut core::ffi::c_void, 5, 4);
    lean_closure_set(v___x_7523_, 0, v_e_7520_);
    lean_closure_set(v___x_7523_, 1, v_val_7516_);
    lean_closure_set(v___x_7523_, 2, v___x_7521_);
    lean_closure_set(v___x_7523_, 3, v___x_7522_);
    v___x_7524_ = lean_apply_2(v_inst_7519_, lean_box(0), v___x_7523_);
    return v___x_7524_;
}
pub unsafe fn l_Lake_LogConfig_getLogger___redArg___lam__0___boxed(
    mut v_val_7525_: *mut LeanObject,
    mut v_outLv_7526_: *mut LeanObject,
    mut v_val_7527_: *mut LeanObject,
    mut v_inst_7528_: *mut LeanObject,
    mut v_e_7529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_outLv_boxed_7530_: u8 = 0;
    let mut v_val_44__boxed_7531_: u8 = 0;
    let mut v_res_7532_: *mut LeanObject = core::ptr::null_mut();
    v_outLv_boxed_7530_ = (lean_unbox(v_outLv_7526_) as u8);
    v_val_44__boxed_7531_ = (lean_unbox(v_val_7527_) as u8);
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
    mut v_inst_7533_: *mut LeanObject,
    mut v_self_7534_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_outLv_7536_: u8 = 0;
    let mut v_ansiMode_7537_: u8 = 0;
    let mut v_out_7538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7540_: u8 = 0;
    let mut v___x_7541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7543_: *mut LeanObject = core::ptr::null_mut();
    v_outLv_7536_ = lean_ctor_get_uint8(
        v_self_7534_,
        (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
    );
    v_ansiMode_7537_ = lean_ctor_get_uint8(
        v_self_7534_,
        (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
    );
    v_out_7538_ = lean_ctor_get(v_self_7534_, 0);
    v___x_7539_ = l_Lake_OutStream_get(v_out_7538_);
    lean_inc_ref(v___x_7539_);
    v___x_7540_ = l_Lake_AnsiMode_isEnabled(v___x_7539_, v_ansiMode_7537_);
    v___x_7541_ = lean_box((v_outLv_7536_) as usize);
    v___x_7542_ = lean_box((v___x_7540_) as usize);
    v___f_7543_ = lean_alloc_closure(
        l_Lake_LogConfig_getLogger___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_7543_, 0, v___x_7539_);
    lean_closure_set(v___f_7543_, 1, v___x_7541_);
    lean_closure_set(v___f_7543_, 2, v___x_7542_);
    lean_closure_set(v___f_7543_, 3, v_inst_7533_);
    return v___f_7543_;
}
pub unsafe fn l_Lake_LogConfig_getLogger___redArg___boxed(
    mut v_inst_7544_: *mut LeanObject,
    mut v_self_7545_: *mut LeanObject,
    mut v_a_7546_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7547_: *mut LeanObject = core::ptr::null_mut();
    v_res_7547_ = l_Lake_LogConfig_getLogger___redArg(v_inst_7544_, v_self_7545_);
    lean_dec_ref(v_self_7545_);
    return v_res_7547_;
}
pub unsafe fn l_Lake_LogConfig_getLogger(
    mut v_m_7548_: *mut LeanObject,
    mut v_inst_7549_: *mut LeanObject,
    mut v_self_7550_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_outLv_7552_: u8 = 0;
    let mut v_ansiMode_7553_: u8 = 0;
    let mut v_out_7554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7556_: u8 = 0;
    let mut v___x_7557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7559_: *mut LeanObject = core::ptr::null_mut();
    v_outLv_7552_ = lean_ctor_get_uint8(
        v_self_7550_,
        (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
    );
    v_ansiMode_7553_ = lean_ctor_get_uint8(
        v_self_7550_,
        (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
    );
    v_out_7554_ = lean_ctor_get(v_self_7550_, 0);
    v___x_7555_ = l_Lake_OutStream_get(v_out_7554_);
    lean_inc_ref(v___x_7555_);
    v___x_7556_ = l_Lake_AnsiMode_isEnabled(v___x_7555_, v_ansiMode_7553_);
    v___x_7557_ = lean_box((v_outLv_7552_) as usize);
    v___x_7558_ = lean_box((v___x_7556_) as usize);
    v___f_7559_ = lean_alloc_closure(
        l_Lake_LogConfig_getLogger___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_7559_, 0, v___x_7555_);
    lean_closure_set(v___f_7559_, 1, v___x_7557_);
    lean_closure_set(v___f_7559_, 2, v___x_7558_);
    lean_closure_set(v___f_7559_, 3, v_inst_7549_);
    return v___f_7559_;
}
pub unsafe fn l_Lake_LogConfig_getLogger___boxed(
    mut v_m_7560_: *mut LeanObject,
    mut v_inst_7561_: *mut LeanObject,
    mut v_self_7562_: *mut LeanObject,
    mut v_a_7563_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7564_: *mut LeanObject = core::ptr::null_mut();
    v_res_7564_ = l_Lake_LogConfig_getLogger(v_m_7560_, v_inst_7561_, v_self_7562_);
    lean_dec_ref(v_self_7562_);
    return v_res_7564_;
}
pub unsafe fn l_Lake_LogIO_instMonadLiftIO___lam__0(
    mut v_00_u03b1_7565_: *mut LeanObject,
    mut v___y_7566_: *mut LeanObject,
    mut v___y_7567_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7569_: *mut LeanObject = core::ptr::null_mut();
    v___x_7569_ = lean_apply_1(v___y_7566_, lean_box(0));
    if lean_obj_tag(v___x_7569_) == 0 {
        let mut v_a_7570_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7571_: *mut LeanObject = core::ptr::null_mut();
        v_a_7570_ = lean_ctor_get(v___x_7569_, 0);
        lean_inc(v_a_7570_);
        lean_dec_ref_known(v___x_7569_, 1);
        v___x_7571_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_7571_, 0, v_a_7570_);
        lean_ctor_set(v___x_7571_, 1, v___y_7567_);
        return v___x_7571_;
    } else {
        let mut v_a_7572_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7573_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7574_: u8 = 0;
        let mut v___x_7575_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7576_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7577_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7578_: *mut LeanObject = core::ptr::null_mut();
        v_a_7572_ = lean_ctor_get(v___x_7569_, 0);
        lean_inc(v_a_7572_);
        lean_dec_ref_known(v___x_7569_, 1);
        v___x_7573_ = lean_io_error_to_string(v_a_7572_);
        v___x_7574_ = 3;
        v___x_7575_ = lean_alloc_ctor(0, 1, (1) as u32);
        lean_ctor_set(v___x_7575_, 0, v___x_7573_);
        lean_ctor_set_uint8(
            v___x_7575_,
            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
            v___x_7574_,
        );
        v___x_7576_ = lean_array_get_size(v___y_7567_);
        v___x_7577_ = lean_array_push(v___y_7567_, v___x_7575_);
        v___x_7578_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_7578_, 0, v___x_7576_);
        lean_ctor_set(v___x_7578_, 1, v___x_7577_);
        return v___x_7578_;
    }
}
pub unsafe fn l_Lake_LogIO_instMonadLiftIO___lam__0___boxed(
    mut v_00_u03b1_7579_: *mut LeanObject,
    mut v___y_7580_: *mut LeanObject,
    mut v___y_7581_: *mut LeanObject,
    mut v___y_7582_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7583_: *mut LeanObject = core::ptr::null_mut();
    v_res_7583_ = l_Lake_LogIO_instMonadLiftIO___lam__0(v_00_u03b1_7579_, v___y_7580_, v___y_7581_);
    return v_res_7583_;
}
pub unsafe fn l_Lake_LogIO_toBaseIO___redArg___lam__0(
    mut v_val_7586_: *mut LeanObject,
    mut v___y_7587_: u8,
    mut v_val_7588_: u8,
    mut v_x_7589_: *mut LeanObject,
    mut v___y_7590_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7592_: *mut LeanObject = core::ptr::null_mut();
    v___x_7592_ = l_Lake_logToStream(v___y_7590_, v_val_7586_, v___y_7587_, v_val_7588_);
    return v___x_7592_;
}
pub unsafe fn l_Lake_LogIO_toBaseIO___redArg___lam__0___boxed(
    mut v_val_7593_: *mut LeanObject,
    mut v___y_7594_: *mut LeanObject,
    mut v_val_7595_: *mut LeanObject,
    mut v_x_7596_: *mut LeanObject,
    mut v___y_7597_: *mut LeanObject,
    mut v___y_7598_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_862__boxed_7599_: u8 = 0;
    let mut v_val_863__boxed_7600_: u8 = 0;
    let mut v_res_7601_: *mut LeanObject = core::ptr::null_mut();
    v___y_862__boxed_7599_ = (lean_unbox(v___y_7594_) as u8);
    v_val_863__boxed_7600_ = (lean_unbox(v_val_7595_) as u8);
    v_res_7601_ = l_Lake_LogIO_toBaseIO___redArg___lam__0(
        v_val_7593_,
        v___y_862__boxed_7599_,
        v_val_863__boxed_7600_,
        v_x_7596_,
        v___y_7597_,
    );
    lean_dec_ref(v___y_7597_);
    return v_res_7601_;
}
pub unsafe fn l_Lake_LogIO_toBaseIO___redArg(
    mut v_self_7602_: *mut LeanObject,
    mut v_cfg_7603_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_7606_: u8 = 0;
    let mut v___y_7607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7610_: u8 = 0;
    let mut v___y_7611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7615_: u8 = 0;
    let mut v___y_7616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7618_: u8 = 0;
    let mut v_ansiMode_7619_: u8 = 0;
    let mut v_out_7620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7622_: u8 = 0;
    let mut v___x_7623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7625_: u8 = 0;
    let mut v___x_7626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7630_: u8 = 0;
    let mut v___x_7631_: usize = 0;
    let mut v___x_7632_: usize = 0;
    let mut v___x_652__overap_7633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7635_: usize = 0;
    let mut v___x_7636_: usize = 0;
    let mut v___x_656__overap_7637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7642_: u8 = 0;
    let mut v___x_7643_: u8 = 0;
    let mut v___x_7644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_failLv_7648_: u8 = 0;
    let mut v_outLv_7649_: u8 = 0;
    let mut v___x_7650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7651_: u8 = 0;
    let mut v___x_7652_: u8 = 0;
    let mut v___x_7653_: u8 = 0;
    let mut v___x_7654_: u8 = 0;
    let mut v_a_7655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7657_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7613_ = l_instMonadBaseIO;
                v___x_7644_ = l_Lake_Log_empty___closed__0;
                v___x_7645_ = lean_apply_2(v_self_7602_, v___x_7644_, lean_box(0));
                if lean_obj_tag(v___x_7645_) == 0 {
                    v_a_7646_ = lean_ctor_get(v___x_7645_, 0);
                    lean_inc(v_a_7646_);
                    v_a_7647_ = lean_ctor_get(v___x_7645_, 1);
                    lean_inc(v_a_7647_);
                    lean_dec_ref_known(v___x_7645_, 2);
                    v_failLv_7648_ = lean_ctor_get_uint8(
                        v_cfg_7603_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    v_outLv_7649_ = lean_ctor_get_uint8(
                        v_cfg_7603_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                    );
                    v___x_7650_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_7650_, 0, v_a_7646_);
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
                    v_a_7655_ = lean_ctor_get(v___x_7645_, 1);
                    lean_inc(v_a_7655_);
                    lean_dec_ref_known(v___x_7645_, 2);
                    v___x_7656_ = lean_box(0);
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
                    lean_dec(v___y_7607_);
                    v___x_7608_ = lean_box(0);
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
                v_ansiMode_7619_ = lean_ctor_get_uint8(
                    v_cfg_7603_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
                );
                v_out_7620_ = lean_ctor_get(v_cfg_7603_, 0);
                v___x_7621_ = l_Lake_OutStream_get(v_out_7620_);
                lean_inc_ref(v___x_7621_);
                v___x_7622_ = l_Lake_AnsiMode_isEnabled(v___x_7621_, v_ansiMode_7619_);
                v___x_7623_ = lean_unsigned_to_nat(0);
                v___x_7624_ = lean_array_get_size(v___y_7617_);
                v___x_7625_ = lean_nat_dec_lt(v___x_7623_, v___x_7624_);
                if v___x_7625_ == 0 {
                    lean_dec_ref(v___x_7621_);
                    lean_dec_ref(v___y_7617_);
                    v___y_7606_ = v___y_7615_;
                    v___y_7607_ = v___y_7616_;
                    state = 1;
                    continue;
                } else {
                    v___x_7626_ = lean_box((v___y_7618_) as usize);
                    v___x_7627_ = lean_box((v___x_7622_) as usize);
                    v___f_7628_ = lean_alloc_closure(
                        l_Lake_LogIO_toBaseIO___redArg___lam__0___boxed as *mut core::ffi::c_void,
                        6,
                        3,
                    );
                    lean_closure_set(v___f_7628_, 0, v___x_7621_);
                    lean_closure_set(v___f_7628_, 1, v___x_7626_);
                    lean_closure_set(v___f_7628_, 2, v___x_7627_);
                    v___x_7629_ = lean_box(0);
                    v___x_7630_ = lean_nat_dec_le(v___x_7624_, v___x_7624_);
                    if v___x_7630_ == 0 {
                        if v___x_7625_ == 0 {
                            lean_dec_ref(v___f_7628_);
                            lean_dec_ref(v___y_7617_);
                            v___y_7606_ = v___y_7615_;
                            v___y_7607_ = v___y_7616_;
                            state = 1;
                            continue;
                        } else {
                            v___x_7631_ = 0usize;
                            v___x_7632_ = lean_usize_of_nat(v___x_7624_);
                            v___x_652__overap_7633_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    lean_box(0),
                                    lean_box(0),
                                    lean_box(0),
                                    v___x_7613_,
                                    v___f_7628_,
                                    v___y_7617_,
                                    v___x_7631_,
                                    v___x_7632_,
                                    v___x_7629_,
                                );
                            v___x_7634_ = lean_apply_1(v___x_652__overap_7633_, lean_box(0));
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
                                lean_box(0),
                                lean_box(0),
                                lean_box(0),
                                v___x_7613_,
                                v___f_7628_,
                                v___y_7617_,
                                v___x_7635_,
                                v___x_7636_,
                                v___x_7629_,
                            );
                        v___x_7638_ = lean_apply_1(v___x_656__overap_7637_, lean_box(0));
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
    mut v_self_7658_: *mut LeanObject,
    mut v_cfg_7659_: *mut LeanObject,
    mut v_a_7660_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7661_: *mut LeanObject = core::ptr::null_mut();
    v_res_7661_ = l_Lake_LogIO_toBaseIO___redArg(v_self_7658_, v_cfg_7659_);
    lean_dec_ref(v_cfg_7659_);
    return v_res_7661_;
}
pub unsafe fn l_Lake_LogIO_toBaseIO(
    mut v_00_u03b1_7662_: *mut LeanObject,
    mut v_self_7663_: *mut LeanObject,
    mut v_cfg_7664_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_7667_: u8 = 0;
    let mut v___y_7668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7671_: u8 = 0;
    let mut v___y_7672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7676_: u8 = 0;
    let mut v___y_7677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7679_: u8 = 0;
    let mut v_ansiMode_7680_: u8 = 0;
    let mut v_out_7681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7683_: u8 = 0;
    let mut v___x_7684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7686_: u8 = 0;
    let mut v___x_7687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7691_: u8 = 0;
    let mut v___x_7692_: usize = 0;
    let mut v___x_7693_: usize = 0;
    let mut v___x_791__overap_7694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7696_: usize = 0;
    let mut v___x_7697_: usize = 0;
    let mut v___x_794__overap_7698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7703_: u8 = 0;
    let mut v___x_7704_: u8 = 0;
    let mut v___x_7705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_failLv_7709_: u8 = 0;
    let mut v_outLv_7710_: u8 = 0;
    let mut v___x_7711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7712_: u8 = 0;
    let mut v___x_7713_: u8 = 0;
    let mut v___x_7714_: u8 = 0;
    let mut v___x_7715_: u8 = 0;
    let mut v_a_7716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7718_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7674_ = l_instMonadBaseIO;
                v___x_7705_ = l_Lake_Log_empty___closed__0;
                v___x_7706_ = lean_apply_2(v_self_7663_, v___x_7705_, lean_box(0));
                if lean_obj_tag(v___x_7706_) == 0 {
                    v_a_7707_ = lean_ctor_get(v___x_7706_, 0);
                    lean_inc(v_a_7707_);
                    v_a_7708_ = lean_ctor_get(v___x_7706_, 1);
                    lean_inc(v_a_7708_);
                    lean_dec_ref_known(v___x_7706_, 2);
                    v_failLv_7709_ = lean_ctor_get_uint8(
                        v_cfg_7664_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    v_outLv_7710_ = lean_ctor_get_uint8(
                        v_cfg_7664_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                    );
                    v___x_7711_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_7711_, 0, v_a_7707_);
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
                    v_a_7716_ = lean_ctor_get(v___x_7706_, 1);
                    lean_inc(v_a_7716_);
                    lean_dec_ref_known(v___x_7706_, 2);
                    v___x_7717_ = lean_box(0);
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
                    lean_dec(v___y_7668_);
                    v___x_7669_ = lean_box(0);
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
                v_ansiMode_7680_ = lean_ctor_get_uint8(
                    v_cfg_7664_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
                );
                v_out_7681_ = lean_ctor_get(v_cfg_7664_, 0);
                v___x_7682_ = l_Lake_OutStream_get(v_out_7681_);
                lean_inc_ref(v___x_7682_);
                v___x_7683_ = l_Lake_AnsiMode_isEnabled(v___x_7682_, v_ansiMode_7680_);
                v___x_7684_ = lean_unsigned_to_nat(0);
                v___x_7685_ = lean_array_get_size(v___y_7678_);
                v___x_7686_ = lean_nat_dec_lt(v___x_7684_, v___x_7685_);
                if v___x_7686_ == 0 {
                    lean_dec_ref(v___x_7682_);
                    lean_dec_ref(v___y_7678_);
                    v___y_7667_ = v___y_7676_;
                    v___y_7668_ = v___y_7677_;
                    state = 1;
                    continue;
                } else {
                    v___x_7687_ = lean_box((v___y_7679_) as usize);
                    v___x_7688_ = lean_box((v___x_7683_) as usize);
                    v___f_7689_ = lean_alloc_closure(
                        l_Lake_LogIO_toBaseIO___redArg___lam__0___boxed as *mut core::ffi::c_void,
                        6,
                        3,
                    );
                    lean_closure_set(v___f_7689_, 0, v___x_7682_);
                    lean_closure_set(v___f_7689_, 1, v___x_7687_);
                    lean_closure_set(v___f_7689_, 2, v___x_7688_);
                    v___x_7690_ = lean_box(0);
                    v___x_7691_ = lean_nat_dec_le(v___x_7685_, v___x_7685_);
                    if v___x_7691_ == 0 {
                        if v___x_7686_ == 0 {
                            lean_dec_ref(v___f_7689_);
                            lean_dec_ref(v___y_7678_);
                            v___y_7667_ = v___y_7676_;
                            v___y_7668_ = v___y_7677_;
                            state = 1;
                            continue;
                        } else {
                            v___x_7692_ = 0usize;
                            v___x_7693_ = lean_usize_of_nat(v___x_7685_);
                            v___x_791__overap_7694_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    lean_box(0),
                                    lean_box(0),
                                    lean_box(0),
                                    v___x_7674_,
                                    v___f_7689_,
                                    v___y_7678_,
                                    v___x_7692_,
                                    v___x_7693_,
                                    v___x_7690_,
                                );
                            v___x_7695_ = lean_apply_1(v___x_791__overap_7694_, lean_box(0));
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
                                lean_box(0),
                                lean_box(0),
                                lean_box(0),
                                v___x_7674_,
                                v___f_7689_,
                                v___y_7678_,
                                v___x_7696_,
                                v___x_7697_,
                                v___x_7690_,
                            );
                        v___x_7699_ = lean_apply_1(v___x_794__overap_7698_, lean_box(0));
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
    mut v_00_u03b1_7719_: *mut LeanObject,
    mut v_self_7720_: *mut LeanObject,
    mut v_cfg_7721_: *mut LeanObject,
    mut v_a_7722_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7723_: *mut LeanObject = core::ptr::null_mut();
    v_res_7723_ = l_Lake_LogIO_toBaseIO(v_00_u03b1_7719_, v_self_7720_, v_cfg_7721_);
    lean_dec_ref(v_cfg_7721_);
    return v_res_7723_;
}
pub unsafe fn l_Lake_LogIO_captureLog___redArg(
    mut v_inst_7724_: *mut LeanObject,
    mut v_self_7725_: *mut LeanObject,
    mut v_log_7726_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_7727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7730_: *mut LeanObject = core::ptr::null_mut();
    v_map_7727_ = lean_ctor_get(v_inst_7724_, 0);
    lean_inc(v_map_7727_);
    lean_dec_ref(v_inst_7724_);
    v___x_7728_ = l_Lake_ELogT_toLogT_x3f___redArg___closed__0;
    v___x_7729_ = lean_apply_1(v_self_7725_, v_log_7726_);
    v___x_7730_ = lean_apply_4(
        v_map_7727_,
        lean_box(0),
        lean_box(0),
        v___x_7728_,
        v___x_7729_,
    );
    return v___x_7730_;
}
pub unsafe fn l_Lake_LogIO_captureLog(
    mut v_m_7731_: *mut LeanObject,
    mut v_00_u03b1_7732_: *mut LeanObject,
    mut v_inst_7733_: *mut LeanObject,
    mut v_self_7734_: *mut LeanObject,
    mut v_log_7735_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_7736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7739_: *mut LeanObject = core::ptr::null_mut();
    v_map_7736_ = lean_ctor_get(v_inst_7733_, 0);
    lean_inc(v_map_7736_);
    lean_dec_ref(v_inst_7733_);
    v___x_7737_ = l_Lake_ELogT_toLogT_x3f___redArg___closed__0;
    v___x_7738_ = lean_apply_1(v_self_7734_, v_log_7735_);
    v___x_7739_ = lean_apply_4(
        v_map_7736_,
        lean_box(0),
        lean_box(0),
        v___x_7737_,
        v___x_7738_,
    );
    return v___x_7739_;
}
pub unsafe fn l_Lake_LoggerIO_instMonadError___lam__0(
    mut v_00_u03b1_7740_: *mut LeanObject,
    mut v___y_7741_: *mut LeanObject,
    mut v___y_7742_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7744_: u8 = 0;
    let mut v___x_7745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7748_: *mut LeanObject = core::ptr::null_mut();
    v___x_7744_ = 3;
    v___x_7745_ = lean_alloc_ctor(0, 1, (1) as u32);
    lean_ctor_set(v___x_7745_, 0, v___y_7741_);
    lean_ctor_set_uint8(
        v___x_7745_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_7744_,
    );
    lean_inc_ref(v___y_7742_);
    v___x_7746_ = lean_apply_2(v___y_7742_, v___x_7745_, lean_box(0));
    v___x_7747_ = lean_box(0);
    v___x_7748_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_7748_, 0, v___x_7747_);
    return v___x_7748_;
}
pub unsafe fn l_Lake_LoggerIO_instMonadError___lam__0___boxed(
    mut v_00_u03b1_7749_: *mut LeanObject,
    mut v___y_7750_: *mut LeanObject,
    mut v___y_7751_: *mut LeanObject,
    mut v___y_7752_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7753_: *mut LeanObject = core::ptr::null_mut();
    v_res_7753_ =
        l_Lake_LoggerIO_instMonadError___lam__0(v_00_u03b1_7749_, v___y_7750_, v___y_7751_);
    lean_dec_ref(v___y_7751_);
    return v_res_7753_;
}
pub unsafe fn l_Lake_LoggerIO_instMonadLiftIO___lam__0(
    mut v_00_u03b1_7756_: *mut LeanObject,
    mut v___y_7757_: *mut LeanObject,
    mut v___y_7758_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7764_: u8 = 0;
    let mut v___x_7766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7768_: u8 = 0;
    let mut v_a_7769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7772_: u8 = 0;
    let mut v___x_7773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7774_: u8 = 0;
    let mut v___x_7775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7781_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7760_ = lean_apply_1(v___y_7757_, lean_box(0));
                if lean_obj_tag(v___x_7760_) == 0 {
                    v_a_7761_ = lean_ctor_get(v___x_7760_, 0);
                    v_isSharedCheck_7768_ = (!lean_is_exclusive(v___x_7760_)) as u8;
                    if v_isSharedCheck_7768_ == 0 {
                        v___x_7763_ = v___x_7760_;
                        v_isShared_7764_ = v_isSharedCheck_7768_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7761_);
                        lean_dec(v___x_7760_);
                        v___x_7763_ = lean_box(0);
                        v_isShared_7764_ = v_isSharedCheck_7768_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7769_ = lean_ctor_get(v___x_7760_, 0);
                    v_isSharedCheck_7781_ = (!lean_is_exclusive(v___x_7760_)) as u8;
                    if v_isSharedCheck_7781_ == 0 {
                        v___x_7771_ = v___x_7760_;
                        v_isShared_7772_ = v_isSharedCheck_7781_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_7769_);
                        lean_dec(v___x_7760_);
                        v___x_7771_ = lean_box(0);
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
                    v_reuseFailAlloc_7767_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7767_, 0, v_a_7761_);
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
                v___x_7775_ = lean_alloc_ctor(0, 1, (1) as u32);
                lean_ctor_set(v___x_7775_, 0, v___x_7773_);
                lean_ctor_set_uint8(
                    v___x_7775_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_7774_,
                );
                lean_inc_ref(v___y_7758_);
                v___x_7776_ = lean_apply_2(v___y_7758_, v___x_7775_, lean_box(0));
                v___x_7777_ = lean_box(0);
                if v_isShared_7772_ == 0 {
                    lean_ctor_set(v___x_7771_, 0, v___x_7777_);
                    v___x_7779_ = v___x_7771_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7780_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7780_, 0, v___x_7777_);
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
    mut v_00_u03b1_7782_: *mut LeanObject,
    mut v___y_7783_: *mut LeanObject,
    mut v___y_7784_: *mut LeanObject,
    mut v___y_7785_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7786_: *mut LeanObject = core::ptr::null_mut();
    v_res_7786_ =
        l_Lake_LoggerIO_instMonadLiftIO___lam__0(v_00_u03b1_7782_, v___y_7783_, v___y_7784_);
    lean_dec_ref(v___y_7784_);
    return v_res_7786_;
}
pub unsafe fn l_Lake_LoggerIO_instMonadLiftLogIO___lam__0(
    mut v_x_7789_: *mut LeanObject,
    mut v___y_7790_: *mut LeanObject,
    mut v___y_7791_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7794_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v___y_7791_);
    v___x_7793_ = lean_apply_2(v___y_7791_, v___y_7790_, lean_box(0));
    v___x_7794_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_7794_, 0, v___x_7793_);
    return v___x_7794_;
}
pub unsafe fn l_Lake_LoggerIO_instMonadLiftLogIO___lam__0___boxed(
    mut v_x_7795_: *mut LeanObject,
    mut v___y_7796_: *mut LeanObject,
    mut v___y_7797_: *mut LeanObject,
    mut v___y_7798_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7799_: *mut LeanObject = core::ptr::null_mut();
    v_res_7799_ = l_Lake_LoggerIO_instMonadLiftLogIO___lam__0(v_x_7795_, v___y_7796_, v___y_7797_);
    lean_dec_ref(v___y_7797_);
    return v_res_7799_;
}
pub unsafe fn l_Lake_LoggerIO_instMonadLiftLogIO___lam__2(
    mut v___x_7800_: *mut LeanObject,
    mut v___f_7801_: *mut LeanObject,
    mut v___f_7802_: *mut LeanObject,
    mut v_00_u03b1_7803_: *mut LeanObject,
    mut v___y_7804_: *mut LeanObject,
    mut v___y_7805_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7816_: u8 = 0;
    let mut v___x_7817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7819_: u8 = 0;
    let mut v___x_7820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7821_: usize = 0;
    let mut v___x_7822_: usize = 0;
    let mut v___x_1796__overap_7823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7827_: u8 = 0;
    let mut v___x_7829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7831_: u8 = 0;
    let mut v_unused_7832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7836_: u8 = 0;
    let mut v___x_7838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7840_: u8 = 0;
    let mut v___x_7841_: usize = 0;
    let mut v___x_7842_: usize = 0;
    let mut v___x_1805__overap_7843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7847_: u8 = 0;
    let mut v___x_7849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7851_: u8 = 0;
    let mut v_unused_7852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7856_: u8 = 0;
    let mut v___x_7858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7860_: u8 = 0;
    let mut v_a_7861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7863_: u8 = 0;
    let mut v___x_7864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7867_: u8 = 0;
    let mut v___x_7868_: usize = 0;
    let mut v___x_7869_: usize = 0;
    let mut v___x_1826__overap_7870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7875_: u8 = 0;
    let mut v___x_7877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7879_: u8 = 0;
    let mut v___x_7880_: usize = 0;
    let mut v___x_7881_: usize = 0;
    let mut v___x_1834__overap_7882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7887_: u8 = 0;
    let mut v___x_7889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7891_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7810_ = lean_unsigned_to_nat(0);
                v___x_7811_ = l_Lake_Log_empty___closed__0;
                v___x_7812_ = lean_apply_2(v___y_7804_, v___x_7811_, lean_box(0));
                if lean_obj_tag(v___x_7812_) == 0 {
                    lean_dec_ref(v___f_7802_);
                    v_a_7813_ = lean_ctor_get(v___x_7812_, 0);
                    lean_inc(v_a_7813_);
                    v_a_7814_ = lean_ctor_get(v___x_7812_, 1);
                    lean_inc(v_a_7814_);
                    lean_dec_ref_known(v___x_7812_, 2);
                    v___x_7815_ = lean_array_get_size(v_a_7814_);
                    v___x_7816_ = lean_nat_dec_lt(v___x_7810_, v___x_7815_);
                    if v___x_7816_ == 0 {
                        lean_dec(v_a_7814_);
                        lean_dec_ref(v___f_7801_);
                        lean_dec_ref(v___x_7800_);
                        v___x_7817_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_7817_, 0, v_a_7813_);
                        return v___x_7817_;
                    } else {
                        v___x_7818_ = lean_box(0);
                        v___x_7819_ = lean_nat_dec_le(v___x_7815_, v___x_7815_);
                        if v___x_7819_ == 0 {
                            if v___x_7816_ == 0 {
                                lean_dec(v_a_7814_);
                                lean_dec_ref(v___f_7801_);
                                lean_dec_ref(v___x_7800_);
                                v___x_7820_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_7820_, 0, v_a_7813_);
                                return v___x_7820_;
                            } else {
                                v___x_7821_ = 0usize;
                                v___x_7822_ = lean_usize_of_nat(v___x_7815_);
                                v___x_1796__overap_7823_ =
                                    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                        lean_box(0),
                                        lean_box(0),
                                        lean_box(0),
                                        v___x_7800_,
                                        v___f_7801_,
                                        v_a_7814_,
                                        v___x_7821_,
                                        v___x_7822_,
                                        v___x_7818_,
                                    );
                                lean_inc_ref(v___y_7805_);
                                v___x_7824_ = lean_apply_2(
                                    v___x_1796__overap_7823_,
                                    v___y_7805_,
                                    lean_box(0),
                                );
                                if lean_obj_tag(v___x_7824_) == 0 {
                                    v_isSharedCheck_7831_ = (!lean_is_exclusive(v___x_7824_)) as u8;
                                    if v_isSharedCheck_7831_ == 0 {
                                        v_unused_7832_ = lean_ctor_get(v___x_7824_, 0);
                                        lean_dec(v_unused_7832_);
                                        v___x_7826_ = v___x_7824_;
                                        v_isShared_7827_ = v_isSharedCheck_7831_;
                                        state = 2;
                                        continue;
                                    } else {
                                        lean_dec(v___x_7824_);
                                        v___x_7826_ = lean_box(0);
                                        v_isShared_7827_ = v_isSharedCheck_7831_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_a_7813_);
                                    v_a_7833_ = lean_ctor_get(v___x_7824_, 0);
                                    v_isSharedCheck_7840_ = (!lean_is_exclusive(v___x_7824_)) as u8;
                                    if v_isSharedCheck_7840_ == 0 {
                                        v___x_7835_ = v___x_7824_;
                                        v_isShared_7836_ = v_isSharedCheck_7840_;
                                        state = 4;
                                        continue;
                                    } else {
                                        lean_inc(v_a_7833_);
                                        lean_dec(v___x_7824_);
                                        v___x_7835_ = lean_box(0);
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
                                    lean_box(0),
                                    lean_box(0),
                                    lean_box(0),
                                    v___x_7800_,
                                    v___f_7801_,
                                    v_a_7814_,
                                    v___x_7841_,
                                    v___x_7842_,
                                    v___x_7818_,
                                );
                            lean_inc_ref(v___y_7805_);
                            v___x_7844_ =
                                lean_apply_2(v___x_1805__overap_7843_, v___y_7805_, lean_box(0));
                            if lean_obj_tag(v___x_7844_) == 0 {
                                v_isSharedCheck_7851_ = (!lean_is_exclusive(v___x_7844_)) as u8;
                                if v_isSharedCheck_7851_ == 0 {
                                    v_unused_7852_ = lean_ctor_get(v___x_7844_, 0);
                                    lean_dec(v_unused_7852_);
                                    v___x_7846_ = v___x_7844_;
                                    v_isShared_7847_ = v_isSharedCheck_7851_;
                                    state = 6;
                                    continue;
                                } else {
                                    lean_dec(v___x_7844_);
                                    v___x_7846_ = lean_box(0);
                                    v_isShared_7847_ = v_isSharedCheck_7851_;
                                    state = 6;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_7813_);
                                v_a_7853_ = lean_ctor_get(v___x_7844_, 0);
                                v_isSharedCheck_7860_ = (!lean_is_exclusive(v___x_7844_)) as u8;
                                if v_isSharedCheck_7860_ == 0 {
                                    v___x_7855_ = v___x_7844_;
                                    v_isShared_7856_ = v_isSharedCheck_7860_;
                                    state = 8;
                                    continue;
                                } else {
                                    lean_inc(v_a_7853_);
                                    lean_dec(v___x_7844_);
                                    v___x_7855_ = lean_box(0);
                                    v_isShared_7856_ = v_isSharedCheck_7860_;
                                    state = 8;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v___f_7801_);
                    v_a_7861_ = lean_ctor_get(v___x_7812_, 1);
                    lean_inc(v_a_7861_);
                    lean_dec_ref_known(v___x_7812_, 2);
                    v___x_7862_ = lean_array_get_size(v_a_7861_);
                    v___x_7863_ = lean_nat_dec_lt(v___x_7810_, v___x_7862_);
                    if v___x_7863_ == 0 {
                        lean_dec(v_a_7861_);
                        lean_dec_ref(v___f_7802_);
                        lean_dec_ref(v___x_7800_);
                        v___x_7864_ = lean_box(0);
                        v___x_7865_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_7865_, 0, v___x_7864_);
                        return v___x_7865_;
                    } else {
                        v___x_7866_ = lean_box(0);
                        v___x_7867_ = lean_nat_dec_le(v___x_7862_, v___x_7862_);
                        if v___x_7867_ == 0 {
                            if v___x_7863_ == 0 {
                                lean_dec(v_a_7861_);
                                lean_dec_ref(v___f_7802_);
                                lean_dec_ref(v___x_7800_);
                                state = 1;
                                continue;
                            } else {
                                v___x_7868_ = 0usize;
                                v___x_7869_ = lean_usize_of_nat(v___x_7862_);
                                v___x_1826__overap_7870_ =
                                    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                        lean_box(0),
                                        lean_box(0),
                                        lean_box(0),
                                        v___x_7800_,
                                        v___f_7802_,
                                        v_a_7861_,
                                        v___x_7868_,
                                        v___x_7869_,
                                        v___x_7866_,
                                    );
                                lean_inc_ref(v___y_7805_);
                                v___x_7871_ = lean_apply_2(
                                    v___x_1826__overap_7870_,
                                    v___y_7805_,
                                    lean_box(0),
                                );
                                if lean_obj_tag(v___x_7871_) == 0 {
                                    lean_dec_ref_known(v___x_7871_, 1);
                                    state = 1;
                                    continue;
                                } else {
                                    v_a_7872_ = lean_ctor_get(v___x_7871_, 0);
                                    v_isSharedCheck_7879_ = (!lean_is_exclusive(v___x_7871_)) as u8;
                                    if v_isSharedCheck_7879_ == 0 {
                                        v___x_7874_ = v___x_7871_;
                                        v_isShared_7875_ = v_isSharedCheck_7879_;
                                        state = 10;
                                        continue;
                                    } else {
                                        lean_inc(v_a_7872_);
                                        lean_dec(v___x_7871_);
                                        v___x_7874_ = lean_box(0);
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
                                    lean_box(0),
                                    lean_box(0),
                                    lean_box(0),
                                    v___x_7800_,
                                    v___f_7802_,
                                    v_a_7861_,
                                    v___x_7880_,
                                    v___x_7881_,
                                    v___x_7866_,
                                );
                            lean_inc_ref(v___y_7805_);
                            v___x_7883_ =
                                lean_apply_2(v___x_1834__overap_7882_, v___y_7805_, lean_box(0));
                            if lean_obj_tag(v___x_7883_) == 0 {
                                lean_dec_ref_known(v___x_7883_, 1);
                                state = 1;
                                continue;
                            } else {
                                v_a_7884_ = lean_ctor_get(v___x_7883_, 0);
                                v_isSharedCheck_7891_ = (!lean_is_exclusive(v___x_7883_)) as u8;
                                if v_isSharedCheck_7891_ == 0 {
                                    v___x_7886_ = v___x_7883_;
                                    v_isShared_7887_ = v_isSharedCheck_7891_;
                                    state = 12;
                                    continue;
                                } else {
                                    lean_inc(v_a_7884_);
                                    lean_dec(v___x_7883_);
                                    v___x_7886_ = lean_box(0);
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
                v___x_7808_ = lean_box(0);
                v___x_7809_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_7809_, 0, v___x_7808_);
                return v___x_7809_;
            }
            2 => {
                if v_isShared_7827_ == 0 {
                    lean_ctor_set(v___x_7826_, 0, v_a_7813_);
                    v___x_7829_ = v___x_7826_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7830_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7830_, 0, v_a_7813_);
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
                    v_reuseFailAlloc_7839_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7839_, 0, v_a_7833_);
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
                    lean_ctor_set(v___x_7846_, 0, v_a_7813_);
                    v___x_7849_ = v___x_7846_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7850_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7850_, 0, v_a_7813_);
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
                    v_reuseFailAlloc_7859_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7859_, 0, v_a_7853_);
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
                    v_reuseFailAlloc_7878_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7878_, 0, v_a_7872_);
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
                    v_reuseFailAlloc_7890_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7890_, 0, v_a_7884_);
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
    mut v___x_7892_: *mut LeanObject,
    mut v___f_7893_: *mut LeanObject,
    mut v___f_7894_: *mut LeanObject,
    mut v_00_u03b1_7895_: *mut LeanObject,
    mut v___y_7896_: *mut LeanObject,
    mut v___y_7897_: *mut LeanObject,
    mut v___y_7898_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7899_: *mut LeanObject = core::ptr::null_mut();
    v_res_7899_ = l_Lake_LoggerIO_instMonadLiftLogIO___lam__2(
        v___x_7892_,
        v___f_7893_,
        v___f_7894_,
        v_00_u03b1_7895_,
        v___y_7896_,
        v___y_7897_,
    );
    lean_dec_ref(v___y_7897_);
    return v_res_7899_;
}
pub unsafe fn _init_l_Lake_LoggerIO_instMonadLiftLogIO___closed__1() -> *mut LeanObject {
    let mut v___x_7901_: *mut LeanObject = core::ptr::null_mut();
    v___x_7901_ = l_instMonadEIO(lean_box(0));
    return v___x_7901_;
}
pub unsafe fn _init_l_Lake_LoggerIO_instMonadLiftLogIO___closed__2() -> *mut LeanObject {
    let mut v___x_7902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7903_: *mut LeanObject = core::ptr::null_mut();
    v___x_7902_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LoggerIO_instMonadLiftLogIO___closed__1),
        core::ptr::addr_of_mut!(l_Lake_LoggerIO_instMonadLiftLogIO___closed__1_once),
        _init_l_Lake_LoggerIO_instMonadLiftLogIO___closed__1,
    );
    v___x_7903_ = l_ReaderT_instMonad___redArg(v___x_7902_);
    return v___x_7903_;
}
pub unsafe fn _init_l_Lake_LoggerIO_instMonadLiftLogIO___closed__3() -> *mut LeanObject {
    let mut v___f_7904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7906_: *mut LeanObject = core::ptr::null_mut();
    v___f_7904_ = l_Lake_LoggerIO_instMonadLiftLogIO___closed__0;
    v___x_7905_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LoggerIO_instMonadLiftLogIO___closed__2),
        core::ptr::addr_of_mut!(l_Lake_LoggerIO_instMonadLiftLogIO___closed__2_once),
        _init_l_Lake_LoggerIO_instMonadLiftLogIO___closed__2,
    );
    v___f_7906_ = lean_alloc_closure(
        l_Lake_LoggerIO_instMonadLiftLogIO___lam__2___boxed as *mut core::ffi::c_void,
        7,
        3,
    );
    lean_closure_set(v___f_7906_, 0, v___x_7905_);
    lean_closure_set(v___f_7906_, 1, v___f_7904_);
    lean_closure_set(v___f_7906_, 2, v___f_7904_);
    return v___f_7906_;
}
pub unsafe fn _init_l_Lake_LoggerIO_instMonadLiftLogIO() -> *mut LeanObject {
    let mut v___f_7907_: *mut LeanObject = core::ptr::null_mut();
    v___f_7907_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LoggerIO_instMonadLiftLogIO___closed__3),
        core::ptr::addr_of_mut!(l_Lake_LoggerIO_instMonadLiftLogIO___closed__3_once),
        _init_l_Lake_LoggerIO_instMonadLiftLogIO___closed__3,
    );
    return v___f_7907_;
}
pub unsafe fn l_Lake_LoggerIO_toBaseIO___redArg___lam__0(
    mut v_val_7908_: *mut LeanObject,
    mut v_outLv_7909_: u8,
    mut v_val_7910_: u8,
    mut v_e_7911_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7913_: *mut LeanObject = core::ptr::null_mut();
    v___x_7913_ = l_Lake_logToStream(v_e_7911_, v_val_7908_, v_outLv_7909_, v_val_7910_);
    return v___x_7913_;
}
pub unsafe fn l_Lake_LoggerIO_toBaseIO___redArg___lam__0___boxed(
    mut v_val_7914_: *mut LeanObject,
    mut v_outLv_7915_: *mut LeanObject,
    mut v_val_7916_: *mut LeanObject,
    mut v_e_7917_: *mut LeanObject,
    mut v___y_7918_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_outLv_boxed_7919_: u8 = 0;
    let mut v_val_178__boxed_7920_: u8 = 0;
    let mut v_res_7921_: *mut LeanObject = core::ptr::null_mut();
    v_outLv_boxed_7919_ = (lean_unbox(v_outLv_7915_) as u8);
    v_val_178__boxed_7920_ = (lean_unbox(v_val_7916_) as u8);
    v_res_7921_ = l_Lake_LoggerIO_toBaseIO___redArg___lam__0(
        v_val_7914_,
        v_outLv_boxed_7919_,
        v_val_178__boxed_7920_,
        v_e_7917_,
    );
    lean_dec_ref(v_e_7917_);
    return v_res_7921_;
}
pub unsafe fn l_Lake_LoggerIO_toBaseIO___redArg(
    mut v_self_7922_: *mut LeanObject,
    mut v_cfg_7923_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_outLv_7925_: u8 = 0;
    let mut v_ansiMode_7926_: u8 = 0;
    let mut v_out_7927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7929_: u8 = 0;
    let mut v___x_7930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7937_: u8 = 0;
    let mut v___x_7939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7941_: u8 = 0;
    let mut v___x_7942_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_outLv_7925_ = lean_ctor_get_uint8(
                    v_cfg_7923_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                );
                v_ansiMode_7926_ = lean_ctor_get_uint8(
                    v_cfg_7923_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
                );
                v_out_7927_ = lean_ctor_get(v_cfg_7923_, 0);
                v___x_7928_ = l_Lake_OutStream_get(v_out_7927_);
                lean_inc_ref(v___x_7928_);
                v___x_7929_ = l_Lake_AnsiMode_isEnabled(v___x_7928_, v_ansiMode_7926_);
                v___x_7930_ = lean_box((v_outLv_7925_) as usize);
                v___x_7931_ = lean_box((v___x_7929_) as usize);
                v___f_7932_ = lean_alloc_closure(
                    l_Lake_LoggerIO_toBaseIO___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    3,
                );
                lean_closure_set(v___f_7932_, 0, v___x_7928_);
                lean_closure_set(v___f_7932_, 1, v___x_7930_);
                lean_closure_set(v___f_7932_, 2, v___x_7931_);
                v___x_7933_ = lean_apply_2(v_self_7922_, v___f_7932_, lean_box(0));
                if lean_obj_tag(v___x_7933_) == 0 {
                    v_a_7934_ = lean_ctor_get(v___x_7933_, 0);
                    v_isSharedCheck_7941_ = (!lean_is_exclusive(v___x_7933_)) as u8;
                    if v_isSharedCheck_7941_ == 0 {
                        v___x_7936_ = v___x_7933_;
                        v_isShared_7937_ = v_isSharedCheck_7941_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7934_);
                        lean_dec(v___x_7933_);
                        v___x_7936_ = lean_box(0);
                        v_isShared_7937_ = v_isSharedCheck_7941_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v___x_7933_, 1);
                    v___x_7942_ = lean_box(0);
                    return v___x_7942_;
                }
            }
            1 => {
                if v_isShared_7937_ == 0 {
                    lean_ctor_set_tag(v___x_7936_, 1);
                    v___x_7939_ = v___x_7936_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7940_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7940_, 0, v_a_7934_);
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
    mut v_self_7943_: *mut LeanObject,
    mut v_cfg_7944_: *mut LeanObject,
    mut v_a_7945_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7946_: *mut LeanObject = core::ptr::null_mut();
    v_res_7946_ = l_Lake_LoggerIO_toBaseIO___redArg(v_self_7943_, v_cfg_7944_);
    lean_dec_ref(v_cfg_7944_);
    return v_res_7946_;
}
pub unsafe fn l_Lake_LoggerIO_toBaseIO(
    mut v_00_u03b1_7947_: *mut LeanObject,
    mut v_self_7948_: *mut LeanObject,
    mut v_cfg_7949_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_outLv_7951_: u8 = 0;
    let mut v_ansiMode_7952_: u8 = 0;
    let mut v_out_7953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7955_: u8 = 0;
    let mut v___x_7956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7963_: u8 = 0;
    let mut v___x_7965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7967_: u8 = 0;
    let mut v___x_7968_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_outLv_7951_ = lean_ctor_get_uint8(
                    v_cfg_7949_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                );
                v_ansiMode_7952_ = lean_ctor_get_uint8(
                    v_cfg_7949_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
                );
                v_out_7953_ = lean_ctor_get(v_cfg_7949_, 0);
                v___x_7954_ = l_Lake_OutStream_get(v_out_7953_);
                lean_inc_ref(v___x_7954_);
                v___x_7955_ = l_Lake_AnsiMode_isEnabled(v___x_7954_, v_ansiMode_7952_);
                v___x_7956_ = lean_box((v_outLv_7951_) as usize);
                v___x_7957_ = lean_box((v___x_7955_) as usize);
                v___f_7958_ = lean_alloc_closure(
                    l_Lake_LoggerIO_toBaseIO___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    3,
                );
                lean_closure_set(v___f_7958_, 0, v___x_7954_);
                lean_closure_set(v___f_7958_, 1, v___x_7956_);
                lean_closure_set(v___f_7958_, 2, v___x_7957_);
                v___x_7959_ = lean_apply_2(v_self_7948_, v___f_7958_, lean_box(0));
                if lean_obj_tag(v___x_7959_) == 0 {
                    v_a_7960_ = lean_ctor_get(v___x_7959_, 0);
                    v_isSharedCheck_7967_ = (!lean_is_exclusive(v___x_7959_)) as u8;
                    if v_isSharedCheck_7967_ == 0 {
                        v___x_7962_ = v___x_7959_;
                        v_isShared_7963_ = v_isSharedCheck_7967_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7960_);
                        lean_dec(v___x_7959_);
                        v___x_7962_ = lean_box(0);
                        v_isShared_7963_ = v_isSharedCheck_7967_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v___x_7959_, 1);
                    v___x_7968_ = lean_box(0);
                    return v___x_7968_;
                }
            }
            1 => {
                if v_isShared_7963_ == 0 {
                    lean_ctor_set_tag(v___x_7962_, 1);
                    v___x_7965_ = v___x_7962_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7966_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7966_, 0, v_a_7960_);
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
    mut v_00_u03b1_7969_: *mut LeanObject,
    mut v_self_7970_: *mut LeanObject,
    mut v_cfg_7971_: *mut LeanObject,
    mut v_a_7972_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7973_: *mut LeanObject = core::ptr::null_mut();
    v_res_7973_ = l_Lake_LoggerIO_toBaseIO(v_00_u03b1_7969_, v_self_7970_, v_cfg_7971_);
    lean_dec_ref(v_cfg_7971_);
    return v_res_7973_;
}
pub unsafe fn l_Lake_LoggerIO_captureLog___redArg___lam__0(
    mut v_val_7974_: *mut LeanObject,
    mut v_e_7975_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7979_: *mut LeanObject = core::ptr::null_mut();
    v___x_7977_ = lean_st_ref_take(v_val_7974_);
    v___x_7978_ = lean_array_push(v___x_7977_, v_e_7975_);
    v___x_7979_ = lean_st_ref_set(v_val_7974_, v___x_7978_);
    return v___x_7979_;
}
pub unsafe fn l_Lake_LoggerIO_captureLog___redArg___lam__0___boxed(
    mut v_val_7980_: *mut LeanObject,
    mut v_e_7981_: *mut LeanObject,
    mut v___y_7982_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7983_: *mut LeanObject = core::ptr::null_mut();
    v_res_7983_ = l_Lake_LoggerIO_captureLog___redArg___lam__0(v_val_7980_, v_e_7981_);
    lean_dec(v_val_7980_);
    return v_res_7983_;
}
pub unsafe fn l_Lake_LoggerIO_captureLog___redArg(
    mut v_self_7984_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_7987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7999_: u8 = 0;
    let mut v___x_8001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8003_: u8 = 0;
    let mut v___f_8004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8009_: u8 = 0;
    let mut v___x_8011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8013_: u8 = 0;
    let mut v_a_8014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8017_: u8 = 0;
    let mut v___x_8019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8021_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7990_ = l_Lake_Log_empty___closed__0;
                v___x_7991_ = lean_st_mk_ref(v___x_7990_);
                lean_inc(v___x_7991_);
                v___f_8004_ = lean_alloc_closure(
                    l_Lake_LoggerIO_captureLog___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    3,
                    1,
                );
                lean_closure_set(v___f_8004_, 0, v___x_7991_);
                v___x_8005_ = lean_apply_2(v_self_7984_, v___f_8004_, lean_box(0));
                if lean_obj_tag(v___x_8005_) == 0 {
                    v_a_8006_ = lean_ctor_get(v___x_8005_, 0);
                    v_isSharedCheck_8013_ = (!lean_is_exclusive(v___x_8005_)) as u8;
                    if v_isSharedCheck_8013_ == 0 {
                        v___x_8008_ = v___x_8005_;
                        v_isShared_8009_ = v_isSharedCheck_8013_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_8006_);
                        lean_dec(v___x_8005_);
                        v___x_8008_ = lean_box(0);
                        v_isShared_8009_ = v_isSharedCheck_8013_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_a_8014_ = lean_ctor_get(v___x_8005_, 0);
                    v_isSharedCheck_8021_ = (!lean_is_exclusive(v___x_8005_)) as u8;
                    if v_isSharedCheck_8021_ == 0 {
                        v___x_8016_ = v___x_8005_;
                        v_isShared_8017_ = v_isSharedCheck_8021_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_8014_);
                        lean_dec(v___x_8005_);
                        v___x_8016_ = lean_box(0);
                        v_isShared_8017_ = v_isSharedCheck_8021_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7989_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_7989_, 0, v___y_7988_);
                lean_ctor_set(v___x_7989_, 1, v___y_7987_);
                return v___x_7989_;
            }
            2 => {
                v___x_7994_ = lean_st_ref_get(v___x_7991_);
                lean_dec(v___x_7991_);
                if lean_obj_tag(v_val_7993_) == 0 {
                    lean_dec_ref_known(v_val_7993_, 1);
                    v___x_7995_ = lean_box(0);
                    v___y_7987_ = v___x_7994_;
                    v___y_7988_ = v___x_7995_;
                    state = 1;
                    continue;
                } else {
                    v_a_7996_ = lean_ctor_get(v_val_7993_, 0);
                    v_isSharedCheck_8003_ = (!lean_is_exclusive(v_val_7993_)) as u8;
                    if v_isSharedCheck_8003_ == 0 {
                        v___x_7998_ = v_val_7993_;
                        v_isShared_7999_ = v_isSharedCheck_8003_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_7996_);
                        lean_dec(v_val_7993_);
                        v___x_7998_ = lean_box(0);
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
                    v_reuseFailAlloc_8002_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8002_, 0, v_a_7996_);
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
                    lean_ctor_set_tag(v___x_8008_, 1);
                    v___x_8011_ = v___x_8008_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_8012_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8012_, 0, v_a_8006_);
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
                    lean_ctor_set_tag(v___x_8016_, 0);
                    v___x_8019_ = v___x_8016_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_8020_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8020_, 0, v_a_8014_);
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
    mut v_self_8022_: *mut LeanObject,
    mut v_a_8023_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8024_: *mut LeanObject = core::ptr::null_mut();
    v_res_8024_ = l_Lake_LoggerIO_captureLog___redArg(v_self_8022_);
    return v_res_8024_;
}
pub unsafe fn l_Lake_LoggerIO_captureLog(
    mut v_00_u03b1_8025_: *mut LeanObject,
    mut v_self_8026_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8028_: *mut LeanObject = core::ptr::null_mut();
    v___x_8028_ = l_Lake_LoggerIO_captureLog___redArg(v_self_8026_);
    return v___x_8028_;
}
pub unsafe fn l_Lake_LoggerIO_captureLog___boxed(
    mut v_00_u03b1_8029_: *mut LeanObject,
    mut v_self_8030_: *mut LeanObject,
    mut v_a_8031_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8032_: *mut LeanObject = core::ptr::null_mut();
    v_res_8032_ = l_Lake_LoggerIO_captureLog(v_00_u03b1_8029_, v_self_8030_);
    return v_res_8032_;
}
pub unsafe fn l_Lake_LoggerIO_run_x3f___redArg(
    mut v_self_8033_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8035_: *mut LeanObject = core::ptr::null_mut();
    v___x_8035_ = l_Lake_LoggerIO_captureLog___redArg(v_self_8033_);
    return v___x_8035_;
}
pub unsafe fn l_Lake_LoggerIO_run_x3f___redArg___boxed(
    mut v_self_8036_: *mut LeanObject,
    mut v_a_8037_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8038_: *mut LeanObject = core::ptr::null_mut();
    v_res_8038_ = l_Lake_LoggerIO_run_x3f___redArg(v_self_8036_);
    return v_res_8038_;
}
pub unsafe fn l_Lake_LoggerIO_run_x3f(
    mut v_00_u03b1_8039_: *mut LeanObject,
    mut v_self_8040_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8042_: *mut LeanObject = core::ptr::null_mut();
    v___x_8042_ = l_Lake_LoggerIO_captureLog___redArg(v_self_8040_);
    return v___x_8042_;
}
pub unsafe fn l_Lake_LoggerIO_run_x3f___boxed(
    mut v_00_u03b1_8043_: *mut LeanObject,
    mut v_self_8044_: *mut LeanObject,
    mut v_a_8045_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8046_: *mut LeanObject = core::ptr::null_mut();
    v_res_8046_ = l_Lake_LoggerIO_run_x3f(v_00_u03b1_8043_, v_self_8044_);
    return v_res_8046_;
}
pub unsafe fn l_Lake_LoggerIO_run_x3f_x27___redArg(
    mut v_self_8047_: *mut LeanObject,
    mut v_logger_8048_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8054_: u8 = 0;
    let mut v___x_8056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8058_: u8 = 0;
    let mut v___x_8059_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8050_ = lean_apply_2(v_self_8047_, v_logger_8048_, lean_box(0));
                if lean_obj_tag(v___x_8050_) == 0 {
                    v_a_8051_ = lean_ctor_get(v___x_8050_, 0);
                    v_isSharedCheck_8058_ = (!lean_is_exclusive(v___x_8050_)) as u8;
                    if v_isSharedCheck_8058_ == 0 {
                        v___x_8053_ = v___x_8050_;
                        v_isShared_8054_ = v_isSharedCheck_8058_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_8051_);
                        lean_dec(v___x_8050_);
                        v___x_8053_ = lean_box(0);
                        v_isShared_8054_ = v_isSharedCheck_8058_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v___x_8050_, 1);
                    v___x_8059_ = lean_box(0);
                    return v___x_8059_;
                }
            }
            1 => {
                if v_isShared_8054_ == 0 {
                    lean_ctor_set_tag(v___x_8053_, 1);
                    v___x_8056_ = v___x_8053_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8057_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8057_, 0, v_a_8051_);
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
    mut v_self_8060_: *mut LeanObject,
    mut v_logger_8061_: *mut LeanObject,
    mut v_a_8062_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8063_: *mut LeanObject = core::ptr::null_mut();
    v_res_8063_ = l_Lake_LoggerIO_run_x3f_x27___redArg(v_self_8060_, v_logger_8061_);
    return v_res_8063_;
}
pub unsafe fn l_Lake_LoggerIO_run_x3f_x27(
    mut v_00_u03b1_8064_: *mut LeanObject,
    mut v_self_8065_: *mut LeanObject,
    mut v_logger_8066_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8072_: u8 = 0;
    let mut v___x_8074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8076_: u8 = 0;
    let mut v___x_8077_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8068_ = lean_apply_2(v_self_8065_, v_logger_8066_, lean_box(0));
                if lean_obj_tag(v___x_8068_) == 0 {
                    v_a_8069_ = lean_ctor_get(v___x_8068_, 0);
                    v_isSharedCheck_8076_ = (!lean_is_exclusive(v___x_8068_)) as u8;
                    if v_isSharedCheck_8076_ == 0 {
                        v___x_8071_ = v___x_8068_;
                        v_isShared_8072_ = v_isSharedCheck_8076_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_8069_);
                        lean_dec(v___x_8068_);
                        v___x_8071_ = lean_box(0);
                        v_isShared_8072_ = v_isSharedCheck_8076_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v___x_8068_, 1);
                    v___x_8077_ = lean_box(0);
                    return v___x_8077_;
                }
            }
            1 => {
                if v_isShared_8072_ == 0 {
                    lean_ctor_set_tag(v___x_8071_, 1);
                    v___x_8074_ = v___x_8071_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8075_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8075_, 0, v_a_8069_);
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
    mut v_00_u03b1_8078_: *mut LeanObject,
    mut v_self_8079_: *mut LeanObject,
    mut v_logger_8080_: *mut LeanObject,
    mut v_a_8081_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8082_: *mut LeanObject = core::ptr::null_mut();
    v_res_8082_ = l_Lake_LoggerIO_run_x3f_x27(v_00_u03b1_8078_, v_self_8079_, v_logger_8080_);
    return v_res_8082_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Util_Log(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_Json(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Error(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_EStateT(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Message(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Lift(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Modify(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lake_instLTVerbosity = _init_l_Lake_instLTVerbosity();
    lean_mark_persistent(l_Lake_instLTVerbosity);
    l_Lake_instLEVerbosity = _init_l_Lake_instLEVerbosity();
    lean_mark_persistent(l_Lake_instLEVerbosity);
    l_Lake_instInhabitedVerbosity = _init_l_Lake_instInhabitedVerbosity();
    l_Lake_instInhabitedLogLevel_default = _init_l_Lake_instInhabitedLogLevel_default();
    l_Lake_instInhabitedLogLevel = _init_l_Lake_instInhabitedLogLevel();
    l_Lake_instLTLogLevel = _init_l_Lake_instLTLogLevel();
    lean_mark_persistent(l_Lake_instLTLogLevel);
    l_Lake_instLELogLevel = _init_l_Lake_instLELogLevel();
    lean_mark_persistent(l_Lake_instLELogLevel);
    l_Lake_Log_instInhabitedPos_default = _init_l_Lake_Log_instInhabitedPos_default();
    lean_mark_persistent(l_Lake_Log_instInhabitedPos_default);
    l_Lake_Log_instInhabitedPos = _init_l_Lake_Log_instInhabitedPos();
    lean_mark_persistent(l_Lake_Log_instInhabitedPos);
    l_Lake_instOfNatPos = _init_l_Lake_instOfNatPos();
    lean_mark_persistent(l_Lake_instOfNatPos);
    l_Lake_instLTPos = _init_l_Lake_instLTPos();
    lean_mark_persistent(l_Lake_instLTPos);
    l_Lake_instLEPos = _init_l_Lake_instLEPos();
    lean_mark_persistent(l_Lake_instLEPos);
    l_Lake_LoggerIO_instMonadLiftLogIO = _init_l_Lake_LoggerIO_instMonadLiftLogIO();
    lean_mark_persistent(l_Lake_LoggerIO_instMonadLiftLogIO);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Util_Log(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Util_Log(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_Json(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_Error(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_EStateT(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Message(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_Lift(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Modify(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Log(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Util_Log(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Util_Log(builtin);
}
