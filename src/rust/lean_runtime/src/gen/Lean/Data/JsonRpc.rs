// Lean compiler output
// Module: Lean.Data.JsonRpc
// Imports: Lean.Data.Json.Stream Lean.Data.Json.FromToJson.Basic
use crate::r#gen::Init::Data::List::Basic::l_List_appendTR___redArg;
use crate::r#gen::Init::Data::Option::Basic::l_Option_instBEq_beq___redArg;
use crate::r#gen::Init::Prelude::l_id___boxed;
use crate::r#gen::Init::System::IOError::lean_mk_io_user_error;
use crate::r#gen::Lean::Data::Json::Basic::{
    l_Lean_Json_getObjVal_x3f, l_Lean_Json_getObjValD, l_Lean_Json_getStr_x3f, l_Lean_Json_mkObj,
    l_Lean_JsonNumber_fromInt, l_Lean_JsonNumber_fromNat, l_Lean_JsonNumber_lt,
    l_Lean_JsonNumber_toString, l_Lean_instDecidableEqJsonNumber_decEq,
    l_Lean_instHashableJsonNumber_hash,
};
use crate::r#gen::Lean::Data::Json::FromToJson::Basic::{
    initialize_Lean_Data_Json_FromToJson_Basic, l_Lean_Json_Structured_fromJson_x3f,
    l_Lean_Json_Structured_toJson, l_Lean_Json_getObjValAs_x3f___redArg, l_Lean_Json_getTag_x3f,
    l_Lean_Json_opt___redArg, l_Lean_Json_toStructured_x3f___redArg, l_Option_toJson___redArg,
    runtime_initialize_Lean_Data_Json_FromToJson_Basic,
};
use crate::r#gen::Lean::Data::Json::Parser::{
    l_Lean_Json_Parser_num, l_Lean_Json_Parser_strCore, l_Lean_Json_parse,
};
use crate::r#gen::Lean::Data::Json::Printer::l_Lean_Json_compress;
use crate::r#gen::Lean::Data::Json::Stream::{
    initialize_Lean_Data_Json_Stream, l_IO_FS_Stream_readJson, l_IO_FS_Stream_writeJson,
    runtime_initialize_Lean_Data_Json_Stream,
};
use crate::r#gen::Std::Internal::Parsec::String::{
    l_Std_Internal_Parsec_String_Parser_run___redArg, l_Std_Internal_Parsec_String_pstring,
};
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_dec_eq, lean_int_neg, lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Data::Ord::String::lean_string_compare;
use crate::lean_imports_rs::Init::Data::String::Basic::{
    lean_string_dec_lt, lean_string_utf8_get_fast, lean_string_utf8_next_fast,
};
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Prelude::{
    lean_nat_dec_eq, lean_string_dec_eq, lean_string_hash, lean_string_utf8_byte_size,
    lean_uint32_dec_eq, lean_uint64_mix_hash,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_box, lean_box_uint64, lean_closure_set,
    lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n,
    lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
pub static l_Lean_JsonRpc_instInhabitedRequestID_default___closed__0_value: LeanStringObject<1> =
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
static mut l_Lean_JsonRpc_instInhabitedRequestID_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instInhabitedRequestID_default___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instInhabitedRequestID_default___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_JsonRpc_instInhabitedRequestID_default___closed__0_value
        ) as *mut LeanObject],
    };
static mut l_Lean_JsonRpc_instInhabitedRequestID_default___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instInhabitedRequestID_default___closed__1_value)
        as *mut LeanObject;
pub static mut l_Lean_JsonRpc_instInhabitedRequestID_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instInhabitedRequestID_default___closed__1_value)
        as *mut LeanObject;
pub static mut l_Lean_JsonRpc_instInhabitedRequestID: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instInhabitedRequestID_default___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instBEqRequestID___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_JsonRpc_instBEqRequestID_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_JsonRpc_instBEqRequestID___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instBEqRequestID___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_JsonRpc_instBEqRequestID: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instBEqRequestID___closed__0_value) as *mut LeanObject;
pub static l_Lean_JsonRpc_instHashableRequestID___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_JsonRpc_instHashableRequestID_hash___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_JsonRpc_instHashableRequestID___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instHashableRequestID___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_JsonRpc_instHashableRequestID: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instHashableRequestID___closed__0_value) as *mut LeanObject;
pub static l_Lean_JsonRpc_instOrdRequestID___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_JsonRpc_instOrdRequestID_ord___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_JsonRpc_instOrdRequestID___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instOrdRequestID___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_JsonRpc_instOrdRequestID: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instOrdRequestID___closed__0_value) as *mut LeanObject;
pub static l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__0_value: LeanStringObject<2> =
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
        m_data: [34, 0],
    };
static mut l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__1_value: LeanStringObject<5> =
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
        m_data: [110, 117, 108, 108, 0],
    };
static mut l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instToStringRequestID___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_JsonRpc_instToStringRequestID___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_JsonRpc_instToStringRequestID___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instToStringRequestID___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_JsonRpc_instToStringRequestID: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instToStringRequestID___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_JsonRpc_instInhabitedErrorCode_default: u8 = 0;
pub static mut l_Lean_JsonRpc_instInhabitedErrorCode: u8 = 0;
pub static l_Lean_JsonRpc_instBEqErrorCode___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_JsonRpc_instBEqErrorCode_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_JsonRpc_instBEqErrorCode___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instBEqErrorCode___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_JsonRpc_instBEqErrorCode: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instBEqErrorCode___closed__0_value) as *mut LeanObject;
pub static l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__0_value: LeanStringObject<20> =
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
            101, 120, 112, 101, 99, 116, 101, 100, 32, 101, 114, 114, 111, 114, 32, 99, 111, 100,
            101, 0,
        ],
    };
static mut l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__0_value
        ) as *mut LeanObject],
    };
static mut l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__6: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__8_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__8: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__10_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__10: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__12_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__12: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__14_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__14: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__16_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__16: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__18_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__18: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__20_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__20: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__22_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__22: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__24_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__24: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__26_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((11 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__26: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__26_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__27_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((10 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__27: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__27_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__28_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((9 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__28: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__28_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__29_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((8 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__29: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__29_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__30_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((7 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__30: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__30_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__31_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((6 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__31: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__31_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__32_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((5 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__32: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__32_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__33_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((4 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__33: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__33_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__34_value: LeanCtorObject<1> =
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
static mut l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__34: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__34_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__35_value: LeanCtorObject<1> =
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
static mut l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__35: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__35_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__36_value: LeanCtorObject<1> =
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
static mut l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__36: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__36_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__37_value: LeanCtorObject<1> =
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
static mut l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__37: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__37_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instFromJsonErrorCode___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_JsonRpc_instFromJsonErrorCode___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instFromJsonErrorCode___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_JsonRpc_instFromJsonErrorCode: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instFromJsonErrorCode___closed__0_value) as *mut LeanObject;
static mut l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__6: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__8_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__8: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__10_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__10: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__12_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__12: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__14_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__14: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__16_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__16: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__18_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__18: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__20_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__20: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__22_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__22: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_JsonRpc_instToJsonErrorCode___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_JsonRpc_instToJsonErrorCode___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_JsonRpc_instToJsonErrorCode___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instToJsonErrorCode___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_JsonRpc_instToJsonErrorCode: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instToJsonErrorCode___closed__0_value) as *mut LeanObject;
pub static l_Lean_JsonRpc_instInhabitedMessage_default___closed__0_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_JsonRpc_instInhabitedRequestID_default___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_JsonRpc_instInhabitedRequestID_default___closed__0_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_JsonRpc_instInhabitedMessage_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instInhabitedMessage_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_JsonRpc_instInhabitedMessage_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instInhabitedMessage_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_JsonRpc_instInhabitedMessage: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instInhabitedMessage_default___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instInhabitedResponseError_default___closed__0_value: LeanCtorObject<4> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 8) as u16,
            other: 3,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_JsonRpc_instInhabitedRequestID_default___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_JsonRpc_instInhabitedRequestID_default___closed__0_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_JsonRpc_instInhabitedResponseError_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instInhabitedResponseError_default___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_JsonRpc_instInhabitedResponseError___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_JsonRpc_instInhabitedResponseError___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_JsonRpc_instCoeOutResponseErrorUnitMessage___closed__0_value: LeanClosureObject<
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
    m_fun: l_Lean_JsonRpc_instCoeOutResponseErrorUnitMessage___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_JsonRpc_instCoeOutResponseErrorUnitMessage___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instCoeOutResponseErrorUnitMessage___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_JsonRpc_instCoeOutResponseErrorUnitMessage: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instCoeOutResponseErrorUnitMessage___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instCoeStringRequestID___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_JsonRpc_instCoeStringRequestID___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_JsonRpc_instCoeStringRequestID___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instCoeStringRequestID___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_JsonRpc_instCoeStringRequestID: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instCoeStringRequestID___closed__0_value) as *mut LeanObject;
pub static l_Lean_JsonRpc_instCoeJsonNumberRequestID___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_JsonRpc_instCoeJsonNumberRequestID___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_JsonRpc_instCoeJsonNumberRequestID___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instCoeJsonNumberRequestID___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_JsonRpc_instCoeJsonNumberRequestID: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instCoeJsonNumberRequestID___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_JsonRpc_RequestID_ltProp: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_JsonRpc_instLTRequestID: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_JsonRpc_instFromJsonRequestID___lam__0___closed__0_value: LeanStringObject<46> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 46,
        m_capacity: 46,
        m_length: 45,
        m_data: [
            97, 32, 114, 101, 113, 117, 101, 115, 116, 32, 105, 100, 32, 110, 101, 101, 100, 115,
            32, 116, 111, 32, 98, 101, 32, 97, 32, 110, 117, 109, 98, 101, 114, 32, 111, 114, 32,
            97, 32, 115, 116, 114, 105, 110, 103, 0,
        ],
    };
static mut l_Lean_JsonRpc_instFromJsonRequestID___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instFromJsonRequestID___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instFromJsonRequestID___lam__0___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_JsonRpc_instFromJsonRequestID___lam__0___closed__0_value
        ) as *mut LeanObject],
    };
static mut l_Lean_JsonRpc_instFromJsonRequestID___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instFromJsonRequestID___lam__0___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instFromJsonRequestID___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_JsonRpc_instFromJsonRequestID___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_JsonRpc_instFromJsonRequestID___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instFromJsonRequestID___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_JsonRpc_instFromJsonRequestID: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instFromJsonRequestID___closed__0_value) as *mut LeanObject;
pub static l_Lean_JsonRpc_instToJsonRequestID___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_JsonRpc_instToJsonRequestID___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_JsonRpc_instToJsonRequestID___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instToJsonRequestID___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_JsonRpc_instToJsonRequestID: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instToJsonRequestID___closed__0_value) as *mut LeanObject;
pub static l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__0_value: LeanStringObject<8> =
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
        m_data: [106, 115, 111, 110, 114, 112, 99, 0],
    };
static mut l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__1_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [50, 46, 48, 0],
    };
static mut l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__2_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4_value: LeanStringObject<3> =
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
        m_data: [105, 100, 0],
    };
static mut l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [109, 101, 116, 104, 111, 100, 0],
    };
static mut l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [112, 97, 114, 97, 109, 115, 0],
    };
static mut l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [114, 101, 115, 117, 108, 116, 0],
    };
static mut l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8_value: LeanStringObject<8> =
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
static mut l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9_value: LeanStringObject<5> =
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
        m_data: [100, 97, 116, 97, 0],
    };
static mut l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10_value: LeanStringObject<6> =
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
static mut l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11_value: LeanStringObject<5> =
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
        m_data: [99, 111, 100, 101, 0],
    };
static mut l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instToJsonMessage___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Json_Structured_toJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_JsonRpc_instToJsonMessage___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instToJsonMessage___closed__0_value) as *mut LeanObject;
pub static l_Lean_JsonRpc_instToJsonMessage___closed__1_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_id___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lean_JsonRpc_instToJsonMessage___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instToJsonMessage___closed__1_value) as *mut LeanObject;
pub static l_Lean_JsonRpc_instToJsonMessage___closed__2_value: LeanClosureObject<2> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_JsonRpc_instToJsonMessage___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 2,
        m_objs: [
            core::ptr::addr_of!(l_Lean_JsonRpc_instToJsonMessage___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_JsonRpc_instToJsonMessage___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_JsonRpc_instToJsonMessage___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instToJsonMessage___closed__2_value) as *mut LeanObject;
pub static mut l_Lean_JsonRpc_instToJsonMessage: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instToJsonMessage___closed__2_value) as *mut LeanObject;
pub static l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__0_value: LeanStringObject<42> =
    LeanStringObject {
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
            111, 110, 108, 121, 32, 118, 101, 114, 115, 105, 111, 110, 32, 50, 46, 48, 32, 111,
            102, 32, 74, 83, 79, 78, 32, 82, 80, 67, 32, 105, 115, 32, 115, 117, 112, 112, 111,
            114, 116, 101, 100, 0,
        ],
    };
static mut l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__1_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instFromJsonMessage___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Json_getStr_x3f as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_JsonRpc_instFromJsonMessage___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instFromJsonMessage___closed__0_value) as *mut LeanObject;
pub static l_Lean_JsonRpc_instFromJsonMessage___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Json_Structured_fromJson_x3f as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_JsonRpc_instFromJsonMessage___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instFromJsonMessage___closed__1_value) as *mut LeanObject;
pub static l_Lean_JsonRpc_instFromJsonMessage___closed__2_value: LeanClosureObject<4> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 4) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_JsonRpc_instFromJsonMessage___lam__0 as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 4,
        m_objs: [
            core::ptr::addr_of!(l_Lean_JsonRpc_instFromJsonRequestID___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_JsonRpc_instFromJsonErrorCode___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_JsonRpc_instFromJsonMessage___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_JsonRpc_instFromJsonMessage___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_JsonRpc_instFromJsonMessage___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instFromJsonMessage___closed__2_value) as *mut LeanObject;
pub static mut l_Lean_JsonRpc_instFromJsonMessage: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instFromJsonMessage___closed__2_value) as *mut LeanObject;
pub static l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0___closed__0_value:
    LeanStringObject<19> = LeanStringObject {
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
        110, 111, 116, 32, 97, 32, 110, 111, 116, 105, 102, 105, 99, 97, 116, 105, 111, 110, 0,
    ],
};
static mut l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0___closed__1_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0___closed__2_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__0_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instInhabitedMessageMetaData_default___closed__0_value: LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_JsonRpc_instInhabitedRequestID_default___closed__1_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_JsonRpc_instInhabitedRequestID_default___closed__0_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_JsonRpc_instInhabitedMessageMetaData_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instInhabitedMessageMetaData_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_JsonRpc_instInhabitedMessageMetaData_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instInhabitedMessageMetaData_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_JsonRpc_instInhabitedMessageMetaData: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instInhabitedMessageMetaData_default___closed__0_value)
        as *mut LeanObject;
pub static l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr___closed__0_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [101, 120, 112, 101, 99, 116, 101, 100, 32, 34, 0]};
static mut l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr___closed__0_value) as *mut LeanObject] };
static mut l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__0_value:
    LeanStringObject<37> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 37,
    m_capacity: 37,
    m_length: 36,
    m_data: [
        101, 120, 112, 101, 99, 116, 101, 100, 32, 114, 101, 115, 112, 111, 110, 115, 101, 32, 101,
        114, 114, 111, 114, 32, 109, 101, 115, 115, 97, 103, 101, 32, 107, 105, 110, 100, 0,
    ],
};
static mut l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__1_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__0_value
    ) as *mut LeanObject],
};
static mut l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__1_value
) as *mut LeanObject;
pub static l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__2_value:
    LeanStringObject<42> = LeanStringObject {
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
        101, 120, 112, 101, 99, 116, 101, 100, 32, 96, 105, 100, 96, 44, 32, 96, 106, 115, 111,
        110, 114, 112, 99, 96, 32, 111, 114, 32, 96, 101, 114, 114, 111, 114, 96, 32, 102, 105,
        101, 108, 100, 0,
    ],
};
static mut l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__2_value
) as *mut LeanObject;
pub static l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__3_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__2_value
    ) as *mut LeanObject],
};
static mut l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__3_value
) as *mut LeanObject;
pub static l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__4_value:
    LeanStringObject<36> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 36,
    m_capacity: 36,
    m_length: 35,
    m_data: [
        101, 120, 112, 101, 99, 116, 101, 100, 32, 96, 109, 101, 116, 104, 111, 100, 96, 32, 111,
        114, 32, 96, 114, 101, 115, 117, 108, 116, 96, 32, 102, 105, 101, 108, 100, 0,
    ],
};
static mut l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__4_value
) as *mut LeanObject;
pub static l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__5_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__4_value
    ) as *mut LeanObject],
};
static mut l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__5_value
) as *mut LeanObject;
pub static mut l_Lean_JsonRpc_instInhabitedMessageDirection_default: u8 = 0;
pub static mut l_Lean_JsonRpc_instInhabitedMessageDirection: u8 = 0;
pub static l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__0_value:
    LeanStringObject<23> = LeanStringObject {
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
        110, 111, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 116, 97, 103, 32, 102, 111,
        117, 110, 100, 0,
    ],
};
static mut l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__1_value: LeanCtorObject<
    1,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__2_value:
    LeanStringObject<15> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        115, 101, 114, 118, 101, 114, 84, 111, 67, 108, 105, 101, 110, 116, 0,
    ],
};
static mut l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__3_value:
    LeanStringObject<15> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        99, 108, 105, 101, 110, 116, 84, 111, 83, 101, 114, 118, 101, 114, 0,
    ],
};
static mut l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__4_value:
    LeanStringObject<33> = LeanStringObject {
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
        110, 111, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 99, 111, 110, 115, 116, 114,
        117, 99, 116, 111, 114, 32, 109, 97, 116, 99, 104, 101, 100, 0,
    ],
};
static mut l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__5_value: LeanCtorObject<
    1,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__4_value
    ) as *mut LeanObject],
};
static mut l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__6_value: LeanCtorObject<
    1,
> = LeanCtorObject {
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
static mut l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__7_value: LeanCtorObject<
    1,
> = LeanCtorObject {
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
static mut l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instFromJsonMessageDirection___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_JsonRpc_instFromJsonMessageDirection___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instFromJsonMessageDirection___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_JsonRpc_instFromJsonMessageDirection: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instFromJsonMessageDirection___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instToJsonMessageDirection_toJson___closed__0_value: LeanCtorObject<1> =
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
            l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__3_value
        ) as *mut LeanObject],
    };
static mut l_Lean_JsonRpc_instToJsonMessageDirection_toJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instToJsonMessageDirection_toJson___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instToJsonMessageDirection_toJson___closed__1_value: LeanCtorObject<1> =
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
            l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__2_value
        ) as *mut LeanObject],
    };
static mut l_Lean_JsonRpc_instToJsonMessageDirection_toJson___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instToJsonMessageDirection_toJson___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instToJsonMessageDirection___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_JsonRpc_instToJsonMessageDirection_toJson___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_JsonRpc_instToJsonMessageDirection___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instToJsonMessageDirection___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_JsonRpc_instToJsonMessageDirection: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instToJsonMessageDirection___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__0_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__0_value
        ) as *mut LeanObject],
    };
static mut l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__1_value: LeanStringObject<14> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [
            114, 101, 115, 112, 111, 110, 115, 101, 69, 114, 114, 111, 114, 0,
        ],
    };
static mut l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__2_value: LeanStringObject<8> =
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
        m_data: [114, 101, 113, 117, 101, 115, 116, 0],
    };
static mut l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__3_value: LeanStringObject<13> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [110, 111, 116, 105, 102, 105, 99, 97, 116, 105, 111, 110, 0],
    };
static mut l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__4_value: LeanStringObject<9> =
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
        m_data: [114, 101, 115, 112, 111, 110, 115, 101, 0],
    };
static mut l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__5_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__4_value
        ) as *mut LeanObject],
    };
static mut l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__6_value: LeanCtorObject<1> =
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
static mut l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__7_value: LeanCtorObject<1> =
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
static mut l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__8_value: LeanCtorObject<1> =
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
static mut l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__9_value: LeanCtorObject<1> =
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
static mut l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instFromJsonMessageKind___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_JsonRpc_instFromJsonMessageKind_fromJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_JsonRpc_instFromJsonMessageKind___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instFromJsonMessageKind___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_JsonRpc_instFromJsonMessageKind: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instFromJsonMessageKind___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__0_value: LeanCtorObject<1> =
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
            l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__2_value
        ) as *mut LeanObject],
    };
static mut l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__1_value: LeanCtorObject<1> =
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
            l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__3_value
        ) as *mut LeanObject],
    };
static mut l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__2_value: LeanCtorObject<1> =
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
            l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__4_value
        ) as *mut LeanObject],
    };
static mut l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__3_value: LeanCtorObject<1> =
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
            l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__1_value
        ) as *mut LeanObject],
    };
static mut l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_JsonRpc_instToJsonMessageKind___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_JsonRpc_instToJsonMessageKind_toJson___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_JsonRpc_instToJsonMessageKind___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instToJsonMessageKind___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_JsonRpc_instToJsonMessageKind: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonRpc_instToJsonMessageKind___closed__0_value) as *mut LeanObject;
pub static l_IO_FS_Stream_readMessage___closed__0_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [74, 83, 79, 78, 32, 39, 0],
};
static mut l_IO_FS_Stream_readMessage___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_Stream_readMessage___closed__0_value) as *mut LeanObject;
pub static l_IO_FS_Stream_readMessage___closed__1_value: LeanStringObject<50> = LeanStringObject {
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
        39, 32, 100, 105, 100, 32, 110, 111, 116, 32, 104, 97, 118, 101, 32, 116, 104, 101, 32,
        102, 111, 114, 109, 97, 116, 32, 111, 102, 32, 97, 32, 74, 83, 79, 78, 45, 82, 80, 67, 32,
        109, 101, 115, 115, 97, 103, 101, 46, 10, 0,
    ],
};
static mut l_IO_FS_Stream_readMessage___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_Stream_readMessage___closed__1_value) as *mut LeanObject;
pub static l_IO_FS_Stream_readRequestAs___redArg___closed__0_value: LeanStringObject<18> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 18,
        m_capacity: 18,
        m_length: 17,
        m_data: [
            69, 120, 112, 101, 99, 116, 101, 100, 32, 109, 101, 116, 104, 111, 100, 32, 39, 0,
        ],
    };
static mut l_IO_FS_Stream_readRequestAs___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_Stream_readRequestAs___redArg___closed__0_value) as *mut LeanObject;
pub static l_IO_FS_Stream_readRequestAs___redArg___closed__1_value: LeanStringObject<16> =
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
            39, 44, 32, 103, 111, 116, 32, 109, 101, 116, 104, 111, 100, 32, 39, 0,
        ],
    };
static mut l_IO_FS_Stream_readRequestAs___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_Stream_readRequestAs___redArg___closed__1_value) as *mut LeanObject;
pub static l_IO_FS_Stream_readRequestAs___redArg___closed__2_value: LeanStringObject<2> =
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
        m_data: [39, 0],
    };
static mut l_IO_FS_Stream_readRequestAs___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_Stream_readRequestAs___redArg___closed__2_value) as *mut LeanObject;
pub static l_IO_FS_Stream_readRequestAs___redArg___closed__3_value: LeanStringObject<19> =
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
            85, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 112, 97, 114, 97, 109, 32, 39, 0,
        ],
    };
static mut l_IO_FS_Stream_readRequestAs___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_Stream_readRequestAs___redArg___closed__3_value) as *mut LeanObject;
pub static l_IO_FS_Stream_readRequestAs___redArg___closed__4_value: LeanStringObject<15> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 14,
        m_data: [
            39, 32, 102, 111, 114, 32, 109, 101, 116, 104, 111, 100, 32, 39, 0,
        ],
    };
static mut l_IO_FS_Stream_readRequestAs___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_Stream_readRequestAs___redArg___closed__4_value) as *mut LeanObject;
pub static l_IO_FS_Stream_readRequestAs___redArg___closed__5_value: LeanStringObject<3> =
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
        m_data: [39, 10, 0],
    };
static mut l_IO_FS_Stream_readRequestAs___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_Stream_readRequestAs___redArg___closed__5_value) as *mut LeanObject;
pub static l_IO_FS_Stream_readRequestAs___redArg___closed__6_value: LeanStringObject<34> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 34,
        m_capacity: 34,
        m_length: 33,
        m_data: [
            69, 120, 112, 101, 99, 116, 101, 100, 32, 74, 83, 79, 78, 45, 82, 80, 67, 32, 114, 101,
            113, 117, 101, 115, 116, 44, 32, 103, 111, 116, 58, 32, 39, 0,
        ],
    };
static mut l_IO_FS_Stream_readRequestAs___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_Stream_readRequestAs___redArg___closed__6_value) as *mut LeanObject;
pub static l_IO_FS_Stream_readNotificationAs___redArg___closed__0_value: LeanStringObject<39> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 39,
        m_capacity: 39,
        m_length: 38,
        m_data: [
            69, 120, 112, 101, 99, 116, 101, 100, 32, 74, 83, 79, 78, 45, 82, 80, 67, 32, 110, 111,
            116, 105, 102, 105, 99, 97, 116, 105, 111, 110, 44, 32, 103, 111, 116, 58, 32, 39, 0,
        ],
    };
static mut l_IO_FS_Stream_readNotificationAs___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_Stream_readNotificationAs___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_IO_FS_Stream_readResponseAs___redArg___closed__0_value: LeanStringObject<13> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [69, 120, 112, 101, 99, 116, 101, 100, 32, 105, 100, 32, 0],
    };
static mut l_IO_FS_Stream_readResponseAs___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_Stream_readResponseAs___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_IO_FS_Stream_readResponseAs___redArg___closed__1_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [44, 32, 103, 111, 116, 32, 105, 100, 32, 0],
    };
static mut l_IO_FS_Stream_readResponseAs___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_Stream_readResponseAs___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_IO_FS_Stream_readResponseAs___redArg___closed__2_value: LeanStringObject<20> =
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
            85, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 114, 101, 115, 117, 108, 116, 32,
            39, 0,
        ],
    };
static mut l_IO_FS_Stream_readResponseAs___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_Stream_readResponseAs___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_IO_FS_Stream_readResponseAs___redArg___closed__3_value: LeanStringObject<35> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 35,
        m_capacity: 35,
        m_length: 34,
        m_data: [
            69, 120, 112, 101, 99, 116, 101, 100, 32, 74, 83, 79, 78, 45, 82, 80, 67, 32, 114, 101,
            115, 112, 111, 110, 115, 101, 44, 32, 103, 111, 116, 58, 32, 39, 0,
        ],
    };
static mut l_IO_FS_Stream_readResponseAs___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_Stream_readResponseAs___redArg___closed__3_value)
        as *mut LeanObject;
pub unsafe fn l_Lean_JsonRpc_RequestID_ctorIdx(mut v_x_3652_: *mut LeanObject) -> *mut LeanObject {
    match lean_obj_tag(v_x_3652_) {
        0 => {
            let mut v___x_3653_: *mut LeanObject = core::ptr::null_mut();
            v___x_3653_ = lean_unsigned_to_nat(0);
            return v___x_3653_;
        }
        1 => {
            let mut v___x_3654_: *mut LeanObject = core::ptr::null_mut();
            v___x_3654_ = lean_unsigned_to_nat(1);
            return v___x_3654_;
        }
        _ => {
            let mut v___x_3655_: *mut LeanObject = core::ptr::null_mut();
            v___x_3655_ = lean_unsigned_to_nat(2);
            return v___x_3655_;
        }
    }
}
pub unsafe fn l_Lean_JsonRpc_RequestID_ctorIdx___boxed(
    mut v_x_3656_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3657_: *mut LeanObject = core::ptr::null_mut();
    v_res_3657_ = l_Lean_JsonRpc_RequestID_ctorIdx(v_x_3656_);
    lean_dec(v_x_3656_);
    return v_res_3657_;
}
pub unsafe fn l_Lean_JsonRpc_RequestID_ctorElim___redArg(
    mut v_t_3658_: *mut LeanObject,
    mut v_k_3659_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_3658_) == 2 {
        return v_k_3659_;
    } else {
        let mut v_s_3660_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3661_: *mut LeanObject = core::ptr::null_mut();
        v_s_3660_ = lean_ctor_get(v_t_3658_, 0);
        lean_inc_ref(v_s_3660_);
        lean_dec(v_t_3658_);
        v___x_3661_ = lean_apply_1(v_k_3659_, v_s_3660_);
        return v___x_3661_;
    }
}
pub unsafe fn l_Lean_JsonRpc_RequestID_ctorElim(
    mut v_motive_3662_: *mut LeanObject,
    mut v_ctorIdx_3663_: *mut LeanObject,
    mut v_t_3664_: *mut LeanObject,
    mut v_h_3665_: *mut LeanObject,
    mut v_k_3666_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3667_: *mut LeanObject = core::ptr::null_mut();
    v___x_3667_ = l_Lean_JsonRpc_RequestID_ctorElim___redArg(v_t_3664_, v_k_3666_);
    return v___x_3667_;
}
pub unsafe fn l_Lean_JsonRpc_RequestID_ctorElim___boxed(
    mut v_motive_3668_: *mut LeanObject,
    mut v_ctorIdx_3669_: *mut LeanObject,
    mut v_t_3670_: *mut LeanObject,
    mut v_h_3671_: *mut LeanObject,
    mut v_k_3672_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3673_: *mut LeanObject = core::ptr::null_mut();
    v_res_3673_ = l_Lean_JsonRpc_RequestID_ctorElim(
        v_motive_3668_,
        v_ctorIdx_3669_,
        v_t_3670_,
        v_h_3671_,
        v_k_3672_,
    );
    lean_dec(v_ctorIdx_3669_);
    return v_res_3673_;
}
pub unsafe fn l_Lean_JsonRpc_RequestID_str_elim___redArg(
    mut v_t_3674_: *mut LeanObject,
    mut v_str_3675_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3676_: *mut LeanObject = core::ptr::null_mut();
    v___x_3676_ = l_Lean_JsonRpc_RequestID_ctorElim___redArg(v_t_3674_, v_str_3675_);
    return v___x_3676_;
}
pub unsafe fn l_Lean_JsonRpc_RequestID_str_elim(
    mut v_motive_3677_: *mut LeanObject,
    mut v_t_3678_: *mut LeanObject,
    mut v_h_3679_: *mut LeanObject,
    mut v_str_3680_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3681_: *mut LeanObject = core::ptr::null_mut();
    v___x_3681_ = l_Lean_JsonRpc_RequestID_ctorElim___redArg(v_t_3678_, v_str_3680_);
    return v___x_3681_;
}
pub unsafe fn l_Lean_JsonRpc_RequestID_num_elim___redArg(
    mut v_t_3682_: *mut LeanObject,
    mut v_num_3683_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3684_: *mut LeanObject = core::ptr::null_mut();
    v___x_3684_ = l_Lean_JsonRpc_RequestID_ctorElim___redArg(v_t_3682_, v_num_3683_);
    return v___x_3684_;
}
pub unsafe fn l_Lean_JsonRpc_RequestID_num_elim(
    mut v_motive_3685_: *mut LeanObject,
    mut v_t_3686_: *mut LeanObject,
    mut v_h_3687_: *mut LeanObject,
    mut v_num_3688_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3689_: *mut LeanObject = core::ptr::null_mut();
    v___x_3689_ = l_Lean_JsonRpc_RequestID_ctorElim___redArg(v_t_3686_, v_num_3688_);
    return v___x_3689_;
}
pub unsafe fn l_Lean_JsonRpc_RequestID_null_elim___redArg(
    mut v_t_3690_: *mut LeanObject,
    mut v_null_3691_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3692_: *mut LeanObject = core::ptr::null_mut();
    v___x_3692_ = l_Lean_JsonRpc_RequestID_ctorElim___redArg(v_t_3690_, v_null_3691_);
    return v___x_3692_;
}
pub unsafe fn l_Lean_JsonRpc_RequestID_null_elim(
    mut v_motive_3693_: *mut LeanObject,
    mut v_t_3694_: *mut LeanObject,
    mut v_h_3695_: *mut LeanObject,
    mut v_null_3696_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3697_: *mut LeanObject = core::ptr::null_mut();
    v___x_3697_ = l_Lean_JsonRpc_RequestID_ctorElim___redArg(v_t_3694_, v_null_3696_);
    return v___x_3697_;
}
pub unsafe fn l_Lean_JsonRpc_instBEqRequestID_beq(
    mut v_x_3703_: *mut LeanObject,
    mut v_x_3704_: *mut LeanObject,
) -> u8 {
    match lean_obj_tag(v_x_3703_) {
        0 => {
            if lean_obj_tag(v_x_3704_) == 0 {
                let mut v_s_3705_: *mut LeanObject = core::ptr::null_mut();
                let mut v_s_3706_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3707_: u8 = 0;
                v_s_3705_ = lean_ctor_get(v_x_3703_, 0);
                v_s_3706_ = lean_ctor_get(v_x_3704_, 0);
                v___x_3707_ = lean_string_dec_eq(v_s_3705_, v_s_3706_);
                return v___x_3707_;
            } else {
                let mut v___x_3708_: u8 = 0;
                v___x_3708_ = 0;
                return v___x_3708_;
            }
        }
        1 => {
            if lean_obj_tag(v_x_3704_) == 1 {
                let mut v_n_3709_: *mut LeanObject = core::ptr::null_mut();
                let mut v_n_3710_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3711_: u8 = 0;
                v_n_3709_ = lean_ctor_get(v_x_3703_, 0);
                v_n_3710_ = lean_ctor_get(v_x_3704_, 0);
                v___x_3711_ = l_Lean_instDecidableEqJsonNumber_decEq(v_n_3709_, v_n_3710_);
                return v___x_3711_;
            } else {
                let mut v___x_3712_: u8 = 0;
                v___x_3712_ = 0;
                return v___x_3712_;
            }
        }
        _ => {
            if lean_obj_tag(v_x_3704_) == 2 {
                let mut v___x_3713_: u8 = 0;
                v___x_3713_ = 1;
                return v___x_3713_;
            } else {
                let mut v___x_3714_: u8 = 0;
                v___x_3714_ = 0;
                return v___x_3714_;
            }
        }
    }
}
pub unsafe fn l_Lean_JsonRpc_instBEqRequestID_beq___boxed(
    mut v_x_3715_: *mut LeanObject,
    mut v_x_3716_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3717_: u8 = 0;
    let mut v_r_3718_: *mut LeanObject = core::ptr::null_mut();
    v_res_3717_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_x_3715_, v_x_3716_);
    lean_dec(v_x_3716_);
    lean_dec(v_x_3715_);
    v_r_3718_ = lean_box((v_res_3717_) as usize);
    return v_r_3718_;
}
pub unsafe fn l_Lean_JsonRpc_instHashableRequestID_hash(mut v_x_3721_: *mut LeanObject) -> u64 {
    match lean_obj_tag(v_x_3721_) {
        0 => {
            let mut v_s_3722_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3723_: u64 = 0;
            let mut v___x_3724_: u64 = 0;
            let mut v___x_3725_: u64 = 0;
            v_s_3722_ = lean_ctor_get(v_x_3721_, 0);
            v___x_3723_ = 0u64;
            v___x_3724_ = lean_string_hash(v_s_3722_);
            v___x_3725_ = lean_uint64_mix_hash(v___x_3723_, v___x_3724_);
            return v___x_3725_;
        }
        1 => {
            let mut v_n_3726_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3727_: u64 = 0;
            let mut v___x_3728_: u64 = 0;
            let mut v___x_3729_: u64 = 0;
            v_n_3726_ = lean_ctor_get(v_x_3721_, 0);
            v___x_3727_ = 1u64;
            v___x_3728_ = l_Lean_instHashableJsonNumber_hash(v_n_3726_);
            v___x_3729_ = lean_uint64_mix_hash(v___x_3727_, v___x_3728_);
            return v___x_3729_;
        }
        _ => {
            let mut v___x_3730_: u64 = 0;
            v___x_3730_ = 2u64;
            return v___x_3730_;
        }
    }
}
pub unsafe fn l_Lean_JsonRpc_instHashableRequestID_hash___boxed(
    mut v_x_3731_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3732_: u64 = 0;
    let mut v_r_3733_: *mut LeanObject = core::ptr::null_mut();
    v_res_3732_ = l_Lean_JsonRpc_instHashableRequestID_hash(v_x_3731_);
    lean_dec(v_x_3731_);
    v_r_3733_ = lean_box_uint64(v_res_3732_);
    return v_r_3733_;
}
pub unsafe fn l_Lean_JsonRpc_instOrdRequestID_ord(
    mut v_x_3736_: *mut LeanObject,
    mut v_x_3737_: *mut LeanObject,
) -> u8 {
    match lean_obj_tag(v_x_3736_) {
        0 => match lean_obj_tag(v_x_3737_) {
            0 => {
                let mut v_s_3738_: *mut LeanObject = core::ptr::null_mut();
                let mut v_s_3739_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3740_: u8 = 0;
                v_s_3738_ = lean_ctor_get(v_x_3736_, 0);
                lean_inc_ref(v_s_3738_);
                lean_dec_ref_known(v_x_3736_, 1);
                v_s_3739_ = lean_ctor_get(v_x_3737_, 0);
                lean_inc_ref(v_s_3739_);
                lean_dec_ref_known(v_x_3737_, 1);
                v___x_3740_ = lean_string_compare(v_s_3738_, v_s_3739_);
                lean_dec_ref(v_s_3739_);
                lean_dec_ref(v_s_3738_);
                if v___x_3740_ == 1 {
                    return v___x_3740_;
                } else {
                    return v___x_3740_;
                }
            }
            1 => {
                let mut v___x_3741_: u8 = 0;
                lean_dec_ref_known(v_x_3737_, 1);
                lean_dec_ref_known(v_x_3736_, 1);
                v___x_3741_ = 0;
                return v___x_3741_;
            }
            _ => {
                let mut v___x_3742_: u8 = 0;
                lean_dec_ref_known(v_x_3736_, 1);
                lean_dec(v_x_3737_);
                v___x_3742_ = 0;
                return v___x_3742_;
            }
        },
        1 => match lean_obj_tag(v_x_3737_) {
            0 => {
                let mut v___x_3743_: u8 = 0;
                lean_dec_ref_known(v_x_3737_, 1);
                lean_dec_ref_known(v_x_3736_, 1);
                v___x_3743_ = 2;
                return v___x_3743_;
            }
            1 => {
                let mut v_n_3744_: *mut LeanObject = core::ptr::null_mut();
                let mut v_n_3745_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3746_: u8 = 0;
                v_n_3744_ = lean_ctor_get(v_x_3736_, 0);
                lean_inc_ref_n(v_n_3744_, 2);
                lean_dec_ref_known(v_x_3736_, 1);
                v_n_3745_ = lean_ctor_get(v_x_3737_, 0);
                lean_inc_ref_n(v_n_3745_, 2);
                lean_dec_ref_known(v_x_3737_, 1);
                v___x_3746_ = l_Lean_JsonNumber_lt(v_n_3744_, v_n_3745_);
                if v___x_3746_ == 0 {
                    let mut v___x_3747_: u8 = 0;
                    v___x_3747_ = l_Lean_JsonNumber_lt(v_n_3745_, v_n_3744_);
                    if v___x_3747_ == 0 {
                        let mut v___x_3748_: u8 = 0;
                        v___x_3748_ = 1;
                        return v___x_3748_;
                    } else {
                        let mut v___x_3749_: u8 = 0;
                        v___x_3749_ = 2;
                        return v___x_3749_;
                    }
                } else {
                    let mut v___x_3750_: u8 = 0;
                    lean_dec_ref(v_n_3745_);
                    lean_dec_ref(v_n_3744_);
                    v___x_3750_ = 0;
                    return v___x_3750_;
                }
            }
            _ => {
                let mut v___x_3751_: u8 = 0;
                lean_dec_ref_known(v_x_3736_, 1);
                lean_dec(v_x_3737_);
                v___x_3751_ = 0;
                return v___x_3751_;
            }
        },
        _ => {
            if lean_obj_tag(v_x_3737_) == 2 {
                let mut v___x_3752_: u8 = 0;
                v___x_3752_ = 1;
                return v___x_3752_;
            } else {
                let mut v___x_3753_: u8 = 0;
                lean_dec(v_x_3737_);
                v___x_3753_ = 2;
                return v___x_3753_;
            }
        }
    }
}
pub unsafe fn l_Lean_JsonRpc_instOrdRequestID_ord___boxed(
    mut v_x_3754_: *mut LeanObject,
    mut v_x_3755_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3756_: u8 = 0;
    let mut v_r_3757_: *mut LeanObject = core::ptr::null_mut();
    v_res_3756_ = l_Lean_JsonRpc_instOrdRequestID_ord(v_x_3754_, v_x_3755_);
    v_r_3757_ = lean_box((v_res_3756_) as usize);
    return v_r_3757_;
}
pub unsafe fn l_Lean_JsonRpc_instOfNatRequestID(mut v_n_3760_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_3761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: *mut LeanObject = core::ptr::null_mut();
    v___x_3761_ = l_Lean_JsonNumber_fromNat(v_n_3760_);
    v___x_3762_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_3762_, 0, v___x_3761_);
    return v___x_3762_;
}
pub unsafe fn l_Lean_JsonRpc_instToStringRequestID___lam__0(
    mut v_x_3765_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_3765_) {
        0 => {
            let mut v_s_3766_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3767_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3768_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3769_: *mut LeanObject = core::ptr::null_mut();
            v_s_3766_ = lean_ctor_get(v_x_3765_, 0);
            lean_inc_ref(v_s_3766_);
            lean_dec_ref_known(v_x_3765_, 1);
            v___x_3767_ = l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__0;
            v___x_3768_ = lean_string_append(v___x_3767_, v_s_3766_);
            lean_dec_ref(v_s_3766_);
            v___x_3769_ = lean_string_append(v___x_3768_, v___x_3767_);
            return v___x_3769_;
        }
        1 => {
            let mut v_n_3770_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3771_: *mut LeanObject = core::ptr::null_mut();
            v_n_3770_ = lean_ctor_get(v_x_3765_, 0);
            lean_inc_ref(v_n_3770_);
            lean_dec_ref_known(v_x_3765_, 1);
            v___x_3771_ = l_Lean_JsonNumber_toString(v_n_3770_);
            return v___x_3771_;
        }
        _ => {
            let mut v___x_3772_: *mut LeanObject = core::ptr::null_mut();
            v___x_3772_ = l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__1;
            return v___x_3772_;
        }
    }
}
pub unsafe fn l_Lean_JsonRpc_ErrorCode_ctorIdx(mut v_x_3775_: u8) -> *mut LeanObject {
    match v_x_3775_ {
        0 => {
            let mut v___x_3776_: *mut LeanObject = core::ptr::null_mut();
            v___x_3776_ = lean_unsigned_to_nat(0);
            return v___x_3776_;
        }
        1 => {
            let mut v___x_3777_: *mut LeanObject = core::ptr::null_mut();
            v___x_3777_ = lean_unsigned_to_nat(1);
            return v___x_3777_;
        }
        2 => {
            let mut v___x_3778_: *mut LeanObject = core::ptr::null_mut();
            v___x_3778_ = lean_unsigned_to_nat(2);
            return v___x_3778_;
        }
        3 => {
            let mut v___x_3779_: *mut LeanObject = core::ptr::null_mut();
            v___x_3779_ = lean_unsigned_to_nat(3);
            return v___x_3779_;
        }
        4 => {
            let mut v___x_3780_: *mut LeanObject = core::ptr::null_mut();
            v___x_3780_ = lean_unsigned_to_nat(4);
            return v___x_3780_;
        }
        5 => {
            let mut v___x_3781_: *mut LeanObject = core::ptr::null_mut();
            v___x_3781_ = lean_unsigned_to_nat(5);
            return v___x_3781_;
        }
        6 => {
            let mut v___x_3782_: *mut LeanObject = core::ptr::null_mut();
            v___x_3782_ = lean_unsigned_to_nat(6);
            return v___x_3782_;
        }
        7 => {
            let mut v___x_3783_: *mut LeanObject = core::ptr::null_mut();
            v___x_3783_ = lean_unsigned_to_nat(7);
            return v___x_3783_;
        }
        8 => {
            let mut v___x_3784_: *mut LeanObject = core::ptr::null_mut();
            v___x_3784_ = lean_unsigned_to_nat(8);
            return v___x_3784_;
        }
        9 => {
            let mut v___x_3785_: *mut LeanObject = core::ptr::null_mut();
            v___x_3785_ = lean_unsigned_to_nat(9);
            return v___x_3785_;
        }
        10 => {
            let mut v___x_3786_: *mut LeanObject = core::ptr::null_mut();
            v___x_3786_ = lean_unsigned_to_nat(10);
            return v___x_3786_;
        }
        _ => {
            let mut v___x_3787_: *mut LeanObject = core::ptr::null_mut();
            v___x_3787_ = lean_unsigned_to_nat(11);
            return v___x_3787_;
        }
    }
}
pub unsafe fn l_Lean_JsonRpc_ErrorCode_ctorIdx___boxed(
    mut v_x_3788_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_3789_: u8 = 0;
    let mut v_res_3790_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_3789_ = (lean_unbox(v_x_3788_) as u8);
    v_res_3790_ = l_Lean_JsonRpc_ErrorCode_ctorIdx(v_x_boxed_3789_);
    return v_res_3790_;
}
pub unsafe fn l_Lean_JsonRpc_ErrorCode_toCtorIdx(mut v_x_3791_: u8) -> *mut LeanObject {
    let mut v___x_3792_: *mut LeanObject = core::ptr::null_mut();
    v___x_3792_ = l_Lean_JsonRpc_ErrorCode_ctorIdx(v_x_3791_);
    return v___x_3792_;
}
pub unsafe fn l_Lean_JsonRpc_ErrorCode_toCtorIdx___boxed(
    mut v_x_3793_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4__boxed_3794_: u8 = 0;
    let mut v_res_3795_: *mut LeanObject = core::ptr::null_mut();
    v_x_4__boxed_3794_ = (lean_unbox(v_x_3793_) as u8);
    v_res_3795_ = l_Lean_JsonRpc_ErrorCode_toCtorIdx(v_x_4__boxed_3794_);
    return v_res_3795_;
}
pub unsafe fn l_Lean_JsonRpc_ErrorCode_ctorElim___redArg(
    mut v_k_3796_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_3796_);
    return v_k_3796_;
}
pub unsafe fn l_Lean_JsonRpc_ErrorCode_ctorElim___redArg___boxed(
    mut v_k_3797_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3798_: *mut LeanObject = core::ptr::null_mut();
    v_res_3798_ = l_Lean_JsonRpc_ErrorCode_ctorElim___redArg(v_k_3797_);
    lean_dec(v_k_3797_);
    return v_res_3798_;
}
pub unsafe fn l_Lean_JsonRpc_ErrorCode_ctorElim(
    mut v_motive_3799_: *mut LeanObject,
    mut v_ctorIdx_3800_: *mut LeanObject,
    mut v_t_3801_: u8,
    mut v_h_3802_: *mut LeanObject,
    mut v_k_3803_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_3803_);
    return v_k_3803_;
}
pub unsafe fn l_Lean_JsonRpc_ErrorCode_ctorElim___boxed(
    mut v_motive_3804_: *mut LeanObject,
    mut v_ctorIdx_3805_: *mut LeanObject,
    mut v_t_3806_: *mut LeanObject,
    mut v_h_3807_: *mut LeanObject,
    mut v_k_3808_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_3809_: u8 = 0;
    let mut v_res_3810_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_3809_ = (lean_unbox(v_t_3806_) as u8);
    v_res_3810_ = l_Lean_JsonRpc_ErrorCode_ctorElim(
        v_motive_3804_,
        v_ctorIdx_3805_,
        v_t_boxed_3809_,
        v_h_3807_,
        v_k_3808_,
    );
    lean_dec(v_k_3808_);
    lean_dec(v_ctorIdx_3805_);
    return v_res_3810_;
}
pub unsafe fn l_Lean_JsonRpc_ErrorCode_parseError_elim___redArg(
    mut v_parseError_3811_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_parseError_3811_);
    return v_parseError_3811_;
}
pub unsafe fn l_Lean_JsonRpc_ErrorCode_parseError_elim___redArg___boxed(
    mut v_parseError_3812_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3813_: *mut LeanObject = core::ptr::null_mut();
    v_res_3813_ = l_Lean_JsonRpc_ErrorCode_parseError_elim___redArg(v_parseError_3812_);
    lean_dec(v_parseError_3812_);
    return v_res_3813_;
}
pub unsafe fn l_Lean_JsonRpc_ErrorCode_parseError_elim(
    mut v_motive_3814_: *mut LeanObject,
    mut v_t_3815_: u8,
    mut v_h_3816_: *mut LeanObject,
    mut v_parseError_3817_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_parseError_3817_);
    return v_parseError_3817_;
}
pub unsafe fn l_Lean_JsonRpc_ErrorCode_parseError_elim___boxed(
    mut v_motive_3818_: *mut LeanObject,
    mut v_t_3819_: *mut LeanObject,
    mut v_h_3820_: *mut LeanObject,
    mut v_parseError_3821_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_3822_: u8 = 0;
    let mut v_res_3823_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_3822_ = (lean_unbox(v_t_3819_) as u8);
    v_res_3823_ = l_Lean_JsonRpc_ErrorCode_parseError_elim(
        v_motive_3818_,
        v_t_boxed_3822_,
        v_h_3820_,
        v_parseError_3821_,
    );
    lean_dec(v_parseError_3821_);
    return v_res_3823_;
}
pub unsafe fn l_Lean_JsonRpc_ErrorCode_invalidRequest_elim___redArg(
    mut v_invalidRequest_3824_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_invalidRequest_3824_);
    return v_invalidRequest_3824_;
}
pub unsafe fn l_Lean_JsonRpc_ErrorCode_invalidRequest_elim___redArg___boxed(
    mut v_invalidRequest_3825_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3826_: *mut LeanObject = core::ptr::null_mut();
    v_res_3826_ = l_Lean_JsonRpc_ErrorCode_invalidRequest_elim___redArg(v_invalidRequest_3825_);
    lean_dec(v_invalidRequest_3825_);
    return v_res_3826_;
}
pub unsafe fn l_Lean_JsonRpc_ErrorCode_invalidRequest_elim(
    mut v_motive_3827_: *mut LeanObject,
    mut v_t_3828_: u8,
    mut v_h_3829_: *mut LeanObject,
    mut v_invalidRequest_3830_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_invalidRequest_3830_);
    return v_invalidRequest_3830_;
}
pub unsafe fn l_Lean_JsonRpc_ErrorCode_invalidRequest_elim___boxed(
    mut v_motive_3831_: *mut LeanObject,
    mut v_t_3832_: *mut LeanObject,
    mut v_h_3833_: *mut LeanObject,
    mut v_invalidRequest_3834_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_3835_: u8 = 0;
    let mut v_res_3836_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_3835_ = (lean_unbox(v_t_3832_) as u8);
    v_res_3836_ = l_Lean_JsonRpc_ErrorCode_invalidRequest_elim(
        v_motive_3831_,
        v_t_boxed_3835_,
        v_h_3833_,
        v_invalidRequest_3834_,
    );
    lean_dec(v_invalidRequest_3834_);
    return v_res_3836_;
}
pub unsafe fn l_Lean_JsonRpc_ErrorCode_methodNotFound_elim___redArg(
    mut v_methodNotFound_3837_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_methodNotFound_3837_);
    return v_methodNotFound_3837_;
}
pub unsafe fn l_Lean_JsonRpc_ErrorCode_methodNotFound_elim___redArg___boxed(
    mut v_methodNotFound_3838_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3839_: *mut LeanObject = core::ptr::null_mut();
    v_res_3839_ = l_Lean_JsonRpc_ErrorCode_methodNotFound_elim___redArg(v_methodNotFound_3838_);
    lean_dec(v_methodNotFound_3838_);
    return v_res_3839_;
}
pub unsafe fn l_Lean_JsonRpc_ErrorCode_methodNotFound_elim(
    mut v_motive_3840_: *mut LeanObject,
    mut v_t_3841_: u8,
    mut v_h_3842_: *mut LeanObject,
    mut v_methodNotFound_3843_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_methodNotFound_3843_);
    return v_methodNotFound_3843_;
}
pub unsafe fn l_Lean_JsonRpc_ErrorCode_methodNotFound_elim___boxed(
    mut v_motive_3844_: *mut LeanObject,
    mut v_t_3845_: *mut LeanObject,
    mut v_h_3846_: *mut LeanObject,
    mut v_methodNotFound_3847_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_3848_: u8 = 0;
    let mut v_res_3849_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_3848_ = (lean_unbox(v_t_3845_) as u8);
    v_res_3849_ = l_Lean_JsonRpc_ErrorCode_methodNotFound_elim(
        v_motive_3844_,
        v_t_boxed_3848_,
        v_h_3846_,
        v_methodNotFound_3847_,
    );
    lean_dec(v_methodNotFound_3847_);
    return v_res_3849_;
}
pub unsafe fn l_Lean_JsonRpc_ErrorCode_invalidParams_elim___redArg(
    mut v_invalidParams_3850_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_invalidParams_3850_);
    return v_invalidParams_3850_;
}
pub unsafe fn l_Lean_JsonRpc_ErrorCode_invalidParams_elim___redArg___boxed(
    mut v_invalidParams_3851_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3852_: *mut LeanObject = core::ptr::null_mut();
    v_res_3852_ = l_Lean_JsonRpc_ErrorCode_invalidParams_elim___redArg(v_invalidParams_3851_);
    lean_dec(v_invalidParams_3851_);
    return v_res_3852_;
}
pub unsafe fn l_Lean_JsonRpc_ErrorCode_invalidParams_elim(
    mut v_motive_3853_: *mut LeanObject,
    mut v_t_3854_: u8,
    mut v_h_3855_: *mut LeanObject,
    mut v_invalidParams_3856_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_invalidParams_3856_);
    return v_invalidParams_3856_;
}
pub unsafe fn l_Lean_JsonRpc_ErrorCode_invalidParams_elim___boxed(
    mut v_motive_3857_: *mut LeanObject,
    mut v_t_3858_: *mut LeanObject,
    mut v_h_3859_: *mut LeanObject,
    mut v_invalidParams_3860_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_3861_: u8 = 0;
    let mut v_res_3862_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_3861_ = (lean_unbox(v_t_3858_) as u8);
    v_res_3862_ = l_Lean_JsonRpc_ErrorCode_invalidParams_elim(
        v_motive_3857_,
        v_t_boxed_3861_,
        v_h_3859_,
        v_invalidParams_3860_,
    );
    lean_dec(v_invalidParams_3860_);
    return v_res_3862_;
}
pub unsafe fn l_Lean_JsonRpc_ErrorCode_internalError_elim___redArg(
    mut v_internalError_3863_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_internalError_3863_);
    return v_internalError_3863_;
}
pub unsafe fn l_Lean_JsonRpc_ErrorCode_internalError_elim___redArg___boxed(
    mut v_internalError_3864_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3865_: *mut LeanObject = core::ptr::null_mut();
    v_res_3865_ = l_Lean_JsonRpc_ErrorCode_internalError_elim___redArg(v_internalError_3864_);
    lean_dec(v_internalError_3864_);
    return v_res_3865_;
}
pub unsafe fn l_Lean_JsonRpc_ErrorCode_internalError_elim(
    mut v_motive_3866_: *mut LeanObject,
    mut v_t_3867_: u8,
    mut v_h_3868_: *mut LeanObject,
    mut v_internalError_3869_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_internalError_3869_);
    return v_internalError_3869_;
}
pub unsafe fn l_Lean_JsonRpc_ErrorCode_internalError_elim___boxed(
    mut v_motive_3870_: *mut LeanObject,
    mut v_t_3871_: *mut LeanObject,
    mut v_h_3872_: *mut LeanObject,
    mut v_internalError_3873_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_3874_: u8 = 0;
    let mut v_res_3875_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_3874_ = (lean_unbox(v_t_3871_) as u8);
    v_res_3875_ = l_Lean_JsonRpc_ErrorCode_internalError_elim(
        v_motive_3870_,
        v_t_boxed_3874_,
        v_h_3872_,
        v_internalError_3873_,
    );
    lean_dec(v_internalError_3873_);
    return v_res_3875_;
}
pub unsafe fn l_Lean_JsonRpc_ErrorCode_serverNotInitialized_elim___redArg(
    mut v_serverNotInitialized_3876_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_serverNotInitialized_3876_);
    return v_serverNotInitialized_3876_;
}
pub unsafe fn l_Lean_JsonRpc_ErrorCode_serverNotInitialized_elim___redArg___boxed(
    mut v_serverNotInitialized_3877_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3878_: *mut LeanObject = core::ptr::null_mut();
    v_res_3878_ =
        l_Lean_JsonRpc_ErrorCode_serverNotInitialized_elim___redArg(v_serverNotInitialized_3877_);
    lean_dec(v_serverNotInitialized_3877_);
    return v_res_3878_;
}
pub unsafe fn l_Lean_JsonRpc_ErrorCode_serverNotInitialized_elim(
    mut v_motive_3879_: *mut LeanObject,
    mut v_t_3880_: u8,
    mut v_h_3881_: *mut LeanObject,
    mut v_serverNotInitialized_3882_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_serverNotInitialized_3882_);
    return v_serverNotInitialized_3882_;
}
pub unsafe fn l_Lean_JsonRpc_ErrorCode_serverNotInitialized_elim___boxed(
    mut v_motive_3883_: *mut LeanObject,
    mut v_t_3884_: *mut LeanObject,
    mut v_h_3885_: *mut LeanObject,
    mut v_serverNotInitialized_3886_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_3887_: u8 = 0;
    let mut v_res_3888_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_3887_ = (lean_unbox(v_t_3884_) as u8);
    v_res_3888_ = l_Lean_JsonRpc_ErrorCode_serverNotInitialized_elim(
        v_motive_3883_,
        v_t_boxed_3887_,
        v_h_3885_,
        v_serverNotInitialized_3886_,
    );
    lean_dec(v_serverNotInitialized_3886_);
    return v_res_3888_;
}
pub unsafe fn l_Lean_JsonRpc_ErrorCode_unknownErrorCode_elim___redArg(
    mut v_unknownErrorCode_3889_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_unknownErrorCode_3889_);
    return v_unknownErrorCode_3889_;
}
pub unsafe fn l_Lean_JsonRpc_ErrorCode_unknownErrorCode_elim___redArg___boxed(
    mut v_unknownErrorCode_3890_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3891_: *mut LeanObject = core::ptr::null_mut();
    v_res_3891_ = l_Lean_JsonRpc_ErrorCode_unknownErrorCode_elim___redArg(v_unknownErrorCode_3890_);
    lean_dec(v_unknownErrorCode_3890_);
    return v_res_3891_;
}
pub unsafe fn l_Lean_JsonRpc_ErrorCode_unknownErrorCode_elim(
    mut v_motive_3892_: *mut LeanObject,
    mut v_t_3893_: u8,
    mut v_h_3894_: *mut LeanObject,
    mut v_unknownErrorCode_3895_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_unknownErrorCode_3895_);
    return v_unknownErrorCode_3895_;
}
pub unsafe fn l_Lean_JsonRpc_ErrorCode_unknownErrorCode_elim___boxed(
    mut v_motive_3896_: *mut LeanObject,
    mut v_t_3897_: *mut LeanObject,
    mut v_h_3898_: *mut LeanObject,
    mut v_unknownErrorCode_3899_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_3900_: u8 = 0;
    let mut v_res_3901_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_3900_ = (lean_unbox(v_t_3897_) as u8);
    v_res_3901_ = l_Lean_JsonRpc_ErrorCode_unknownErrorCode_elim(
        v_motive_3896_,
        v_t_boxed_3900_,
        v_h_3898_,
        v_unknownErrorCode_3899_,
    );
    lean_dec(v_unknownErrorCode_3899_);
    return v_res_3901_;
}
pub unsafe fn l_Lean_JsonRpc_ErrorCode_contentModified_elim___redArg(
    mut v_contentModified_3902_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_contentModified_3902_);
    return v_contentModified_3902_;
}
pub unsafe fn l_Lean_JsonRpc_ErrorCode_contentModified_elim___redArg___boxed(
    mut v_contentModified_3903_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3904_: *mut LeanObject = core::ptr::null_mut();
    v_res_3904_ = l_Lean_JsonRpc_ErrorCode_contentModified_elim___redArg(v_contentModified_3903_);
    lean_dec(v_contentModified_3903_);
    return v_res_3904_;
}
pub unsafe fn l_Lean_JsonRpc_ErrorCode_contentModified_elim(
    mut v_motive_3905_: *mut LeanObject,
    mut v_t_3906_: u8,
    mut v_h_3907_: *mut LeanObject,
    mut v_contentModified_3908_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_contentModified_3908_);
    return v_contentModified_3908_;
}
pub unsafe fn l_Lean_JsonRpc_ErrorCode_contentModified_elim___boxed(
    mut v_motive_3909_: *mut LeanObject,
    mut v_t_3910_: *mut LeanObject,
    mut v_h_3911_: *mut LeanObject,
    mut v_contentModified_3912_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_3913_: u8 = 0;
    let mut v_res_3914_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_3913_ = (lean_unbox(v_t_3910_) as u8);
    v_res_3914_ = l_Lean_JsonRpc_ErrorCode_contentModified_elim(
        v_motive_3909_,
        v_t_boxed_3913_,
        v_h_3911_,
        v_contentModified_3912_,
    );
    lean_dec(v_contentModified_3912_);
    return v_res_3914_;
}
pub unsafe fn l_Lean_JsonRpc_ErrorCode_requestCancelled_elim___redArg(
    mut v_requestCancelled_3915_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_requestCancelled_3915_);
    return v_requestCancelled_3915_;
}
pub unsafe fn l_Lean_JsonRpc_ErrorCode_requestCancelled_elim___redArg___boxed(
    mut v_requestCancelled_3916_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3917_: *mut LeanObject = core::ptr::null_mut();
    v_res_3917_ = l_Lean_JsonRpc_ErrorCode_requestCancelled_elim___redArg(v_requestCancelled_3916_);
    lean_dec(v_requestCancelled_3916_);
    return v_res_3917_;
}
pub unsafe fn l_Lean_JsonRpc_ErrorCode_requestCancelled_elim(
    mut v_motive_3918_: *mut LeanObject,
    mut v_t_3919_: u8,
    mut v_h_3920_: *mut LeanObject,
    mut v_requestCancelled_3921_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_requestCancelled_3921_);
    return v_requestCancelled_3921_;
}
pub unsafe fn l_Lean_JsonRpc_ErrorCode_requestCancelled_elim___boxed(
    mut v_motive_3922_: *mut LeanObject,
    mut v_t_3923_: *mut LeanObject,
    mut v_h_3924_: *mut LeanObject,
    mut v_requestCancelled_3925_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_3926_: u8 = 0;
    let mut v_res_3927_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_3926_ = (lean_unbox(v_t_3923_) as u8);
    v_res_3927_ = l_Lean_JsonRpc_ErrorCode_requestCancelled_elim(
        v_motive_3922_,
        v_t_boxed_3926_,
        v_h_3924_,
        v_requestCancelled_3925_,
    );
    lean_dec(v_requestCancelled_3925_);
    return v_res_3927_;
}
pub unsafe fn l_Lean_JsonRpc_ErrorCode_rpcNeedsReconnect_elim___redArg(
    mut v_rpcNeedsReconnect_3928_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_rpcNeedsReconnect_3928_);
    return v_rpcNeedsReconnect_3928_;
}
pub unsafe fn l_Lean_JsonRpc_ErrorCode_rpcNeedsReconnect_elim___redArg___boxed(
    mut v_rpcNeedsReconnect_3929_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3930_: *mut LeanObject = core::ptr::null_mut();
    v_res_3930_ =
        l_Lean_JsonRpc_ErrorCode_rpcNeedsReconnect_elim___redArg(v_rpcNeedsReconnect_3929_);
    lean_dec(v_rpcNeedsReconnect_3929_);
    return v_res_3930_;
}
pub unsafe fn l_Lean_JsonRpc_ErrorCode_rpcNeedsReconnect_elim(
    mut v_motive_3931_: *mut LeanObject,
    mut v_t_3932_: u8,
    mut v_h_3933_: *mut LeanObject,
    mut v_rpcNeedsReconnect_3934_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_rpcNeedsReconnect_3934_);
    return v_rpcNeedsReconnect_3934_;
}
pub unsafe fn l_Lean_JsonRpc_ErrorCode_rpcNeedsReconnect_elim___boxed(
    mut v_motive_3935_: *mut LeanObject,
    mut v_t_3936_: *mut LeanObject,
    mut v_h_3937_: *mut LeanObject,
    mut v_rpcNeedsReconnect_3938_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_3939_: u8 = 0;
    let mut v_res_3940_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_3939_ = (lean_unbox(v_t_3936_) as u8);
    v_res_3940_ = l_Lean_JsonRpc_ErrorCode_rpcNeedsReconnect_elim(
        v_motive_3935_,
        v_t_boxed_3939_,
        v_h_3937_,
        v_rpcNeedsReconnect_3938_,
    );
    lean_dec(v_rpcNeedsReconnect_3938_);
    return v_res_3940_;
}
pub unsafe fn l_Lean_JsonRpc_ErrorCode_workerExited_elim___redArg(
    mut v_workerExited_3941_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_workerExited_3941_);
    return v_workerExited_3941_;
}
pub unsafe fn l_Lean_JsonRpc_ErrorCode_workerExited_elim___redArg___boxed(
    mut v_workerExited_3942_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3943_: *mut LeanObject = core::ptr::null_mut();
    v_res_3943_ = l_Lean_JsonRpc_ErrorCode_workerExited_elim___redArg(v_workerExited_3942_);
    lean_dec(v_workerExited_3942_);
    return v_res_3943_;
}
pub unsafe fn l_Lean_JsonRpc_ErrorCode_workerExited_elim(
    mut v_motive_3944_: *mut LeanObject,
    mut v_t_3945_: u8,
    mut v_h_3946_: *mut LeanObject,
    mut v_workerExited_3947_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_workerExited_3947_);
    return v_workerExited_3947_;
}
pub unsafe fn l_Lean_JsonRpc_ErrorCode_workerExited_elim___boxed(
    mut v_motive_3948_: *mut LeanObject,
    mut v_t_3949_: *mut LeanObject,
    mut v_h_3950_: *mut LeanObject,
    mut v_workerExited_3951_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_3952_: u8 = 0;
    let mut v_res_3953_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_3952_ = (lean_unbox(v_t_3949_) as u8);
    v_res_3953_ = l_Lean_JsonRpc_ErrorCode_workerExited_elim(
        v_motive_3948_,
        v_t_boxed_3952_,
        v_h_3950_,
        v_workerExited_3951_,
    );
    lean_dec(v_workerExited_3951_);
    return v_res_3953_;
}
pub unsafe fn l_Lean_JsonRpc_ErrorCode_workerCrashed_elim___redArg(
    mut v_workerCrashed_3954_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_workerCrashed_3954_);
    return v_workerCrashed_3954_;
}
pub unsafe fn l_Lean_JsonRpc_ErrorCode_workerCrashed_elim___redArg___boxed(
    mut v_workerCrashed_3955_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3956_: *mut LeanObject = core::ptr::null_mut();
    v_res_3956_ = l_Lean_JsonRpc_ErrorCode_workerCrashed_elim___redArg(v_workerCrashed_3955_);
    lean_dec(v_workerCrashed_3955_);
    return v_res_3956_;
}
pub unsafe fn l_Lean_JsonRpc_ErrorCode_workerCrashed_elim(
    mut v_motive_3957_: *mut LeanObject,
    mut v_t_3958_: u8,
    mut v_h_3959_: *mut LeanObject,
    mut v_workerCrashed_3960_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_workerCrashed_3960_);
    return v_workerCrashed_3960_;
}
pub unsafe fn l_Lean_JsonRpc_ErrorCode_workerCrashed_elim___boxed(
    mut v_motive_3961_: *mut LeanObject,
    mut v_t_3962_: *mut LeanObject,
    mut v_h_3963_: *mut LeanObject,
    mut v_workerCrashed_3964_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_3965_: u8 = 0;
    let mut v_res_3966_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_3965_ = (lean_unbox(v_t_3962_) as u8);
    v_res_3966_ = l_Lean_JsonRpc_ErrorCode_workerCrashed_elim(
        v_motive_3961_,
        v_t_boxed_3965_,
        v_h_3963_,
        v_workerCrashed_3964_,
    );
    lean_dec(v_workerCrashed_3964_);
    return v_res_3966_;
}
pub unsafe fn _init_l_Lean_JsonRpc_instInhabitedErrorCode_default() -> u8 {
    let mut v___x_3967_: u8 = 0;
    v___x_3967_ = 0;
    return v___x_3967_;
}
pub unsafe fn _init_l_Lean_JsonRpc_instInhabitedErrorCode() -> u8 {
    let mut v___x_3968_: u8 = 0;
    v___x_3968_ = 0;
    return v___x_3968_;
}
pub unsafe fn l_Lean_JsonRpc_instBEqErrorCode_beq(mut v_x_3969_: u8, mut v_y_3970_: u8) -> u8 {
    let mut v___x_3971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: u8 = 0;
    v___x_3971_ = l_Lean_JsonRpc_ErrorCode_ctorIdx(v_x_3969_);
    v___x_3972_ = l_Lean_JsonRpc_ErrorCode_ctorIdx(v_y_3970_);
    v___x_3973_ = lean_nat_dec_eq(v___x_3971_, v___x_3972_);
    lean_dec(v___x_3972_);
    lean_dec(v___x_3971_);
    return v___x_3973_;
}
pub unsafe fn l_Lean_JsonRpc_instBEqErrorCode_beq___boxed(
    mut v_x_3974_: *mut LeanObject,
    mut v_y_3975_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_17__boxed_3976_: u8 = 0;
    let mut v_y_18__boxed_3977_: u8 = 0;
    let mut v_res_3978_: u8 = 0;
    let mut v_r_3979_: *mut LeanObject = core::ptr::null_mut();
    v_x_17__boxed_3976_ = (lean_unbox(v_x_3974_) as u8);
    v_y_18__boxed_3977_ = (lean_unbox(v_y_3975_) as u8);
    v_res_3978_ = l_Lean_JsonRpc_instBEqErrorCode_beq(v_x_17__boxed_3976_, v_y_18__boxed_3977_);
    v_r_3979_ = lean_box((v_res_3978_) as usize);
    return v_r_3979_;
}
pub unsafe fn _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__2() -> *mut LeanObject {
    let mut v___x_3985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: *mut LeanObject = core::ptr::null_mut();
    v___x_3985_ = lean_unsigned_to_nat(32700);
    v___x_3986_ = lean_nat_to_int(v___x_3985_);
    return v___x_3986_;
}
pub unsafe fn _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3() -> *mut LeanObject {
    let mut v___x_3987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: *mut LeanObject = core::ptr::null_mut();
    v___x_3987_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__2_once),
        _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__2,
    );
    v___x_3988_ = lean_int_neg(v___x_3987_);
    return v___x_3988_;
}
pub unsafe fn _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__4() -> *mut LeanObject {
    let mut v___x_3989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: *mut LeanObject = core::ptr::null_mut();
    v___x_3989_ = lean_unsigned_to_nat(32600);
    v___x_3990_ = lean_nat_to_int(v___x_3989_);
    return v___x_3990_;
}
pub unsafe fn _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5() -> *mut LeanObject {
    let mut v___x_3991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: *mut LeanObject = core::ptr::null_mut();
    v___x_3991_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__4),
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__4_once),
        _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__4,
    );
    v___x_3992_ = lean_int_neg(v___x_3991_);
    return v___x_3992_;
}
pub unsafe fn _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__6() -> *mut LeanObject {
    let mut v___x_3993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut LeanObject = core::ptr::null_mut();
    v___x_3993_ = lean_unsigned_to_nat(32601);
    v___x_3994_ = lean_nat_to_int(v___x_3993_);
    return v___x_3994_;
}
pub unsafe fn _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7() -> *mut LeanObject {
    let mut v___x_3995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut LeanObject = core::ptr::null_mut();
    v___x_3995_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__6),
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__6_once),
        _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__6,
    );
    v___x_3996_ = lean_int_neg(v___x_3995_);
    return v___x_3996_;
}
pub unsafe fn _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__8() -> *mut LeanObject {
    let mut v___x_3997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut LeanObject = core::ptr::null_mut();
    v___x_3997_ = lean_unsigned_to_nat(32602);
    v___x_3998_ = lean_nat_to_int(v___x_3997_);
    return v___x_3998_;
}
pub unsafe fn _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9() -> *mut LeanObject {
    let mut v___x_3999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut LeanObject = core::ptr::null_mut();
    v___x_3999_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__8),
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__8_once),
        _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__8,
    );
    v___x_4000_ = lean_int_neg(v___x_3999_);
    return v___x_4000_;
}
pub unsafe fn _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__10() -> *mut LeanObject
{
    let mut v___x_4001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut LeanObject = core::ptr::null_mut();
    v___x_4001_ = lean_unsigned_to_nat(32603);
    v___x_4002_ = lean_nat_to_int(v___x_4001_);
    return v___x_4002_;
}
pub unsafe fn _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11() -> *mut LeanObject
{
    let mut v___x_4003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut LeanObject = core::ptr::null_mut();
    v___x_4003_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__10),
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__10_once),
        _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__10,
    );
    v___x_4004_ = lean_int_neg(v___x_4003_);
    return v___x_4004_;
}
pub unsafe fn _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__12() -> *mut LeanObject
{
    let mut v___x_4005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: *mut LeanObject = core::ptr::null_mut();
    v___x_4005_ = lean_unsigned_to_nat(32002);
    v___x_4006_ = lean_nat_to_int(v___x_4005_);
    return v___x_4006_;
}
pub unsafe fn _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13() -> *mut LeanObject
{
    let mut v___x_4007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4008_: *mut LeanObject = core::ptr::null_mut();
    v___x_4007_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__12),
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__12_once),
        _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__12,
    );
    v___x_4008_ = lean_int_neg(v___x_4007_);
    return v___x_4008_;
}
pub unsafe fn _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__14() -> *mut LeanObject
{
    let mut v___x_4009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut LeanObject = core::ptr::null_mut();
    v___x_4009_ = lean_unsigned_to_nat(32001);
    v___x_4010_ = lean_nat_to_int(v___x_4009_);
    return v___x_4010_;
}
pub unsafe fn _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15() -> *mut LeanObject
{
    let mut v___x_4011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut LeanObject = core::ptr::null_mut();
    v___x_4011_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__14),
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__14_once),
        _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__14,
    );
    v___x_4012_ = lean_int_neg(v___x_4011_);
    return v___x_4012_;
}
pub unsafe fn _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__16() -> *mut LeanObject
{
    let mut v___x_4013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut LeanObject = core::ptr::null_mut();
    v___x_4013_ = lean_unsigned_to_nat(32801);
    v___x_4014_ = lean_nat_to_int(v___x_4013_);
    return v___x_4014_;
}
pub unsafe fn _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17() -> *mut LeanObject
{
    let mut v___x_4015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut LeanObject = core::ptr::null_mut();
    v___x_4015_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__16),
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__16_once),
        _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__16,
    );
    v___x_4016_ = lean_int_neg(v___x_4015_);
    return v___x_4016_;
}
pub unsafe fn _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__18() -> *mut LeanObject
{
    let mut v___x_4017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: *mut LeanObject = core::ptr::null_mut();
    v___x_4017_ = lean_unsigned_to_nat(32800);
    v___x_4018_ = lean_nat_to_int(v___x_4017_);
    return v___x_4018_;
}
pub unsafe fn _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19() -> *mut LeanObject
{
    let mut v___x_4019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4020_: *mut LeanObject = core::ptr::null_mut();
    v___x_4019_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__18),
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__18_once),
        _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__18,
    );
    v___x_4020_ = lean_int_neg(v___x_4019_);
    return v___x_4020_;
}
pub unsafe fn _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__20() -> *mut LeanObject
{
    let mut v___x_4021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: *mut LeanObject = core::ptr::null_mut();
    v___x_4021_ = lean_unsigned_to_nat(32900);
    v___x_4022_ = lean_nat_to_int(v___x_4021_);
    return v___x_4022_;
}
pub unsafe fn _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21() -> *mut LeanObject
{
    let mut v___x_4023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: *mut LeanObject = core::ptr::null_mut();
    v___x_4023_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__20),
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__20_once),
        _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__20,
    );
    v___x_4024_ = lean_int_neg(v___x_4023_);
    return v___x_4024_;
}
pub unsafe fn _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__22() -> *mut LeanObject
{
    let mut v___x_4025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: *mut LeanObject = core::ptr::null_mut();
    v___x_4025_ = lean_unsigned_to_nat(32901);
    v___x_4026_ = lean_nat_to_int(v___x_4025_);
    return v___x_4026_;
}
pub unsafe fn _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23() -> *mut LeanObject
{
    let mut v___x_4027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4028_: *mut LeanObject = core::ptr::null_mut();
    v___x_4027_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__22),
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__22_once),
        _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__22,
    );
    v___x_4028_ = lean_int_neg(v___x_4027_);
    return v___x_4028_;
}
pub unsafe fn _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__24() -> *mut LeanObject
{
    let mut v___x_4029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut LeanObject = core::ptr::null_mut();
    v___x_4029_ = lean_unsigned_to_nat(32902);
    v___x_4030_ = lean_nat_to_int(v___x_4029_);
    return v___x_4030_;
}
pub unsafe fn _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25() -> *mut LeanObject
{
    let mut v___x_4031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut LeanObject = core::ptr::null_mut();
    v___x_4031_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__24),
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__24_once),
        _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__24,
    );
    v___x_4032_ = lean_int_neg(v___x_4031_);
    return v___x_4032_;
}
pub unsafe fn l_Lean_JsonRpc_instFromJsonErrorCode___lam__0(
    mut v_x_4069_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_4072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mantissa_4073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exponent_4074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: u8 = 0;
    let mut v___x_4077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4078_: u8 = 0;
    let mut v___x_4079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: u8 = 0;
    let mut v___x_4081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: u8 = 0;
    let mut v___x_4083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: u8 = 0;
    let mut v___x_4085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: u8 = 0;
    let mut v___x_4087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: u8 = 0;
    let mut v___x_4089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: u8 = 0;
    let mut v___x_4091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: u8 = 0;
    let mut v___x_4093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: u8 = 0;
    let mut v___x_4095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: u8 = 0;
    let mut v___x_4097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4098_: u8 = 0;
    let mut v___x_4099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: u8 = 0;
    let mut v___x_4101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: u8 = 0;
    let mut v___x_4104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: u8 = 0;
    let mut v___x_4107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: u8 = 0;
    let mut v___x_4110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: u8 = 0;
    let mut v___x_4113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: u8 = 0;
    let mut v___x_4116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: u8 = 0;
    let mut v___x_4119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: u8 = 0;
    let mut v___x_4122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: u8 = 0;
    let mut v___x_4125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: u8 = 0;
    let mut v___x_4128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4130_: u8 = 0;
    let mut v___x_4131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: u8 = 0;
    let mut v___x_4134_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4069_) == 2 {
                    v_n_4072_ = lean_ctor_get(v_x_4069_, 0);
                    v_mantissa_4073_ = lean_ctor_get(v_n_4072_, 0);
                    v_exponent_4074_ = lean_ctor_get(v_n_4072_, 1);
                    v___x_4075_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3_once
                        ),
                        _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3,
                    );
                    v___x_4076_ = lean_int_dec_eq(v_mantissa_4073_, v___x_4075_);
                    if v___x_4076_ == 0 {
                        v___x_4077_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5_once
                            ),
                            _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5,
                        );
                        v___x_4078_ = lean_int_dec_eq(v_mantissa_4073_, v___x_4077_);
                        if v___x_4078_ == 0 {
                            v___x_4079_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7_once
                                ),
                                _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7,
                            );
                            v___x_4080_ = lean_int_dec_eq(v_mantissa_4073_, v___x_4079_);
                            if v___x_4080_ == 0 {
                                v___x_4081_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9), core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9_once), _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9);
                                v___x_4082_ = lean_int_dec_eq(v_mantissa_4073_, v___x_4081_);
                                if v___x_4082_ == 0 {
                                    v___x_4083_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11), core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11_once), _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11);
                                    v___x_4084_ = lean_int_dec_eq(v_mantissa_4073_, v___x_4083_);
                                    if v___x_4084_ == 0 {
                                        v___x_4085_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13), core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13_once), _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13);
                                        v___x_4086_ =
                                            lean_int_dec_eq(v_mantissa_4073_, v___x_4085_);
                                        if v___x_4086_ == 0 {
                                            v___x_4087_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15), core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15_once), _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15);
                                            v___x_4088_ =
                                                lean_int_dec_eq(v_mantissa_4073_, v___x_4087_);
                                            if v___x_4088_ == 0 {
                                                v___x_4089_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17), core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17_once), _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17);
                                                v___x_4090_ =
                                                    lean_int_dec_eq(v_mantissa_4073_, v___x_4089_);
                                                if v___x_4090_ == 0 {
                                                    v___x_4091_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19), core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19_once), _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19);
                                                    v___x_4092_ = lean_int_dec_eq(
                                                        v_mantissa_4073_,
                                                        v___x_4091_,
                                                    );
                                                    if v___x_4092_ == 0 {
                                                        v___x_4093_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21), core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21_once), _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21);
                                                        v___x_4094_ = lean_int_dec_eq(
                                                            v_mantissa_4073_,
                                                            v___x_4093_,
                                                        );
                                                        if v___x_4094_ == 0 {
                                                            v___x_4095_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23), core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23_once), _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23);
                                                            v___x_4096_ = lean_int_dec_eq(
                                                                v_mantissa_4073_,
                                                                v___x_4095_,
                                                            );
                                                            if v___x_4096_ == 0 {
                                                                v___x_4097_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25), core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25_once), _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25);
                                                                v___x_4098_ = lean_int_dec_eq(
                                                                    v_mantissa_4073_,
                                                                    v___x_4097_,
                                                                );
                                                                if v___x_4098_ == 0 {
                                                                    state = 1;
                                                                    continue;
                                                                } else {
                                                                    v___x_4099_ =
                                                                        lean_unsigned_to_nat(0);
                                                                    v___x_4100_ = lean_nat_dec_eq(
                                                                        v_exponent_4074_,
                                                                        v___x_4099_,
                                                                    );
                                                                    if v___x_4100_ == 0 {
                                                                        state = 1;
                                                                        continue;
                                                                    } else {
                                                                        v___x_4101_ = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__26;
                                                                        return v___x_4101_;
                                                                    }
                                                                }
                                                            } else {
                                                                v___x_4102_ =
                                                                    lean_unsigned_to_nat(0);
                                                                v___x_4103_ = lean_nat_dec_eq(
                                                                    v_exponent_4074_,
                                                                    v___x_4102_,
                                                                );
                                                                if v___x_4103_ == 0 {
                                                                    state = 1;
                                                                    continue;
                                                                } else {
                                                                    v___x_4104_ = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__27;
                                                                    return v___x_4104_;
                                                                }
                                                            }
                                                        } else {
                                                            v___x_4105_ = lean_unsigned_to_nat(0);
                                                            v___x_4106_ = lean_nat_dec_eq(
                                                                v_exponent_4074_,
                                                                v___x_4105_,
                                                            );
                                                            if v___x_4106_ == 0 {
                                                                state = 1;
                                                                continue;
                                                            } else {
                                                                v___x_4107_ = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__28;
                                                                return v___x_4107_;
                                                            }
                                                        }
                                                    } else {
                                                        v___x_4108_ = lean_unsigned_to_nat(0);
                                                        v___x_4109_ = lean_nat_dec_eq(
                                                            v_exponent_4074_,
                                                            v___x_4108_,
                                                        );
                                                        if v___x_4109_ == 0 {
                                                            state = 1;
                                                            continue;
                                                        } else {
                                                            v___x_4110_ = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__29;
                                                            return v___x_4110_;
                                                        }
                                                    }
                                                } else {
                                                    v___x_4111_ = lean_unsigned_to_nat(0);
                                                    v___x_4112_ = lean_nat_dec_eq(
                                                        v_exponent_4074_,
                                                        v___x_4111_,
                                                    );
                                                    if v___x_4112_ == 0 {
                                                        state = 1;
                                                        continue;
                                                    } else {
                                                        v___x_4113_ = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__30;
                                                        return v___x_4113_;
                                                    }
                                                }
                                            } else {
                                                v___x_4114_ = lean_unsigned_to_nat(0);
                                                v___x_4115_ =
                                                    lean_nat_dec_eq(v_exponent_4074_, v___x_4114_);
                                                if v___x_4115_ == 0 {
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    v___x_4116_ = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__31;
                                                    return v___x_4116_;
                                                }
                                            }
                                        } else {
                                            v___x_4117_ = lean_unsigned_to_nat(0);
                                            v___x_4118_ =
                                                lean_nat_dec_eq(v_exponent_4074_, v___x_4117_);
                                            if v___x_4118_ == 0 {
                                                state = 1;
                                                continue;
                                            } else {
                                                v___x_4119_ = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__32;
                                                return v___x_4119_;
                                            }
                                        }
                                    } else {
                                        v___x_4120_ = lean_unsigned_to_nat(0);
                                        v___x_4121_ =
                                            lean_nat_dec_eq(v_exponent_4074_, v___x_4120_);
                                        if v___x_4121_ == 0 {
                                            state = 1;
                                            continue;
                                        } else {
                                            v___x_4122_ = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__33;
                                            return v___x_4122_;
                                        }
                                    }
                                } else {
                                    v___x_4123_ = lean_unsigned_to_nat(0);
                                    v___x_4124_ = lean_nat_dec_eq(v_exponent_4074_, v___x_4123_);
                                    if v___x_4124_ == 0 {
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_4125_ = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__34;
                                        return v___x_4125_;
                                    }
                                }
                            } else {
                                v___x_4126_ = lean_unsigned_to_nat(0);
                                v___x_4127_ = lean_nat_dec_eq(v_exponent_4074_, v___x_4126_);
                                if v___x_4127_ == 0 {
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_4128_ =
                                        l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__35;
                                    return v___x_4128_;
                                }
                            }
                        } else {
                            v___x_4129_ = lean_unsigned_to_nat(0);
                            v___x_4130_ = lean_nat_dec_eq(v_exponent_4074_, v___x_4129_);
                            if v___x_4130_ == 0 {
                                state = 1;
                                continue;
                            } else {
                                v___x_4131_ =
                                    l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__36;
                                return v___x_4131_;
                            }
                        }
                    } else {
                        v___x_4132_ = lean_unsigned_to_nat(0);
                        v___x_4133_ = lean_nat_dec_eq(v_exponent_4074_, v___x_4132_);
                        if v___x_4133_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            v___x_4134_ =
                                l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__37;
                            return v___x_4134_;
                        }
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4071_ = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__1;
                return v___x_4071_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___boxed(
    mut v_x_4135_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4136_: *mut LeanObject = core::ptr::null_mut();
    v_res_4136_ = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0(v_x_4135_);
    lean_dec(v_x_4135_);
    return v_res_4136_;
}
pub unsafe fn _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__0() -> *mut LeanObject {
    let mut v___x_4139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4140_: *mut LeanObject = core::ptr::null_mut();
    v___x_4139_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3),
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3_once),
        _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3,
    );
    v___x_4140_ = l_Lean_JsonNumber_fromInt(v___x_4139_);
    return v___x_4140_;
}
pub unsafe fn _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1() -> *mut LeanObject {
    let mut v___x_4141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4142_: *mut LeanObject = core::ptr::null_mut();
    v___x_4141_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__0_once),
        _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__0,
    );
    v___x_4142_ = lean_alloc_ctor(2, 1, (0) as u32);
    lean_ctor_set(v___x_4142_, 0, v___x_4141_);
    return v___x_4142_;
}
pub unsafe fn _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__2() -> *mut LeanObject {
    let mut v___x_4143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: *mut LeanObject = core::ptr::null_mut();
    v___x_4143_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5),
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5_once),
        _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5,
    );
    v___x_4144_ = l_Lean_JsonNumber_fromInt(v___x_4143_);
    return v___x_4144_;
}
pub unsafe fn _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3() -> *mut LeanObject {
    let mut v___x_4145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4146_: *mut LeanObject = core::ptr::null_mut();
    v___x_4145_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__2_once),
        _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__2,
    );
    v___x_4146_ = lean_alloc_ctor(2, 1, (0) as u32);
    lean_ctor_set(v___x_4146_, 0, v___x_4145_);
    return v___x_4146_;
}
pub unsafe fn _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__4() -> *mut LeanObject {
    let mut v___x_4147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4148_: *mut LeanObject = core::ptr::null_mut();
    v___x_4147_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7),
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7_once),
        _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7,
    );
    v___x_4148_ = l_Lean_JsonNumber_fromInt(v___x_4147_);
    return v___x_4148_;
}
pub unsafe fn _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5() -> *mut LeanObject {
    let mut v___x_4149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4150_: *mut LeanObject = core::ptr::null_mut();
    v___x_4149_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__4),
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__4_once),
        _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__4,
    );
    v___x_4150_ = lean_alloc_ctor(2, 1, (0) as u32);
    lean_ctor_set(v___x_4150_, 0, v___x_4149_);
    return v___x_4150_;
}
pub unsafe fn _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__6() -> *mut LeanObject {
    let mut v___x_4151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4152_: *mut LeanObject = core::ptr::null_mut();
    v___x_4151_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9),
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9_once),
        _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9,
    );
    v___x_4152_ = l_Lean_JsonNumber_fromInt(v___x_4151_);
    return v___x_4152_;
}
pub unsafe fn _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7() -> *mut LeanObject {
    let mut v___x_4153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: *mut LeanObject = core::ptr::null_mut();
    v___x_4153_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__6),
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__6_once),
        _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__6,
    );
    v___x_4154_ = lean_alloc_ctor(2, 1, (0) as u32);
    lean_ctor_set(v___x_4154_, 0, v___x_4153_);
    return v___x_4154_;
}
pub unsafe fn _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__8() -> *mut LeanObject {
    let mut v___x_4155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: *mut LeanObject = core::ptr::null_mut();
    v___x_4155_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11),
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11_once),
        _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11,
    );
    v___x_4156_ = l_Lean_JsonNumber_fromInt(v___x_4155_);
    return v___x_4156_;
}
pub unsafe fn _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9() -> *mut LeanObject {
    let mut v___x_4157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: *mut LeanObject = core::ptr::null_mut();
    v___x_4157_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__8),
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__8_once),
        _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__8,
    );
    v___x_4158_ = lean_alloc_ctor(2, 1, (0) as u32);
    lean_ctor_set(v___x_4158_, 0, v___x_4157_);
    return v___x_4158_;
}
pub unsafe fn _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__10() -> *mut LeanObject {
    let mut v___x_4159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut LeanObject = core::ptr::null_mut();
    v___x_4159_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13),
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13_once),
        _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13,
    );
    v___x_4160_ = l_Lean_JsonNumber_fromInt(v___x_4159_);
    return v___x_4160_;
}
pub unsafe fn _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11() -> *mut LeanObject {
    let mut v___x_4161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4162_: *mut LeanObject = core::ptr::null_mut();
    v___x_4161_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__10),
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__10_once),
        _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__10,
    );
    v___x_4162_ = lean_alloc_ctor(2, 1, (0) as u32);
    lean_ctor_set(v___x_4162_, 0, v___x_4161_);
    return v___x_4162_;
}
pub unsafe fn _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__12() -> *mut LeanObject {
    let mut v___x_4163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: *mut LeanObject = core::ptr::null_mut();
    v___x_4163_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15),
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15_once),
        _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15,
    );
    v___x_4164_ = l_Lean_JsonNumber_fromInt(v___x_4163_);
    return v___x_4164_;
}
pub unsafe fn _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13() -> *mut LeanObject {
    let mut v___x_4165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: *mut LeanObject = core::ptr::null_mut();
    v___x_4165_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__12),
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__12_once),
        _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__12,
    );
    v___x_4166_ = lean_alloc_ctor(2, 1, (0) as u32);
    lean_ctor_set(v___x_4166_, 0, v___x_4165_);
    return v___x_4166_;
}
pub unsafe fn _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__14() -> *mut LeanObject {
    let mut v___x_4167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: *mut LeanObject = core::ptr::null_mut();
    v___x_4167_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17),
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17_once),
        _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17,
    );
    v___x_4168_ = l_Lean_JsonNumber_fromInt(v___x_4167_);
    return v___x_4168_;
}
pub unsafe fn _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15() -> *mut LeanObject {
    let mut v___x_4169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: *mut LeanObject = core::ptr::null_mut();
    v___x_4169_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__14),
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__14_once),
        _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__14,
    );
    v___x_4170_ = lean_alloc_ctor(2, 1, (0) as u32);
    lean_ctor_set(v___x_4170_, 0, v___x_4169_);
    return v___x_4170_;
}
pub unsafe fn _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__16() -> *mut LeanObject {
    let mut v___x_4171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4172_: *mut LeanObject = core::ptr::null_mut();
    v___x_4171_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19),
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19_once),
        _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19,
    );
    v___x_4172_ = l_Lean_JsonNumber_fromInt(v___x_4171_);
    return v___x_4172_;
}
pub unsafe fn _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17() -> *mut LeanObject {
    let mut v___x_4173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4174_: *mut LeanObject = core::ptr::null_mut();
    v___x_4173_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__16),
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__16_once),
        _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__16,
    );
    v___x_4174_ = lean_alloc_ctor(2, 1, (0) as u32);
    lean_ctor_set(v___x_4174_, 0, v___x_4173_);
    return v___x_4174_;
}
pub unsafe fn _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__18() -> *mut LeanObject {
    let mut v___x_4175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4176_: *mut LeanObject = core::ptr::null_mut();
    v___x_4175_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21),
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21_once),
        _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21,
    );
    v___x_4176_ = l_Lean_JsonNumber_fromInt(v___x_4175_);
    return v___x_4176_;
}
pub unsafe fn _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19() -> *mut LeanObject {
    let mut v___x_4177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4178_: *mut LeanObject = core::ptr::null_mut();
    v___x_4177_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__18),
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__18_once),
        _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__18,
    );
    v___x_4178_ = lean_alloc_ctor(2, 1, (0) as u32);
    lean_ctor_set(v___x_4178_, 0, v___x_4177_);
    return v___x_4178_;
}
pub unsafe fn _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__20() -> *mut LeanObject {
    let mut v___x_4179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4180_: *mut LeanObject = core::ptr::null_mut();
    v___x_4179_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23),
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23_once),
        _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23,
    );
    v___x_4180_ = l_Lean_JsonNumber_fromInt(v___x_4179_);
    return v___x_4180_;
}
pub unsafe fn _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21() -> *mut LeanObject {
    let mut v___x_4181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4182_: *mut LeanObject = core::ptr::null_mut();
    v___x_4181_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__20),
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__20_once),
        _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__20,
    );
    v___x_4182_ = lean_alloc_ctor(2, 1, (0) as u32);
    lean_ctor_set(v___x_4182_, 0, v___x_4181_);
    return v___x_4182_;
}
pub unsafe fn _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__22() -> *mut LeanObject {
    let mut v___x_4183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: *mut LeanObject = core::ptr::null_mut();
    v___x_4183_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25),
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25_once),
        _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25,
    );
    v___x_4184_ = l_Lean_JsonNumber_fromInt(v___x_4183_);
    return v___x_4184_;
}
pub unsafe fn _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23() -> *mut LeanObject {
    let mut v___x_4185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: *mut LeanObject = core::ptr::null_mut();
    v___x_4185_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__22),
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__22_once),
        _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__22,
    );
    v___x_4186_ = lean_alloc_ctor(2, 1, (0) as u32);
    lean_ctor_set(v___x_4186_, 0, v___x_4185_);
    return v___x_4186_;
}
pub unsafe fn l_Lean_JsonRpc_instToJsonErrorCode___lam__0(mut v_x_4187_: u8) -> *mut LeanObject {
    match v_x_4187_ {
        0 => {
            let mut v___x_4188_: *mut LeanObject = core::ptr::null_mut();
            v___x_4188_ = lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1),
                core::ptr::addr_of_mut!(
                    l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1_once
                ),
                _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1,
            );
            return v___x_4188_;
        }
        1 => {
            let mut v___x_4189_: *mut LeanObject = core::ptr::null_mut();
            v___x_4189_ = lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3),
                core::ptr::addr_of_mut!(
                    l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3_once
                ),
                _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3,
            );
            return v___x_4189_;
        }
        2 => {
            let mut v___x_4190_: *mut LeanObject = core::ptr::null_mut();
            v___x_4190_ = lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5),
                core::ptr::addr_of_mut!(
                    l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5_once
                ),
                _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5,
            );
            return v___x_4190_;
        }
        3 => {
            let mut v___x_4191_: *mut LeanObject = core::ptr::null_mut();
            v___x_4191_ = lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7),
                core::ptr::addr_of_mut!(
                    l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7_once
                ),
                _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7,
            );
            return v___x_4191_;
        }
        4 => {
            let mut v___x_4192_: *mut LeanObject = core::ptr::null_mut();
            v___x_4192_ = lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9),
                core::ptr::addr_of_mut!(
                    l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9_once
                ),
                _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9,
            );
            return v___x_4192_;
        }
        5 => {
            let mut v___x_4193_: *mut LeanObject = core::ptr::null_mut();
            v___x_4193_ = lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11),
                core::ptr::addr_of_mut!(
                    l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11_once
                ),
                _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11,
            );
            return v___x_4193_;
        }
        6 => {
            let mut v___x_4194_: *mut LeanObject = core::ptr::null_mut();
            v___x_4194_ = lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13),
                core::ptr::addr_of_mut!(
                    l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13_once
                ),
                _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13,
            );
            return v___x_4194_;
        }
        7 => {
            let mut v___x_4195_: *mut LeanObject = core::ptr::null_mut();
            v___x_4195_ = lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15),
                core::ptr::addr_of_mut!(
                    l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15_once
                ),
                _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15,
            );
            return v___x_4195_;
        }
        8 => {
            let mut v___x_4196_: *mut LeanObject = core::ptr::null_mut();
            v___x_4196_ = lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17),
                core::ptr::addr_of_mut!(
                    l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17_once
                ),
                _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17,
            );
            return v___x_4196_;
        }
        9 => {
            let mut v___x_4197_: *mut LeanObject = core::ptr::null_mut();
            v___x_4197_ = lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19),
                core::ptr::addr_of_mut!(
                    l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19_once
                ),
                _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19,
            );
            return v___x_4197_;
        }
        10 => {
            let mut v___x_4198_: *mut LeanObject = core::ptr::null_mut();
            v___x_4198_ = lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21),
                core::ptr::addr_of_mut!(
                    l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21_once
                ),
                _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21,
            );
            return v___x_4198_;
        }
        _ => {
            let mut v___x_4199_: *mut LeanObject = core::ptr::null_mut();
            v___x_4199_ = lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23),
                core::ptr::addr_of_mut!(
                    l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23_once
                ),
                _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23,
            );
            return v___x_4199_;
        }
    }
}
pub unsafe fn l_Lean_JsonRpc_instToJsonErrorCode___lam__0___boxed(
    mut v_x_4200_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_474__boxed_4201_: u8 = 0;
    let mut v_res_4202_: *mut LeanObject = core::ptr::null_mut();
    v_x_474__boxed_4201_ = (lean_unbox(v_x_4200_) as u8);
    v_res_4202_ = l_Lean_JsonRpc_instToJsonErrorCode___lam__0(v_x_474__boxed_4201_);
    return v_res_4202_;
}
pub unsafe fn l_Lean_JsonRpc_Message_ctorIdx(mut v_x_4205_: *mut LeanObject) -> *mut LeanObject {
    match lean_obj_tag(v_x_4205_) {
        0 => {
            let mut v___x_4206_: *mut LeanObject = core::ptr::null_mut();
            v___x_4206_ = lean_unsigned_to_nat(0);
            return v___x_4206_;
        }
        1 => {
            let mut v___x_4207_: *mut LeanObject = core::ptr::null_mut();
            v___x_4207_ = lean_unsigned_to_nat(1);
            return v___x_4207_;
        }
        2 => {
            let mut v___x_4208_: *mut LeanObject = core::ptr::null_mut();
            v___x_4208_ = lean_unsigned_to_nat(2);
            return v___x_4208_;
        }
        _ => {
            let mut v___x_4209_: *mut LeanObject = core::ptr::null_mut();
            v___x_4209_ = lean_unsigned_to_nat(3);
            return v___x_4209_;
        }
    }
}
pub unsafe fn l_Lean_JsonRpc_Message_ctorIdx___boxed(
    mut v_x_4210_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4211_: *mut LeanObject = core::ptr::null_mut();
    v_res_4211_ = l_Lean_JsonRpc_Message_ctorIdx(v_x_4210_);
    lean_dec_ref(v_x_4210_);
    return v_res_4211_;
}
pub unsafe fn l_Lean_JsonRpc_Message_ctorElim___redArg(
    mut v_t_4212_: *mut LeanObject,
    mut v_k_4213_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_t_4212_) {
        0 => {
            let mut v_id_4214_: *mut LeanObject = core::ptr::null_mut();
            let mut v_method_4215_: *mut LeanObject = core::ptr::null_mut();
            let mut v_params_x3f_4216_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4217_: *mut LeanObject = core::ptr::null_mut();
            v_id_4214_ = lean_ctor_get(v_t_4212_, 0);
            lean_inc(v_id_4214_);
            v_method_4215_ = lean_ctor_get(v_t_4212_, 1);
            lean_inc_ref(v_method_4215_);
            v_params_x3f_4216_ = lean_ctor_get(v_t_4212_, 2);
            lean_inc(v_params_x3f_4216_);
            lean_dec_ref_known(v_t_4212_, 3);
            v___x_4217_ = lean_apply_3(v_k_4213_, v_id_4214_, v_method_4215_, v_params_x3f_4216_);
            return v___x_4217_;
        }
        1 => {
            let mut v_method_4218_: *mut LeanObject = core::ptr::null_mut();
            let mut v_params_x3f_4219_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4220_: *mut LeanObject = core::ptr::null_mut();
            v_method_4218_ = lean_ctor_get(v_t_4212_, 0);
            lean_inc_ref(v_method_4218_);
            v_params_x3f_4219_ = lean_ctor_get(v_t_4212_, 1);
            lean_inc(v_params_x3f_4219_);
            lean_dec_ref_known(v_t_4212_, 2);
            v___x_4220_ = lean_apply_2(v_k_4213_, v_method_4218_, v_params_x3f_4219_);
            return v___x_4220_;
        }
        2 => {
            let mut v_id_4221_: *mut LeanObject = core::ptr::null_mut();
            let mut v_result_4222_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4223_: *mut LeanObject = core::ptr::null_mut();
            v_id_4221_ = lean_ctor_get(v_t_4212_, 0);
            lean_inc(v_id_4221_);
            v_result_4222_ = lean_ctor_get(v_t_4212_, 1);
            lean_inc(v_result_4222_);
            lean_dec_ref_known(v_t_4212_, 2);
            v___x_4223_ = lean_apply_2(v_k_4213_, v_id_4221_, v_result_4222_);
            return v___x_4223_;
        }
        _ => {
            let mut v_id_4224_: *mut LeanObject = core::ptr::null_mut();
            let mut v_code_4225_: u8 = 0;
            let mut v_message_4226_: *mut LeanObject = core::ptr::null_mut();
            let mut v_data_x3f_4227_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4228_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4229_: *mut LeanObject = core::ptr::null_mut();
            v_id_4224_ = lean_ctor_get(v_t_4212_, 0);
            lean_inc(v_id_4224_);
            v_code_4225_ = lean_ctor_get_uint8(
                v_t_4212_,
                (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
            );
            v_message_4226_ = lean_ctor_get(v_t_4212_, 1);
            lean_inc_ref(v_message_4226_);
            v_data_x3f_4227_ = lean_ctor_get(v_t_4212_, 2);
            lean_inc(v_data_x3f_4227_);
            lean_dec_ref_known(v_t_4212_, 3);
            v___x_4228_ = lean_box((v_code_4225_) as usize);
            v___x_4229_ = lean_apply_4(
                v_k_4213_,
                v_id_4224_,
                v___x_4228_,
                v_message_4226_,
                v_data_x3f_4227_,
            );
            return v___x_4229_;
        }
    }
}
pub unsafe fn l_Lean_JsonRpc_Message_ctorElim(
    mut v_motive_4230_: *mut LeanObject,
    mut v_ctorIdx_4231_: *mut LeanObject,
    mut v_t_4232_: *mut LeanObject,
    mut v_h_4233_: *mut LeanObject,
    mut v_k_4234_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4235_: *mut LeanObject = core::ptr::null_mut();
    v___x_4235_ = l_Lean_JsonRpc_Message_ctorElim___redArg(v_t_4232_, v_k_4234_);
    return v___x_4235_;
}
pub unsafe fn l_Lean_JsonRpc_Message_ctorElim___boxed(
    mut v_motive_4236_: *mut LeanObject,
    mut v_ctorIdx_4237_: *mut LeanObject,
    mut v_t_4238_: *mut LeanObject,
    mut v_h_4239_: *mut LeanObject,
    mut v_k_4240_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4241_: *mut LeanObject = core::ptr::null_mut();
    v_res_4241_ = l_Lean_JsonRpc_Message_ctorElim(
        v_motive_4236_,
        v_ctorIdx_4237_,
        v_t_4238_,
        v_h_4239_,
        v_k_4240_,
    );
    lean_dec(v_ctorIdx_4237_);
    return v_res_4241_;
}
pub unsafe fn l_Lean_JsonRpc_Message_request_elim___redArg(
    mut v_t_4242_: *mut LeanObject,
    mut v_request_4243_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4244_: *mut LeanObject = core::ptr::null_mut();
    v___x_4244_ = l_Lean_JsonRpc_Message_ctorElim___redArg(v_t_4242_, v_request_4243_);
    return v___x_4244_;
}
pub unsafe fn l_Lean_JsonRpc_Message_request_elim(
    mut v_motive_4245_: *mut LeanObject,
    mut v_t_4246_: *mut LeanObject,
    mut v_h_4247_: *mut LeanObject,
    mut v_request_4248_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4249_: *mut LeanObject = core::ptr::null_mut();
    v___x_4249_ = l_Lean_JsonRpc_Message_ctorElim___redArg(v_t_4246_, v_request_4248_);
    return v___x_4249_;
}
pub unsafe fn l_Lean_JsonRpc_Message_notification_elim___redArg(
    mut v_t_4250_: *mut LeanObject,
    mut v_notification_4251_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4252_: *mut LeanObject = core::ptr::null_mut();
    v___x_4252_ = l_Lean_JsonRpc_Message_ctorElim___redArg(v_t_4250_, v_notification_4251_);
    return v___x_4252_;
}
pub unsafe fn l_Lean_JsonRpc_Message_notification_elim(
    mut v_motive_4253_: *mut LeanObject,
    mut v_t_4254_: *mut LeanObject,
    mut v_h_4255_: *mut LeanObject,
    mut v_notification_4256_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4257_: *mut LeanObject = core::ptr::null_mut();
    v___x_4257_ = l_Lean_JsonRpc_Message_ctorElim___redArg(v_t_4254_, v_notification_4256_);
    return v___x_4257_;
}
pub unsafe fn l_Lean_JsonRpc_Message_response_elim___redArg(
    mut v_t_4258_: *mut LeanObject,
    mut v_response_4259_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4260_: *mut LeanObject = core::ptr::null_mut();
    v___x_4260_ = l_Lean_JsonRpc_Message_ctorElim___redArg(v_t_4258_, v_response_4259_);
    return v___x_4260_;
}
pub unsafe fn l_Lean_JsonRpc_Message_response_elim(
    mut v_motive_4261_: *mut LeanObject,
    mut v_t_4262_: *mut LeanObject,
    mut v_h_4263_: *mut LeanObject,
    mut v_response_4264_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4265_: *mut LeanObject = core::ptr::null_mut();
    v___x_4265_ = l_Lean_JsonRpc_Message_ctorElim___redArg(v_t_4262_, v_response_4264_);
    return v___x_4265_;
}
pub unsafe fn l_Lean_JsonRpc_Message_responseError_elim___redArg(
    mut v_t_4266_: *mut LeanObject,
    mut v_responseError_4267_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4268_: *mut LeanObject = core::ptr::null_mut();
    v___x_4268_ = l_Lean_JsonRpc_Message_ctorElim___redArg(v_t_4266_, v_responseError_4267_);
    return v___x_4268_;
}
pub unsafe fn l_Lean_JsonRpc_Message_responseError_elim(
    mut v_motive_4269_: *mut LeanObject,
    mut v_t_4270_: *mut LeanObject,
    mut v_h_4271_: *mut LeanObject,
    mut v_responseError_4272_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4273_: *mut LeanObject = core::ptr::null_mut();
    v___x_4273_ = l_Lean_JsonRpc_Message_ctorElim___redArg(v_t_4270_, v_responseError_4272_);
    return v___x_4273_;
}
pub unsafe fn l_Lean_JsonRpc_instInhabitedRequest_default___redArg(
    mut v_inst_4280_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut LeanObject = core::ptr::null_mut();
    v___x_4281_ = l_Lean_JsonRpc_instInhabitedRequestID_default;
    v___x_4282_ = l_Lean_JsonRpc_instInhabitedRequestID_default___closed__0;
    v___x_4283_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_4283_, 0, v___x_4281_);
    lean_ctor_set(v___x_4283_, 1, v___x_4282_);
    lean_ctor_set(v___x_4283_, 2, v_inst_4280_);
    return v___x_4283_;
}
pub unsafe fn l_Lean_JsonRpc_instInhabitedRequest_default(
    mut v_00_u03b1_4284_: *mut LeanObject,
    mut v_inst_4285_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4286_: *mut LeanObject = core::ptr::null_mut();
    v___x_4286_ = l_Lean_JsonRpc_instInhabitedRequest_default___redArg(v_inst_4285_);
    return v___x_4286_;
}
pub unsafe fn l_Lean_JsonRpc_instInhabitedRequest___redArg(
    mut v_inst_4287_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4288_: *mut LeanObject = core::ptr::null_mut();
    v___x_4288_ = l_Lean_JsonRpc_instInhabitedRequest_default___redArg(v_inst_4287_);
    return v___x_4288_;
}
pub unsafe fn l_Lean_JsonRpc_instInhabitedRequest(
    mut v_a_4289_: *mut LeanObject,
    mut v_inst_4290_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4291_: *mut LeanObject = core::ptr::null_mut();
    v___x_4291_ = l_Lean_JsonRpc_instInhabitedRequest_default___redArg(v_inst_4290_);
    return v___x_4291_;
}
pub unsafe fn l_Lean_JsonRpc_instBEqRequest_beq___redArg(
    mut v_inst_4292_: *mut LeanObject,
    mut v_x_4293_: *mut LeanObject,
    mut v_x_4294_: *mut LeanObject,
) -> u8 {
    let mut v_id_4295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_method_4296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_param_4297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_4298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_method_4299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_param_4300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: u8 = 0;
    v_id_4295_ = lean_ctor_get(v_x_4293_, 0);
    lean_inc(v_id_4295_);
    v_method_4296_ = lean_ctor_get(v_x_4293_, 1);
    lean_inc_ref(v_method_4296_);
    v_param_4297_ = lean_ctor_get(v_x_4293_, 2);
    lean_inc(v_param_4297_);
    lean_dec_ref(v_x_4293_);
    v_id_4298_ = lean_ctor_get(v_x_4294_, 0);
    lean_inc(v_id_4298_);
    v_method_4299_ = lean_ctor_get(v_x_4294_, 1);
    lean_inc_ref(v_method_4299_);
    v_param_4300_ = lean_ctor_get(v_x_4294_, 2);
    lean_inc(v_param_4300_);
    lean_dec_ref(v_x_4294_);
    v___x_4301_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_4295_, v_id_4298_);
    lean_dec(v_id_4298_);
    lean_dec(v_id_4295_);
    if v___x_4301_ == 0 {
        lean_dec(v_param_4300_);
        lean_dec_ref(v_method_4299_);
        lean_dec(v_param_4297_);
        lean_dec_ref(v_method_4296_);
        lean_dec_ref(v_inst_4292_);
        return v___x_4301_;
    } else {
        let mut v___x_4302_: u8 = 0;
        v___x_4302_ = lean_string_dec_eq(v_method_4296_, v_method_4299_);
        lean_dec_ref(v_method_4299_);
        lean_dec_ref(v_method_4296_);
        if v___x_4302_ == 0 {
            lean_dec(v_param_4300_);
            lean_dec(v_param_4297_);
            lean_dec_ref(v_inst_4292_);
            return v___x_4302_;
        } else {
            let mut v___x_4303_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4304_: u8 = 0;
            v___x_4303_ = lean_apply_2(v_inst_4292_, v_param_4297_, v_param_4300_);
            v___x_4304_ = (lean_unbox(v___x_4303_) as u8);
            return v___x_4304_;
        }
    }
}
pub unsafe fn l_Lean_JsonRpc_instBEqRequest_beq___redArg___boxed(
    mut v_inst_4305_: *mut LeanObject,
    mut v_x_4306_: *mut LeanObject,
    mut v_x_4307_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4308_: u8 = 0;
    let mut v_r_4309_: *mut LeanObject = core::ptr::null_mut();
    v_res_4308_ = l_Lean_JsonRpc_instBEqRequest_beq___redArg(v_inst_4305_, v_x_4306_, v_x_4307_);
    v_r_4309_ = lean_box((v_res_4308_) as usize);
    return v_r_4309_;
}
pub unsafe fn l_Lean_JsonRpc_instBEqRequest_beq(
    mut v_00_u03b1_4310_: *mut LeanObject,
    mut v_inst_4311_: *mut LeanObject,
    mut v_x_4312_: *mut LeanObject,
    mut v_x_4313_: *mut LeanObject,
) -> u8 {
    let mut v___x_4314_: u8 = 0;
    v___x_4314_ = l_Lean_JsonRpc_instBEqRequest_beq___redArg(v_inst_4311_, v_x_4312_, v_x_4313_);
    return v___x_4314_;
}
pub unsafe fn l_Lean_JsonRpc_instBEqRequest_beq___boxed(
    mut v_00_u03b1_4315_: *mut LeanObject,
    mut v_inst_4316_: *mut LeanObject,
    mut v_x_4317_: *mut LeanObject,
    mut v_x_4318_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4319_: u8 = 0;
    let mut v_r_4320_: *mut LeanObject = core::ptr::null_mut();
    v_res_4319_ =
        l_Lean_JsonRpc_instBEqRequest_beq(v_00_u03b1_4315_, v_inst_4316_, v_x_4317_, v_x_4318_);
    v_r_4320_ = lean_box((v_res_4319_) as usize);
    return v_r_4320_;
}
pub unsafe fn l_Lean_JsonRpc_instBEqRequest___redArg(
    mut v_inst_4321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4322_: *mut LeanObject = core::ptr::null_mut();
    v___x_4322_ = lean_alloc_closure(
        l_Lean_JsonRpc_instBEqRequest_beq___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___x_4322_, 0, lean_box(0));
    lean_closure_set(v___x_4322_, 1, v_inst_4321_);
    return v___x_4322_;
}
pub unsafe fn l_Lean_JsonRpc_instBEqRequest(
    mut v_00_u03b1_4323_: *mut LeanObject,
    mut v_inst_4324_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4325_: *mut LeanObject = core::ptr::null_mut();
    v___x_4325_ = lean_alloc_closure(
        l_Lean_JsonRpc_instBEqRequest_beq___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___x_4325_, 0, lean_box(0));
    lean_closure_set(v___x_4325_, 1, v_inst_4324_);
    return v___x_4325_;
}
pub unsafe fn l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson___redArg___lam__0(
    mut v_inst_4326_: *mut LeanObject,
    mut v_r_4327_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_id_4328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_method_4329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_param_4330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4333_: u8 = 0;
    let mut v___x_4334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4342_: u8 = 0;
    let mut v___x_4344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4349_: u8 = 0;
    let mut v_isSharedCheck_4350_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_4328_ = lean_ctor_get(v_r_4327_, 0);
                v_method_4329_ = lean_ctor_get(v_r_4327_, 1);
                v_param_4330_ = lean_ctor_get(v_r_4327_, 2);
                v_isSharedCheck_4350_ = (!lean_is_exclusive(v_r_4327_)) as u8;
                if v_isSharedCheck_4350_ == 0 {
                    v___x_4332_ = v_r_4327_;
                    v_isShared_4333_ = v_isSharedCheck_4350_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_param_4330_);
                    lean_inc(v_method_4329_);
                    lean_inc(v_id_4328_);
                    lean_dec(v_r_4327_);
                    v___x_4332_ = lean_box(0);
                    v_isShared_4333_ = v_isSharedCheck_4350_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4334_ = l_Lean_Json_toStructured_x3f___redArg(v_inst_4326_, v_param_4330_);
                if lean_obj_tag(v___x_4334_) == 0 {
                    lean_dec_ref_known(v___x_4334_, 1);
                    v___x_4335_ = lean_box(0);
                    if v_isShared_4333_ == 0 {
                        lean_ctor_set(v___x_4332_, 2, v___x_4335_);
                        v___x_4337_ = v___x_4332_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4338_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4338_, 0, v_id_4328_);
                        lean_ctor_set(v_reuseFailAlloc_4338_, 1, v_method_4329_);
                        lean_ctor_set(v_reuseFailAlloc_4338_, 2, v___x_4335_);
                        v___x_4337_ = v_reuseFailAlloc_4338_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_4339_ = lean_ctor_get(v___x_4334_, 0);
                    v_isSharedCheck_4349_ = (!lean_is_exclusive(v___x_4334_)) as u8;
                    if v_isSharedCheck_4349_ == 0 {
                        v___x_4341_ = v___x_4334_;
                        v_isShared_4342_ = v_isSharedCheck_4349_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4339_);
                        lean_dec(v___x_4334_);
                        v___x_4341_ = lean_box(0);
                        v_isShared_4342_ = v_isSharedCheck_4349_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4337_;
            }
            3 => {
                if v_isShared_4342_ == 0 {
                    v___x_4344_ = v___x_4341_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4348_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4348_, 0, v_a_4339_);
                    v___x_4344_ = v_reuseFailAlloc_4348_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4333_ == 0 {
                    lean_ctor_set(v___x_4332_, 2, v___x_4344_);
                    v___x_4346_ = v___x_4332_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4347_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4347_, 0, v_id_4328_);
                    lean_ctor_set(v_reuseFailAlloc_4347_, 1, v_method_4329_);
                    lean_ctor_set(v_reuseFailAlloc_4347_, 2, v___x_4344_);
                    v___x_4346_ = v_reuseFailAlloc_4347_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4346_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson___redArg(
    mut v_inst_4351_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4352_: *mut LeanObject = core::ptr::null_mut();
    v___f_4352_ = lean_alloc_closure(
        l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_4352_, 0, v_inst_4351_);
    return v___f_4352_;
}
pub unsafe fn l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson(
    mut v_00_u03b1_4353_: *mut LeanObject,
    mut v_inst_4354_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4355_: *mut LeanObject = core::ptr::null_mut();
    v___f_4355_ = lean_alloc_closure(
        l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_4355_, 0, v_inst_4354_);
    return v___f_4355_;
}
pub unsafe fn l_Option_toJson___at___00Lean_JsonRpc_Request_ofMessage_x3f_spec__0(
    mut v_x_4356_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_4356_) == 0 {
        let mut v___x_4357_: *mut LeanObject = core::ptr::null_mut();
        v___x_4357_ = lean_box(0);
        return v___x_4357_;
    } else {
        let mut v_val_4358_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4359_: *mut LeanObject = core::ptr::null_mut();
        v_val_4358_ = lean_ctor_get(v_x_4356_, 0);
        lean_inc(v_val_4358_);
        lean_dec_ref_known(v_x_4356_, 1);
        v___x_4359_ = l_Lean_Json_Structured_toJson(v_val_4358_);
        return v___x_4359_;
    }
}
pub unsafe fn l_Lean_JsonRpc_Request_ofMessage_x3f(
    mut v_x_4360_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_id_4361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_method_4362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_x3f_4363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4366_: u8 = 0;
    let mut v___x_4367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4372_: u8 = 0;
    let mut v___x_4373_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4360_) == 0 {
                    v_id_4361_ = lean_ctor_get(v_x_4360_, 0);
                    v_method_4362_ = lean_ctor_get(v_x_4360_, 1);
                    v_params_x3f_4363_ = lean_ctor_get(v_x_4360_, 2);
                    v_isSharedCheck_4372_ = (!lean_is_exclusive(v_x_4360_)) as u8;
                    if v_isSharedCheck_4372_ == 0 {
                        v___x_4365_ = v_x_4360_;
                        v_isShared_4366_ = v_isSharedCheck_4372_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_params_x3f_4363_);
                        lean_inc(v_method_4362_);
                        lean_inc(v_id_4361_);
                        lean_dec(v_x_4360_);
                        v___x_4365_ = lean_box(0);
                        v_isShared_4366_ = v_isSharedCheck_4372_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_x_4360_);
                    v___x_4373_ = lean_box(0);
                    return v___x_4373_;
                }
            }
            1 => {
                v___x_4367_ = l_Option_toJson___at___00Lean_JsonRpc_Request_ofMessage_x3f_spec__0(
                    v_params_x3f_4363_,
                );
                if v_isShared_4366_ == 0 {
                    lean_ctor_set(v___x_4365_, 2, v___x_4367_);
                    v___x_4369_ = v___x_4365_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4371_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4371_, 0, v_id_4361_);
                    lean_ctor_set(v_reuseFailAlloc_4371_, 1, v_method_4362_);
                    lean_ctor_set(v_reuseFailAlloc_4371_, 2, v___x_4367_);
                    v___x_4369_ = v_reuseFailAlloc_4371_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4370_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4370_, 0, v___x_4369_);
                return v___x_4370_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_JsonRpc_instInhabitedNotification_default___redArg(
    mut v_inst_4374_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: *mut LeanObject = core::ptr::null_mut();
    v___x_4375_ = l_Lean_JsonRpc_instInhabitedRequestID_default___closed__0;
    v___x_4376_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4376_, 0, v___x_4375_);
    lean_ctor_set(v___x_4376_, 1, v_inst_4374_);
    return v___x_4376_;
}
pub unsafe fn l_Lean_JsonRpc_instInhabitedNotification_default(
    mut v_00_u03b1_4377_: *mut LeanObject,
    mut v_inst_4378_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4379_: *mut LeanObject = core::ptr::null_mut();
    v___x_4379_ = l_Lean_JsonRpc_instInhabitedNotification_default___redArg(v_inst_4378_);
    return v___x_4379_;
}
pub unsafe fn l_Lean_JsonRpc_instInhabitedNotification___redArg(
    mut v_inst_4380_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4381_: *mut LeanObject = core::ptr::null_mut();
    v___x_4381_ = l_Lean_JsonRpc_instInhabitedNotification_default___redArg(v_inst_4380_);
    return v___x_4381_;
}
pub unsafe fn l_Lean_JsonRpc_instInhabitedNotification(
    mut v_a_4382_: *mut LeanObject,
    mut v_inst_4383_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4384_: *mut LeanObject = core::ptr::null_mut();
    v___x_4384_ = l_Lean_JsonRpc_instInhabitedNotification_default___redArg(v_inst_4383_);
    return v___x_4384_;
}
pub unsafe fn l_Lean_JsonRpc_instBEqNotification_beq___redArg(
    mut v_inst_4385_: *mut LeanObject,
    mut v_x_4386_: *mut LeanObject,
    mut v_x_4387_: *mut LeanObject,
) -> u8 {
    let mut v_method_4388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_param_4389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_method_4390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_param_4391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4392_: u8 = 0;
    v_method_4388_ = lean_ctor_get(v_x_4386_, 0);
    lean_inc_ref(v_method_4388_);
    v_param_4389_ = lean_ctor_get(v_x_4386_, 1);
    lean_inc(v_param_4389_);
    lean_dec_ref(v_x_4386_);
    v_method_4390_ = lean_ctor_get(v_x_4387_, 0);
    lean_inc_ref(v_method_4390_);
    v_param_4391_ = lean_ctor_get(v_x_4387_, 1);
    lean_inc(v_param_4391_);
    lean_dec_ref(v_x_4387_);
    v___x_4392_ = lean_string_dec_eq(v_method_4388_, v_method_4390_);
    lean_dec_ref(v_method_4390_);
    lean_dec_ref(v_method_4388_);
    if v___x_4392_ == 0 {
        lean_dec(v_param_4391_);
        lean_dec(v_param_4389_);
        lean_dec_ref(v_inst_4385_);
        return v___x_4392_;
    } else {
        let mut v___x_4393_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4394_: u8 = 0;
        v___x_4393_ = lean_apply_2(v_inst_4385_, v_param_4389_, v_param_4391_);
        v___x_4394_ = (lean_unbox(v___x_4393_) as u8);
        return v___x_4394_;
    }
}
pub unsafe fn l_Lean_JsonRpc_instBEqNotification_beq___redArg___boxed(
    mut v_inst_4395_: *mut LeanObject,
    mut v_x_4396_: *mut LeanObject,
    mut v_x_4397_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4398_: u8 = 0;
    let mut v_r_4399_: *mut LeanObject = core::ptr::null_mut();
    v_res_4398_ =
        l_Lean_JsonRpc_instBEqNotification_beq___redArg(v_inst_4395_, v_x_4396_, v_x_4397_);
    v_r_4399_ = lean_box((v_res_4398_) as usize);
    return v_r_4399_;
}
pub unsafe fn l_Lean_JsonRpc_instBEqNotification_beq(
    mut v_00_u03b1_4400_: *mut LeanObject,
    mut v_inst_4401_: *mut LeanObject,
    mut v_x_4402_: *mut LeanObject,
    mut v_x_4403_: *mut LeanObject,
) -> u8 {
    let mut v___x_4404_: u8 = 0;
    v___x_4404_ =
        l_Lean_JsonRpc_instBEqNotification_beq___redArg(v_inst_4401_, v_x_4402_, v_x_4403_);
    return v___x_4404_;
}
pub unsafe fn l_Lean_JsonRpc_instBEqNotification_beq___boxed(
    mut v_00_u03b1_4405_: *mut LeanObject,
    mut v_inst_4406_: *mut LeanObject,
    mut v_x_4407_: *mut LeanObject,
    mut v_x_4408_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4409_: u8 = 0;
    let mut v_r_4410_: *mut LeanObject = core::ptr::null_mut();
    v_res_4409_ = l_Lean_JsonRpc_instBEqNotification_beq(
        v_00_u03b1_4405_,
        v_inst_4406_,
        v_x_4407_,
        v_x_4408_,
    );
    v_r_4410_ = lean_box((v_res_4409_) as usize);
    return v_r_4410_;
}
pub unsafe fn l_Lean_JsonRpc_instBEqNotification___redArg(
    mut v_inst_4411_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4412_: *mut LeanObject = core::ptr::null_mut();
    v___x_4412_ = lean_alloc_closure(
        l_Lean_JsonRpc_instBEqNotification_beq___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___x_4412_, 0, lean_box(0));
    lean_closure_set(v___x_4412_, 1, v_inst_4411_);
    return v___x_4412_;
}
pub unsafe fn l_Lean_JsonRpc_instBEqNotification(
    mut v_00_u03b1_4413_: *mut LeanObject,
    mut v_inst_4414_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4415_: *mut LeanObject = core::ptr::null_mut();
    v___x_4415_ = lean_alloc_closure(
        l_Lean_JsonRpc_instBEqNotification_beq___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___x_4415_, 0, lean_box(0));
    lean_closure_set(v___x_4415_, 1, v_inst_4414_);
    return v___x_4415_;
}
pub unsafe fn l_Lean_JsonRpc_instCoeOutNotificationMessageOfToJson___redArg___lam__0(
    mut v_inst_4416_: *mut LeanObject,
    mut v_r_4417_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_method_4418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_param_4419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4422_: u8 = 0;
    let mut v___x_4423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4431_: u8 = 0;
    let mut v___x_4433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4438_: u8 = 0;
    let mut v_isSharedCheck_4439_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_method_4418_ = lean_ctor_get(v_r_4417_, 0);
                v_param_4419_ = lean_ctor_get(v_r_4417_, 1);
                v_isSharedCheck_4439_ = (!lean_is_exclusive(v_r_4417_)) as u8;
                if v_isSharedCheck_4439_ == 0 {
                    v___x_4421_ = v_r_4417_;
                    v_isShared_4422_ = v_isSharedCheck_4439_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_param_4419_);
                    lean_inc(v_method_4418_);
                    lean_dec(v_r_4417_);
                    v___x_4421_ = lean_box(0);
                    v_isShared_4422_ = v_isSharedCheck_4439_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4423_ = l_Lean_Json_toStructured_x3f___redArg(v_inst_4416_, v_param_4419_);
                if lean_obj_tag(v___x_4423_) == 0 {
                    lean_dec_ref_known(v___x_4423_, 1);
                    v___x_4424_ = lean_box(0);
                    if v_isShared_4422_ == 0 {
                        lean_ctor_set_tag(v___x_4421_, 1);
                        lean_ctor_set(v___x_4421_, 1, v___x_4424_);
                        v___x_4426_ = v___x_4421_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4427_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4427_, 0, v_method_4418_);
                        lean_ctor_set(v_reuseFailAlloc_4427_, 1, v___x_4424_);
                        v___x_4426_ = v_reuseFailAlloc_4427_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_4428_ = lean_ctor_get(v___x_4423_, 0);
                    v_isSharedCheck_4438_ = (!lean_is_exclusive(v___x_4423_)) as u8;
                    if v_isSharedCheck_4438_ == 0 {
                        v___x_4430_ = v___x_4423_;
                        v_isShared_4431_ = v_isSharedCheck_4438_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4428_);
                        lean_dec(v___x_4423_);
                        v___x_4430_ = lean_box(0);
                        v_isShared_4431_ = v_isSharedCheck_4438_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4426_;
            }
            3 => {
                if v_isShared_4431_ == 0 {
                    v___x_4433_ = v___x_4430_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4437_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4437_, 0, v_a_4428_);
                    v___x_4433_ = v_reuseFailAlloc_4437_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4422_ == 0 {
                    lean_ctor_set_tag(v___x_4421_, 1);
                    lean_ctor_set(v___x_4421_, 1, v___x_4433_);
                    v___x_4435_ = v___x_4421_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4436_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4436_, 0, v_method_4418_);
                    lean_ctor_set(v_reuseFailAlloc_4436_, 1, v___x_4433_);
                    v___x_4435_ = v_reuseFailAlloc_4436_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4435_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_JsonRpc_instCoeOutNotificationMessageOfToJson___redArg(
    mut v_inst_4440_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4441_: *mut LeanObject = core::ptr::null_mut();
    v___f_4441_ = lean_alloc_closure(
        l_Lean_JsonRpc_instCoeOutNotificationMessageOfToJson___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_4441_, 0, v_inst_4440_);
    return v___f_4441_;
}
pub unsafe fn l_Lean_JsonRpc_instCoeOutNotificationMessageOfToJson(
    mut v_00_u03b1_4442_: *mut LeanObject,
    mut v_inst_4443_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4444_: *mut LeanObject = core::ptr::null_mut();
    v___f_4444_ = lean_alloc_closure(
        l_Lean_JsonRpc_instCoeOutNotificationMessageOfToJson___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_4444_, 0, v_inst_4443_);
    return v___f_4444_;
}
pub unsafe fn l_Lean_JsonRpc_Notification_ofMessage_x3f(
    mut v_x_4445_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_method_4446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_x3f_4447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4450_: u8 = 0;
    let mut v___x_4451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4456_: u8 = 0;
    let mut v___x_4457_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4445_) == 1 {
                    v_method_4446_ = lean_ctor_get(v_x_4445_, 0);
                    v_params_x3f_4447_ = lean_ctor_get(v_x_4445_, 1);
                    v_isSharedCheck_4456_ = (!lean_is_exclusive(v_x_4445_)) as u8;
                    if v_isSharedCheck_4456_ == 0 {
                        v___x_4449_ = v_x_4445_;
                        v_isShared_4450_ = v_isSharedCheck_4456_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_params_x3f_4447_);
                        lean_inc(v_method_4446_);
                        lean_dec(v_x_4445_);
                        v___x_4449_ = lean_box(0);
                        v_isShared_4450_ = v_isSharedCheck_4456_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_x_4445_);
                    v___x_4457_ = lean_box(0);
                    return v___x_4457_;
                }
            }
            1 => {
                v___x_4451_ = l_Option_toJson___at___00Lean_JsonRpc_Request_ofMessage_x3f_spec__0(
                    v_params_x3f_4447_,
                );
                if v_isShared_4450_ == 0 {
                    lean_ctor_set_tag(v___x_4449_, 0);
                    lean_ctor_set(v___x_4449_, 1, v___x_4451_);
                    v___x_4453_ = v___x_4449_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4455_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4455_, 0, v_method_4446_);
                    lean_ctor_set(v_reuseFailAlloc_4455_, 1, v___x_4451_);
                    v___x_4453_ = v_reuseFailAlloc_4455_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4454_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4454_, 0, v___x_4453_);
                return v___x_4454_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_JsonRpc_instInhabitedResponse_default___redArg(
    mut v_inst_4458_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: *mut LeanObject = core::ptr::null_mut();
    v___x_4459_ = l_Lean_JsonRpc_instInhabitedRequestID_default;
    v___x_4460_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4460_, 0, v___x_4459_);
    lean_ctor_set(v___x_4460_, 1, v_inst_4458_);
    return v___x_4460_;
}
pub unsafe fn l_Lean_JsonRpc_instInhabitedResponse_default(
    mut v_00_u03b1_4461_: *mut LeanObject,
    mut v_inst_4462_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4463_: *mut LeanObject = core::ptr::null_mut();
    v___x_4463_ = l_Lean_JsonRpc_instInhabitedResponse_default___redArg(v_inst_4462_);
    return v___x_4463_;
}
pub unsafe fn l_Lean_JsonRpc_instInhabitedResponse___redArg(
    mut v_inst_4464_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4465_: *mut LeanObject = core::ptr::null_mut();
    v___x_4465_ = l_Lean_JsonRpc_instInhabitedResponse_default___redArg(v_inst_4464_);
    return v___x_4465_;
}
pub unsafe fn l_Lean_JsonRpc_instInhabitedResponse(
    mut v_a_4466_: *mut LeanObject,
    mut v_inst_4467_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4468_: *mut LeanObject = core::ptr::null_mut();
    v___x_4468_ = l_Lean_JsonRpc_instInhabitedResponse_default___redArg(v_inst_4467_);
    return v___x_4468_;
}
pub unsafe fn l_Lean_JsonRpc_instBEqResponse_beq___redArg(
    mut v_inst_4469_: *mut LeanObject,
    mut v_x_4470_: *mut LeanObject,
    mut v_x_4471_: *mut LeanObject,
) -> u8 {
    let mut v_id_4472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_result_4473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_4474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_result_4475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4476_: u8 = 0;
    v_id_4472_ = lean_ctor_get(v_x_4470_, 0);
    lean_inc(v_id_4472_);
    v_result_4473_ = lean_ctor_get(v_x_4470_, 1);
    lean_inc(v_result_4473_);
    lean_dec_ref(v_x_4470_);
    v_id_4474_ = lean_ctor_get(v_x_4471_, 0);
    lean_inc(v_id_4474_);
    v_result_4475_ = lean_ctor_get(v_x_4471_, 1);
    lean_inc(v_result_4475_);
    lean_dec_ref(v_x_4471_);
    v___x_4476_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_4472_, v_id_4474_);
    lean_dec(v_id_4474_);
    lean_dec(v_id_4472_);
    if v___x_4476_ == 0 {
        lean_dec(v_result_4475_);
        lean_dec(v_result_4473_);
        lean_dec_ref(v_inst_4469_);
        return v___x_4476_;
    } else {
        let mut v___x_4477_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4478_: u8 = 0;
        v___x_4477_ = lean_apply_2(v_inst_4469_, v_result_4473_, v_result_4475_);
        v___x_4478_ = (lean_unbox(v___x_4477_) as u8);
        return v___x_4478_;
    }
}
pub unsafe fn l_Lean_JsonRpc_instBEqResponse_beq___redArg___boxed(
    mut v_inst_4479_: *mut LeanObject,
    mut v_x_4480_: *mut LeanObject,
    mut v_x_4481_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4482_: u8 = 0;
    let mut v_r_4483_: *mut LeanObject = core::ptr::null_mut();
    v_res_4482_ = l_Lean_JsonRpc_instBEqResponse_beq___redArg(v_inst_4479_, v_x_4480_, v_x_4481_);
    v_r_4483_ = lean_box((v_res_4482_) as usize);
    return v_r_4483_;
}
pub unsafe fn l_Lean_JsonRpc_instBEqResponse_beq(
    mut v_00_u03b1_4484_: *mut LeanObject,
    mut v_inst_4485_: *mut LeanObject,
    mut v_x_4486_: *mut LeanObject,
    mut v_x_4487_: *mut LeanObject,
) -> u8 {
    let mut v___x_4488_: u8 = 0;
    v___x_4488_ = l_Lean_JsonRpc_instBEqResponse_beq___redArg(v_inst_4485_, v_x_4486_, v_x_4487_);
    return v___x_4488_;
}
pub unsafe fn l_Lean_JsonRpc_instBEqResponse_beq___boxed(
    mut v_00_u03b1_4489_: *mut LeanObject,
    mut v_inst_4490_: *mut LeanObject,
    mut v_x_4491_: *mut LeanObject,
    mut v_x_4492_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4493_: u8 = 0;
    let mut v_r_4494_: *mut LeanObject = core::ptr::null_mut();
    v_res_4493_ =
        l_Lean_JsonRpc_instBEqResponse_beq(v_00_u03b1_4489_, v_inst_4490_, v_x_4491_, v_x_4492_);
    v_r_4494_ = lean_box((v_res_4493_) as usize);
    return v_r_4494_;
}
pub unsafe fn l_Lean_JsonRpc_instBEqResponse___redArg(
    mut v_inst_4495_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4496_: *mut LeanObject = core::ptr::null_mut();
    v___x_4496_ = lean_alloc_closure(
        l_Lean_JsonRpc_instBEqResponse_beq___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___x_4496_, 0, lean_box(0));
    lean_closure_set(v___x_4496_, 1, v_inst_4495_);
    return v___x_4496_;
}
pub unsafe fn l_Lean_JsonRpc_instBEqResponse(
    mut v_00_u03b1_4497_: *mut LeanObject,
    mut v_inst_4498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4499_: *mut LeanObject = core::ptr::null_mut();
    v___x_4499_ = lean_alloc_closure(
        l_Lean_JsonRpc_instBEqResponse_beq___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___x_4499_, 0, lean_box(0));
    lean_closure_set(v___x_4499_, 1, v_inst_4498_);
    return v___x_4499_;
}
pub unsafe fn l_Lean_JsonRpc_instCoeOutResponseMessageOfToJson___redArg___lam__0(
    mut v_inst_4500_: *mut LeanObject,
    mut v_r_4501_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_id_4502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_result_4503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4506_: u8 = 0;
    let mut v___x_4507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4511_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_4502_ = lean_ctor_get(v_r_4501_, 0);
                v_result_4503_ = lean_ctor_get(v_r_4501_, 1);
                v_isSharedCheck_4511_ = (!lean_is_exclusive(v_r_4501_)) as u8;
                if v_isSharedCheck_4511_ == 0 {
                    v___x_4505_ = v_r_4501_;
                    v_isShared_4506_ = v_isSharedCheck_4511_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_result_4503_);
                    lean_inc(v_id_4502_);
                    lean_dec(v_r_4501_);
                    v___x_4505_ = lean_box(0);
                    v_isShared_4506_ = v_isSharedCheck_4511_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4507_ = lean_apply_1(v_inst_4500_, v_result_4503_);
                if v_isShared_4506_ == 0 {
                    lean_ctor_set_tag(v___x_4505_, 2);
                    lean_ctor_set(v___x_4505_, 1, v___x_4507_);
                    v___x_4509_ = v___x_4505_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4510_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4510_, 0, v_id_4502_);
                    lean_ctor_set(v_reuseFailAlloc_4510_, 1, v___x_4507_);
                    v___x_4509_ = v_reuseFailAlloc_4510_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4509_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_JsonRpc_instCoeOutResponseMessageOfToJson___redArg(
    mut v_inst_4512_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4513_: *mut LeanObject = core::ptr::null_mut();
    v___f_4513_ = lean_alloc_closure(
        l_Lean_JsonRpc_instCoeOutResponseMessageOfToJson___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_4513_, 0, v_inst_4512_);
    return v___f_4513_;
}
pub unsafe fn l_Lean_JsonRpc_instCoeOutResponseMessageOfToJson(
    mut v_00_u03b1_4514_: *mut LeanObject,
    mut v_inst_4515_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4516_: *mut LeanObject = core::ptr::null_mut();
    v___f_4516_ = lean_alloc_closure(
        l_Lean_JsonRpc_instCoeOutResponseMessageOfToJson___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_4516_, 0, v_inst_4515_);
    return v___f_4516_;
}
pub unsafe fn l_Lean_JsonRpc_Response_ofMessage_x3f(
    mut v_x_4517_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_id_4518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_result_4519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4522_: u8 = 0;
    let mut v___x_4524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4527_: u8 = 0;
    let mut v___x_4528_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4517_) == 2 {
                    v_id_4518_ = lean_ctor_get(v_x_4517_, 0);
                    v_result_4519_ = lean_ctor_get(v_x_4517_, 1);
                    v_isSharedCheck_4527_ = (!lean_is_exclusive(v_x_4517_)) as u8;
                    if v_isSharedCheck_4527_ == 0 {
                        v___x_4521_ = v_x_4517_;
                        v_isShared_4522_ = v_isSharedCheck_4527_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_result_4519_);
                        lean_inc(v_id_4518_);
                        lean_dec(v_x_4517_);
                        v___x_4521_ = lean_box(0);
                        v_isShared_4522_ = v_isSharedCheck_4527_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_x_4517_);
                    v___x_4528_ = lean_box(0);
                    return v___x_4528_;
                }
            }
            1 => {
                if v_isShared_4522_ == 0 {
                    lean_ctor_set_tag(v___x_4521_, 0);
                    v___x_4524_ = v___x_4521_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4526_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4526_, 0, v_id_4518_);
                    lean_ctor_set(v_reuseFailAlloc_4526_, 1, v_result_4519_);
                    v___x_4524_ = v_reuseFailAlloc_4526_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4525_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4525_, 0, v___x_4524_);
                return v___x_4525_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_JsonRpc_instInhabitedResponseError_default(
    mut v_00_u03b1_4534_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4535_: *mut LeanObject = core::ptr::null_mut();
    v___x_4535_ = l_Lean_JsonRpc_instInhabitedResponseError_default___closed__0;
    return v___x_4535_;
}
pub unsafe fn _init_l_Lean_JsonRpc_instInhabitedResponseError___closed__0() -> *mut LeanObject {
    let mut v___x_4536_: *mut LeanObject = core::ptr::null_mut();
    v___x_4536_ = l_Lean_JsonRpc_instInhabitedResponseError_default(lean_box(0));
    return v___x_4536_;
}
pub unsafe fn l_Lean_JsonRpc_instInhabitedResponseError(
    mut v_a_4537_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4538_: *mut LeanObject = core::ptr::null_mut();
    v___x_4538_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instInhabitedResponseError___closed__0),
        core::ptr::addr_of_mut!(l_Lean_JsonRpc_instInhabitedResponseError___closed__0_once),
        _init_l_Lean_JsonRpc_instInhabitedResponseError___closed__0,
    );
    return v___x_4538_;
}
pub unsafe fn l_Lean_JsonRpc_instBEqResponseError_beq___redArg(
    mut v_inst_4539_: *mut LeanObject,
    mut v_x_4540_: *mut LeanObject,
    mut v_x_4541_: *mut LeanObject,
) -> u8 {
    let mut v_id_4542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_4543_: u8 = 0;
    let mut v_message_4544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_x3f_4545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_4546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_4547_: u8 = 0;
    let mut v_message_4548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_x3f_4549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4550_: u8 = 0;
    v_id_4542_ = lean_ctor_get(v_x_4540_, 0);
    lean_inc(v_id_4542_);
    v_code_4543_ = lean_ctor_get_uint8(
        v_x_4540_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
    );
    v_message_4544_ = lean_ctor_get(v_x_4540_, 1);
    lean_inc_ref(v_message_4544_);
    v_data_x3f_4545_ = lean_ctor_get(v_x_4540_, 2);
    lean_inc(v_data_x3f_4545_);
    lean_dec_ref(v_x_4540_);
    v_id_4546_ = lean_ctor_get(v_x_4541_, 0);
    lean_inc(v_id_4546_);
    v_code_4547_ = lean_ctor_get_uint8(
        v_x_4541_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
    );
    v_message_4548_ = lean_ctor_get(v_x_4541_, 1);
    lean_inc_ref(v_message_4548_);
    v_data_x3f_4549_ = lean_ctor_get(v_x_4541_, 2);
    lean_inc(v_data_x3f_4549_);
    lean_dec_ref(v_x_4541_);
    v___x_4550_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_4542_, v_id_4546_);
    lean_dec(v_id_4546_);
    lean_dec(v_id_4542_);
    if v___x_4550_ == 0 {
        lean_dec(v_data_x3f_4549_);
        lean_dec_ref(v_message_4548_);
        lean_dec(v_data_x3f_4545_);
        lean_dec_ref(v_message_4544_);
        lean_dec_ref(v_inst_4539_);
        return v___x_4550_;
    } else {
        let mut v___x_4551_: u8 = 0;
        v___x_4551_ = l_Lean_JsonRpc_instBEqErrorCode_beq(v_code_4543_, v_code_4547_);
        if v___x_4551_ == 0 {
            lean_dec(v_data_x3f_4549_);
            lean_dec_ref(v_message_4548_);
            lean_dec(v_data_x3f_4545_);
            lean_dec_ref(v_message_4544_);
            lean_dec_ref(v_inst_4539_);
            return v___x_4551_;
        } else {
            let mut v___x_4552_: u8 = 0;
            v___x_4552_ = lean_string_dec_eq(v_message_4544_, v_message_4548_);
            lean_dec_ref(v_message_4548_);
            lean_dec_ref(v_message_4544_);
            if v___x_4552_ == 0 {
                lean_dec(v_data_x3f_4549_);
                lean_dec(v_data_x3f_4545_);
                lean_dec_ref(v_inst_4539_);
                return v___x_4552_;
            } else {
                let mut v___x_4553_: u8 = 0;
                v___x_4553_ =
                    l_Option_instBEq_beq___redArg(v_inst_4539_, v_data_x3f_4545_, v_data_x3f_4549_);
                return v___x_4553_;
            }
        }
    }
}
pub unsafe fn l_Lean_JsonRpc_instBEqResponseError_beq___redArg___boxed(
    mut v_inst_4554_: *mut LeanObject,
    mut v_x_4555_: *mut LeanObject,
    mut v_x_4556_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4557_: u8 = 0;
    let mut v_r_4558_: *mut LeanObject = core::ptr::null_mut();
    v_res_4557_ =
        l_Lean_JsonRpc_instBEqResponseError_beq___redArg(v_inst_4554_, v_x_4555_, v_x_4556_);
    v_r_4558_ = lean_box((v_res_4557_) as usize);
    return v_r_4558_;
}
pub unsafe fn l_Lean_JsonRpc_instBEqResponseError_beq(
    mut v_00_u03b1_4559_: *mut LeanObject,
    mut v_inst_4560_: *mut LeanObject,
    mut v_x_4561_: *mut LeanObject,
    mut v_x_4562_: *mut LeanObject,
) -> u8 {
    let mut v___x_4563_: u8 = 0;
    v___x_4563_ =
        l_Lean_JsonRpc_instBEqResponseError_beq___redArg(v_inst_4560_, v_x_4561_, v_x_4562_);
    return v___x_4563_;
}
pub unsafe fn l_Lean_JsonRpc_instBEqResponseError_beq___boxed(
    mut v_00_u03b1_4564_: *mut LeanObject,
    mut v_inst_4565_: *mut LeanObject,
    mut v_x_4566_: *mut LeanObject,
    mut v_x_4567_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4568_: u8 = 0;
    let mut v_r_4569_: *mut LeanObject = core::ptr::null_mut();
    v_res_4568_ = l_Lean_JsonRpc_instBEqResponseError_beq(
        v_00_u03b1_4564_,
        v_inst_4565_,
        v_x_4566_,
        v_x_4567_,
    );
    v_r_4569_ = lean_box((v_res_4568_) as usize);
    return v_r_4569_;
}
pub unsafe fn l_Lean_JsonRpc_instBEqResponseError___redArg(
    mut v_inst_4570_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4571_: *mut LeanObject = core::ptr::null_mut();
    v___x_4571_ = lean_alloc_closure(
        l_Lean_JsonRpc_instBEqResponseError_beq___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___x_4571_, 0, lean_box(0));
    lean_closure_set(v___x_4571_, 1, v_inst_4570_);
    return v___x_4571_;
}
pub unsafe fn l_Lean_JsonRpc_instBEqResponseError(
    mut v_00_u03b1_4572_: *mut LeanObject,
    mut v_inst_4573_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4574_: *mut LeanObject = core::ptr::null_mut();
    v___x_4574_ = lean_alloc_closure(
        l_Lean_JsonRpc_instBEqResponseError_beq___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___x_4574_, 0, lean_box(0));
    lean_closure_set(v___x_4574_, 1, v_inst_4573_);
    return v___x_4574_;
}
pub unsafe fn l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson___redArg___lam__0(
    mut v_inst_4575_: *mut LeanObject,
    mut v_r_4576_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_data_x3f_4577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_4578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_4579_: u8 = 0;
    let mut v_message_4580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4583_: u8 = 0;
    let mut v___x_4584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4588_: u8 = 0;
    let mut v_unused_4589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_4590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_4591_: u8 = 0;
    let mut v_message_4592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4595_: u8 = 0;
    let mut v_val_4596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4599_: u8 = 0;
    let mut v___x_4600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4607_: u8 = 0;
    let mut v_isSharedCheck_4608_: u8 = 0;
    let mut v_unused_4609_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_data_x3f_4577_ = lean_ctor_get(v_r_4576_, 2);
                lean_inc(v_data_x3f_4577_);
                if lean_obj_tag(v_data_x3f_4577_) == 0 {
                    lean_dec_ref(v_inst_4575_);
                    v_id_4578_ = lean_ctor_get(v_r_4576_, 0);
                    v_code_4579_ = lean_ctor_get_uint8(
                        v_r_4576_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    v_message_4580_ = lean_ctor_get(v_r_4576_, 1);
                    v_isSharedCheck_4588_ = (!lean_is_exclusive(v_r_4576_)) as u8;
                    if v_isSharedCheck_4588_ == 0 {
                        v_unused_4589_ = lean_ctor_get(v_r_4576_, 2);
                        lean_dec(v_unused_4589_);
                        v___x_4582_ = v_r_4576_;
                        v_isShared_4583_ = v_isSharedCheck_4588_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_message_4580_);
                        lean_inc(v_id_4578_);
                        lean_dec(v_r_4576_);
                        v___x_4582_ = lean_box(0);
                        v_isShared_4583_ = v_isSharedCheck_4588_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_id_4590_ = lean_ctor_get(v_r_4576_, 0);
                    v_code_4591_ = lean_ctor_get_uint8(
                        v_r_4576_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    v_message_4592_ = lean_ctor_get(v_r_4576_, 1);
                    v_isSharedCheck_4608_ = (!lean_is_exclusive(v_r_4576_)) as u8;
                    if v_isSharedCheck_4608_ == 0 {
                        v_unused_4609_ = lean_ctor_get(v_r_4576_, 2);
                        lean_dec(v_unused_4609_);
                        v___x_4594_ = v_r_4576_;
                        v_isShared_4595_ = v_isSharedCheck_4608_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_message_4592_);
                        lean_inc(v_id_4590_);
                        lean_dec(v_r_4576_);
                        v___x_4594_ = lean_box(0);
                        v_isShared_4595_ = v_isSharedCheck_4608_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4584_ = lean_box(0);
                if v_isShared_4583_ == 0 {
                    lean_ctor_set_tag(v___x_4582_, 3);
                    lean_ctor_set(v___x_4582_, 2, v___x_4584_);
                    v___x_4586_ = v___x_4582_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4587_ = lean_alloc_ctor(3, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4587_, 0, v_id_4578_);
                    lean_ctor_set(v_reuseFailAlloc_4587_, 1, v_message_4580_);
                    lean_ctor_set(v_reuseFailAlloc_4587_, 2, v___x_4584_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4587_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_code_4579_,
                    );
                    v___x_4586_ = v_reuseFailAlloc_4587_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4586_;
            }
            3 => {
                v_val_4596_ = lean_ctor_get(v_data_x3f_4577_, 0);
                v_isSharedCheck_4607_ = (!lean_is_exclusive(v_data_x3f_4577_)) as u8;
                if v_isSharedCheck_4607_ == 0 {
                    v___x_4598_ = v_data_x3f_4577_;
                    v_isShared_4599_ = v_isSharedCheck_4607_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_val_4596_);
                    lean_dec(v_data_x3f_4577_);
                    v___x_4598_ = lean_box(0);
                    v_isShared_4599_ = v_isSharedCheck_4607_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4600_ = lean_apply_1(v_inst_4575_, v_val_4596_);
                if v_isShared_4599_ == 0 {
                    lean_ctor_set(v___x_4598_, 0, v___x_4600_);
                    v___x_4602_ = v___x_4598_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4606_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4606_, 0, v___x_4600_);
                    v___x_4602_ = v_reuseFailAlloc_4606_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_4595_ == 0 {
                    lean_ctor_set_tag(v___x_4594_, 3);
                    lean_ctor_set(v___x_4594_, 2, v___x_4602_);
                    v___x_4604_ = v___x_4594_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4605_ = lean_alloc_ctor(3, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4605_, 0, v_id_4590_);
                    lean_ctor_set(v_reuseFailAlloc_4605_, 1, v_message_4592_);
                    lean_ctor_set(v_reuseFailAlloc_4605_, 2, v___x_4602_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4605_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_code_4591_,
                    );
                    v___x_4604_ = v_reuseFailAlloc_4605_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4604_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson___redArg(
    mut v_inst_4610_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4611_: *mut LeanObject = core::ptr::null_mut();
    v___f_4611_ = lean_alloc_closure(
        l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_4611_, 0, v_inst_4610_);
    return v___f_4611_;
}
pub unsafe fn l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson(
    mut v_00_u03b1_4612_: *mut LeanObject,
    mut v_inst_4613_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4614_: *mut LeanObject = core::ptr::null_mut();
    v___f_4614_ = lean_alloc_closure(
        l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_4614_, 0, v_inst_4613_);
    return v___f_4614_;
}
pub unsafe fn l_Lean_JsonRpc_instCoeOutResponseErrorUnitMessage___lam__0(
    mut v_r_4615_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_id_4616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_4617_: u8 = 0;
    let mut v_message_4618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4621_: u8 = 0;
    let mut v___x_4622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4626_: u8 = 0;
    let mut v_unused_4627_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_4616_ = lean_ctor_get(v_r_4615_, 0);
                v_code_4617_ = lean_ctor_get_uint8(
                    v_r_4615_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_message_4618_ = lean_ctor_get(v_r_4615_, 1);
                v_isSharedCheck_4626_ = (!lean_is_exclusive(v_r_4615_)) as u8;
                if v_isSharedCheck_4626_ == 0 {
                    v_unused_4627_ = lean_ctor_get(v_r_4615_, 2);
                    lean_dec(v_unused_4627_);
                    v___x_4620_ = v_r_4615_;
                    v_isShared_4621_ = v_isSharedCheck_4626_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_message_4618_);
                    lean_inc(v_id_4616_);
                    lean_dec(v_r_4615_);
                    v___x_4620_ = lean_box(0);
                    v_isShared_4621_ = v_isSharedCheck_4626_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4622_ = lean_box(0);
                if v_isShared_4621_ == 0 {
                    lean_ctor_set_tag(v___x_4620_, 3);
                    lean_ctor_set(v___x_4620_, 2, v___x_4622_);
                    v___x_4624_ = v___x_4620_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4625_ = lean_alloc_ctor(3, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4625_, 0, v_id_4616_);
                    lean_ctor_set(v_reuseFailAlloc_4625_, 1, v_message_4618_);
                    lean_ctor_set(v_reuseFailAlloc_4625_, 2, v___x_4622_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4625_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_code_4617_,
                    );
                    v___x_4624_ = v_reuseFailAlloc_4625_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4624_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_JsonRpc_ResponseError_ofMessage_x3f(
    mut v_x_4630_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_id_4631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_4632_: u8 = 0;
    let mut v_message_4633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_x3f_4634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4637_: u8 = 0;
    let mut v___x_4639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4642_: u8 = 0;
    let mut v___x_4643_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4630_) == 3 {
                    v_id_4631_ = lean_ctor_get(v_x_4630_, 0);
                    v_code_4632_ = lean_ctor_get_uint8(
                        v_x_4630_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    v_message_4633_ = lean_ctor_get(v_x_4630_, 1);
                    v_data_x3f_4634_ = lean_ctor_get(v_x_4630_, 2);
                    v_isSharedCheck_4642_ = (!lean_is_exclusive(v_x_4630_)) as u8;
                    if v_isSharedCheck_4642_ == 0 {
                        v___x_4636_ = v_x_4630_;
                        v_isShared_4637_ = v_isSharedCheck_4642_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_data_x3f_4634_);
                        lean_inc(v_message_4633_);
                        lean_inc(v_id_4631_);
                        lean_dec(v_x_4630_);
                        v___x_4636_ = lean_box(0);
                        v_isShared_4637_ = v_isSharedCheck_4642_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_x_4630_);
                    v___x_4643_ = lean_box(0);
                    return v___x_4643_;
                }
            }
            1 => {
                if v_isShared_4637_ == 0 {
                    lean_ctor_set_tag(v___x_4636_, 0);
                    v___x_4639_ = v___x_4636_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4641_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4641_, 0, v_id_4631_);
                    lean_ctor_set(v_reuseFailAlloc_4641_, 1, v_message_4633_);
                    lean_ctor_set(v_reuseFailAlloc_4641_, 2, v_data_x3f_4634_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4641_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_code_4632_,
                    );
                    v___x_4639_ = v_reuseFailAlloc_4641_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4640_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4640_, 0, v___x_4639_);
                return v___x_4640_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_JsonRpc_instCoeStringRequestID___lam__0(
    mut v_s_4644_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4645_: *mut LeanObject = core::ptr::null_mut();
    v___x_4645_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4645_, 0, v_s_4644_);
    return v___x_4645_;
}
pub unsafe fn l_Lean_JsonRpc_instCoeJsonNumberRequestID___lam__0(
    mut v_n_4648_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4649_: *mut LeanObject = core::ptr::null_mut();
    v___x_4649_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4649_, 0, v_n_4648_);
    return v___x_4649_;
}
pub unsafe fn l_Lean_JsonRpc_RequestID_lt(
    mut v_x_4652_: *mut LeanObject,
    mut v_x_4653_: *mut LeanObject,
) -> u8 {
    match lean_obj_tag(v_x_4652_) {
        0 => {
            if lean_obj_tag(v_x_4653_) == 0 {
                let mut v_s_4654_: *mut LeanObject = core::ptr::null_mut();
                let mut v_s_4655_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4656_: u8 = 0;
                v_s_4654_ = lean_ctor_get(v_x_4652_, 0);
                lean_inc_ref(v_s_4654_);
                lean_dec_ref_known(v_x_4652_, 1);
                v_s_4655_ = lean_ctor_get(v_x_4653_, 0);
                lean_inc_ref(v_s_4655_);
                lean_dec_ref_known(v_x_4653_, 1);
                v___x_4656_ = lean_string_dec_lt(v_s_4654_, v_s_4655_);
                lean_dec_ref(v_s_4655_);
                lean_dec_ref(v_s_4654_);
                return v___x_4656_;
            } else {
                let mut v___x_4657_: u8 = 0;
                lean_dec_ref_known(v_x_4652_, 1);
                lean_dec(v_x_4653_);
                v___x_4657_ = 0;
                return v___x_4657_;
            }
        }
        1 => match lean_obj_tag(v_x_4653_) {
            1 => {
                let mut v_n_4658_: *mut LeanObject = core::ptr::null_mut();
                let mut v_n_4659_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4660_: u8 = 0;
                v_n_4658_ = lean_ctor_get(v_x_4652_, 0);
                lean_inc_ref(v_n_4658_);
                lean_dec_ref_known(v_x_4652_, 1);
                v_n_4659_ = lean_ctor_get(v_x_4653_, 0);
                lean_inc_ref(v_n_4659_);
                lean_dec_ref_known(v_x_4653_, 1);
                v___x_4660_ = l_Lean_JsonNumber_lt(v_n_4658_, v_n_4659_);
                return v___x_4660_;
            }
            0 => {
                let mut v___x_4661_: u8 = 0;
                lean_dec_ref_known(v_x_4653_, 1);
                lean_dec_ref_known(v_x_4652_, 1);
                v___x_4661_ = 1;
                return v___x_4661_;
            }
            _ => {
                let mut v___x_4662_: u8 = 0;
                lean_dec_ref_known(v_x_4652_, 1);
                lean_dec(v_x_4653_);
                v___x_4662_ = 0;
                return v___x_4662_;
            }
        },
        _ => match lean_obj_tag(v_x_4653_) {
            1 => {
                let mut v___x_4663_: u8 = 0;
                lean_dec_ref_known(v_x_4653_, 1);
                v___x_4663_ = 1;
                return v___x_4663_;
            }
            0 => {
                let mut v___x_4664_: u8 = 0;
                lean_dec_ref_known(v_x_4653_, 1);
                v___x_4664_ = 1;
                return v___x_4664_;
            }
            _ => {
                let mut v___x_4665_: u8 = 0;
                lean_dec(v_x_4653_);
                v___x_4665_ = 0;
                return v___x_4665_;
            }
        },
    }
}
pub unsafe fn l_Lean_JsonRpc_RequestID_lt___boxed(
    mut v_x_4666_: *mut LeanObject,
    mut v_x_4667_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4668_: u8 = 0;
    let mut v_r_4669_: *mut LeanObject = core::ptr::null_mut();
    v_res_4668_ = l_Lean_JsonRpc_RequestID_lt(v_x_4666_, v_x_4667_);
    v_r_4669_ = lean_box((v_res_4668_) as usize);
    return v_r_4669_;
}
pub unsafe fn _init_l_Lean_JsonRpc_RequestID_ltProp() -> *mut LeanObject {
    let mut v___x_4670_: *mut LeanObject = core::ptr::null_mut();
    v___x_4670_ = lean_box(0);
    return v___x_4670_;
}
pub unsafe fn _init_l_Lean_JsonRpc_instLTRequestID() -> *mut LeanObject {
    let mut v___x_4671_: *mut LeanObject = core::ptr::null_mut();
    v___x_4671_ = lean_box(0);
    return v___x_4671_;
}
pub unsafe fn l_Lean_JsonRpc_instDecidableLtRequestID(
    mut v_a_4672_: *mut LeanObject,
    mut v_b_4673_: *mut LeanObject,
) -> u8 {
    let mut v___x_4674_: u8 = 0;
    v___x_4674_ = l_Lean_JsonRpc_RequestID_lt(v_a_4672_, v_b_4673_);
    return v___x_4674_;
}
pub unsafe fn l_Lean_JsonRpc_instDecidableLtRequestID___boxed(
    mut v_a_4675_: *mut LeanObject,
    mut v_b_4676_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4677_: u8 = 0;
    let mut v_r_4678_: *mut LeanObject = core::ptr::null_mut();
    v_res_4677_ = l_Lean_JsonRpc_instDecidableLtRequestID(v_a_4675_, v_b_4676_);
    v_r_4678_ = lean_box((v_res_4677_) as usize);
    return v_r_4678_;
}
pub unsafe fn l_Lean_JsonRpc_instFromJsonRequestID___lam__0(
    mut v_j_4682_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_s_4683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4686_: u8 = 0;
    let mut v___x_4688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4691_: u8 = 0;
    let mut v_n_4692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4695_: u8 = 0;
    let mut v___x_4697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4700_: u8 = 0;
    let mut v___x_4701_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_j_4682_) {
                3 => {
                    v_s_4683_ = lean_ctor_get(v_j_4682_, 0);
                    v_isSharedCheck_4691_ = (!lean_is_exclusive(v_j_4682_)) as u8;
                    if v_isSharedCheck_4691_ == 0 {
                        v___x_4685_ = v_j_4682_;
                        v_isShared_4686_ = v_isSharedCheck_4691_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_s_4683_);
                        lean_dec(v_j_4682_);
                        v___x_4685_ = lean_box(0);
                        v_isShared_4686_ = v_isSharedCheck_4691_;
                        state = 1;
                        continue;
                    }
                }
                2 => {
                    v_n_4692_ = lean_ctor_get(v_j_4682_, 0);
                    v_isSharedCheck_4700_ = (!lean_is_exclusive(v_j_4682_)) as u8;
                    if v_isSharedCheck_4700_ == 0 {
                        v___x_4694_ = v_j_4682_;
                        v_isShared_4695_ = v_isSharedCheck_4700_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_n_4692_);
                        lean_dec(v_j_4682_);
                        v___x_4694_ = lean_box(0);
                        v_isShared_4695_ = v_isSharedCheck_4700_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    lean_dec(v_j_4682_);
                    v___x_4701_ = l_Lean_JsonRpc_instFromJsonRequestID___lam__0___closed__1;
                    return v___x_4701_;
                }
            },
            1 => {
                if v_isShared_4686_ == 0 {
                    lean_ctor_set_tag(v___x_4685_, 0);
                    v___x_4688_ = v___x_4685_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4690_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4690_, 0, v_s_4683_);
                    v___x_4688_ = v_reuseFailAlloc_4690_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4689_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4689_, 0, v___x_4688_);
                return v___x_4689_;
            }
            3 => {
                if v_isShared_4695_ == 0 {
                    lean_ctor_set_tag(v___x_4694_, 1);
                    v___x_4697_ = v___x_4694_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4699_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4699_, 0, v_n_4692_);
                    v___x_4697_ = v_reuseFailAlloc_4699_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4698_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4698_, 0, v___x_4697_);
                return v___x_4698_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_JsonRpc_instToJsonRequestID___lam__0(
    mut v_rid_4704_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_s_4705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4708_: u8 = 0;
    let mut v___x_4710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4712_: u8 = 0;
    let mut v_n_4713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4716_: u8 = 0;
    let mut v___x_4718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4720_: u8 = 0;
    let mut v___x_4721_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_rid_4704_) {
                0 => {
                    v_s_4705_ = lean_ctor_get(v_rid_4704_, 0);
                    v_isSharedCheck_4712_ = (!lean_is_exclusive(v_rid_4704_)) as u8;
                    if v_isSharedCheck_4712_ == 0 {
                        v___x_4707_ = v_rid_4704_;
                        v_isShared_4708_ = v_isSharedCheck_4712_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_s_4705_);
                        lean_dec(v_rid_4704_);
                        v___x_4707_ = lean_box(0);
                        v_isShared_4708_ = v_isSharedCheck_4712_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_n_4713_ = lean_ctor_get(v_rid_4704_, 0);
                    v_isSharedCheck_4720_ = (!lean_is_exclusive(v_rid_4704_)) as u8;
                    if v_isSharedCheck_4720_ == 0 {
                        v___x_4715_ = v_rid_4704_;
                        v_isShared_4716_ = v_isSharedCheck_4720_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_n_4713_);
                        lean_dec(v_rid_4704_);
                        v___x_4715_ = lean_box(0);
                        v_isShared_4716_ = v_isSharedCheck_4720_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v___x_4721_ = lean_box(0);
                    return v___x_4721_;
                }
            },
            1 => {
                if v_isShared_4708_ == 0 {
                    lean_ctor_set_tag(v___x_4707_, 3);
                    v___x_4710_ = v___x_4707_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4711_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4711_, 0, v_s_4705_);
                    v___x_4710_ = v_reuseFailAlloc_4711_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4710_;
            }
            3 => {
                if v_isShared_4716_ == 0 {
                    lean_ctor_set_tag(v___x_4715_, 2);
                    v___x_4718_ = v___x_4715_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4719_ = lean_alloc_ctor(2, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4719_, 0, v_n_4713_);
                    v___x_4718_ = v_reuseFailAlloc_4719_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4718_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_JsonRpc_instToJsonMessage___lam__0(
    mut v___x_4739_: *mut LeanObject,
    mut v___x_4740_: *mut LeanObject,
    mut v_m_4741_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_4747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_method_4748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_x3f_4749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_4763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4766_: u8 = 0;
    let mut v___x_4768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4770_: u8 = 0;
    let mut v_n_4771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4774_: u8 = 0;
    let mut v___x_4776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4778_: u8 = 0;
    let mut v___x_4779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_method_4780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_x3f_4781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4784_: u8 = 0;
    let mut v___x_4785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4793_: u8 = 0;
    let mut v_id_4794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_result_4795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4798_: u8 = 0;
    let mut v___x_4799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_4810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4813_: u8 = 0;
    let mut v___x_4815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4817_: u8 = 0;
    let mut v_n_4818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4821_: u8 = 0;
    let mut v___x_4823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4825_: u8 = 0;
    let mut v___x_4826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4827_: u8 = 0;
    let mut v_id_4828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_4829_: u8 = 0;
    let mut v_message_4830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_x3f_4831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_4869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4872_: u8 = 0;
    let mut v___x_4874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4876_: u8 = 0;
    let mut v_n_4877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4880_: u8 = 0;
    let mut v___x_4882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4884_: u8 = 0;
    let mut v___x_4885_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4742_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3;
                match lean_obj_tag(v_m_4741_) {
                    0 => {
                        lean_dec_ref(v___x_4740_);
                        v_id_4747_ = lean_ctor_get(v_m_4741_, 0);
                        lean_inc(v_id_4747_);
                        v_method_4748_ = lean_ctor_get(v_m_4741_, 1);
                        lean_inc_ref(v_method_4748_);
                        v_params_x3f_4749_ = lean_ctor_get(v_m_4741_, 2);
                        lean_inc(v_params_x3f_4749_);
                        lean_dec_ref_known(v_m_4741_, 3);
                        v___x_4750_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4;
                        match lean_obj_tag(v_id_4747_) {
                            0 => {
                                v_s_4763_ = lean_ctor_get(v_id_4747_, 0);
                                v_isSharedCheck_4770_ = (!lean_is_exclusive(v_id_4747_)) as u8;
                                if v_isSharedCheck_4770_ == 0 {
                                    v___x_4765_ = v_id_4747_;
                                    v_isShared_4766_ = v_isSharedCheck_4770_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_inc(v_s_4763_);
                                    lean_dec(v_id_4747_);
                                    v___x_4765_ = lean_box(0);
                                    v_isShared_4766_ = v_isSharedCheck_4770_;
                                    state = 3;
                                    continue;
                                }
                            }
                            1 => {
                                v_n_4771_ = lean_ctor_get(v_id_4747_, 0);
                                v_isSharedCheck_4778_ = (!lean_is_exclusive(v_id_4747_)) as u8;
                                if v_isSharedCheck_4778_ == 0 {
                                    v___x_4773_ = v_id_4747_;
                                    v_isShared_4774_ = v_isSharedCheck_4778_;
                                    state = 5;
                                    continue;
                                } else {
                                    lean_inc(v_n_4771_);
                                    lean_dec(v_id_4747_);
                                    v___x_4773_ = lean_box(0);
                                    v_isShared_4774_ = v_isSharedCheck_4778_;
                                    state = 5;
                                    continue;
                                }
                            }
                            _ => {
                                v___x_4779_ = lean_box(0);
                                v___y_4752_ = v___x_4779_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                    1 => {
                        lean_dec_ref(v___x_4740_);
                        v_method_4780_ = lean_ctor_get(v_m_4741_, 0);
                        v_params_x3f_4781_ = lean_ctor_get(v_m_4741_, 1);
                        v_isSharedCheck_4793_ = (!lean_is_exclusive(v_m_4741_)) as u8;
                        if v_isSharedCheck_4793_ == 0 {
                            v___x_4783_ = v_m_4741_;
                            v_isShared_4784_ = v_isSharedCheck_4793_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_params_x3f_4781_);
                            lean_inc(v_method_4780_);
                            lean_dec(v_m_4741_);
                            v___x_4783_ = lean_box(0);
                            v_isShared_4784_ = v_isSharedCheck_4793_;
                            state = 7;
                            continue;
                        }
                    }
                    2 => {
                        lean_dec_ref(v___x_4740_);
                        lean_dec_ref(v___x_4739_);
                        v_id_4794_ = lean_ctor_get(v_m_4741_, 0);
                        v_result_4795_ = lean_ctor_get(v_m_4741_, 1);
                        v_isSharedCheck_4827_ = (!lean_is_exclusive(v_m_4741_)) as u8;
                        if v_isSharedCheck_4827_ == 0 {
                            v___x_4797_ = v_m_4741_;
                            v_isShared_4798_ = v_isSharedCheck_4827_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_result_4795_);
                            lean_inc(v_id_4794_);
                            lean_dec(v_m_4741_);
                            v___x_4797_ = lean_box(0);
                            v_isShared_4798_ = v_isSharedCheck_4827_;
                            state = 9;
                            continue;
                        }
                    }
                    _ => {
                        lean_dec_ref(v___x_4739_);
                        v_id_4828_ = lean_ctor_get(v_m_4741_, 0);
                        lean_inc(v_id_4828_);
                        v_code_4829_ = lean_ctor_get_uint8(
                            v_m_4741_,
                            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        );
                        v_message_4830_ = lean_ctor_get(v_m_4741_, 1);
                        lean_inc_ref(v_message_4830_);
                        v_data_x3f_4831_ = lean_ctor_get(v_m_4741_, 2);
                        lean_inc(v_data_x3f_4831_);
                        lean_dec_ref_known(v_m_4741_, 3);
                        v___x_4851_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4;
                        match lean_obj_tag(v_id_4828_) {
                            0 => {
                                v_s_4869_ = lean_ctor_get(v_id_4828_, 0);
                                v_isSharedCheck_4876_ = (!lean_is_exclusive(v_id_4828_)) as u8;
                                if v_isSharedCheck_4876_ == 0 {
                                    v___x_4871_ = v_id_4828_;
                                    v_isShared_4872_ = v_isSharedCheck_4876_;
                                    state = 18;
                                    continue;
                                } else {
                                    lean_inc(v_s_4869_);
                                    lean_dec(v_id_4828_);
                                    v___x_4871_ = lean_box(0);
                                    v_isShared_4872_ = v_isSharedCheck_4876_;
                                    state = 18;
                                    continue;
                                }
                            }
                            1 => {
                                v_n_4877_ = lean_ctor_get(v_id_4828_, 0);
                                v_isSharedCheck_4884_ = (!lean_is_exclusive(v_id_4828_)) as u8;
                                if v_isSharedCheck_4884_ == 0 {
                                    v___x_4879_ = v_id_4828_;
                                    v_isShared_4880_ = v_isSharedCheck_4884_;
                                    state = 20;
                                    continue;
                                } else {
                                    lean_inc(v_n_4877_);
                                    lean_dec(v_id_4828_);
                                    v___x_4879_ = lean_box(0);
                                    v_isShared_4880_ = v_isSharedCheck_4884_;
                                    state = 20;
                                    continue;
                                }
                            }
                            _ => {
                                v___x_4885_ = lean_box(0);
                                v___y_4853_ = v___x_4885_;
                                state = 17;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_4745_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4745_, 0, v___x_4742_);
                lean_ctor_set(v___x_4745_, 1, v___y_4744_);
                v___x_4746_ = l_Lean_Json_mkObj(v___x_4745_);
                lean_dec_ref_known(v___x_4745_, 2);
                return v___x_4746_;
            }
            2 => {
                v___x_4753_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4753_, 0, v___x_4750_);
                lean_ctor_set(v___x_4753_, 1, v___y_4752_);
                v___x_4754_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
                v___x_4755_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_4755_, 0, v_method_4748_);
                v___x_4756_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4756_, 0, v___x_4754_);
                lean_ctor_set(v___x_4756_, 1, v___x_4755_);
                v___x_4757_ = lean_box(0);
                v___x_4758_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4758_, 0, v___x_4756_);
                lean_ctor_set(v___x_4758_, 1, v___x_4757_);
                v___x_4759_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4759_, 0, v___x_4753_);
                lean_ctor_set(v___x_4759_, 1, v___x_4758_);
                v___x_4760_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6;
                v___x_4761_ =
                    l_Lean_Json_opt___redArg(v___x_4739_, v___x_4760_, v_params_x3f_4749_);
                v___x_4762_ = l_List_appendTR___redArg(v___x_4759_, v___x_4761_);
                v___y_4744_ = v___x_4762_;
                state = 1;
                continue;
            }
            3 => {
                if v_isShared_4766_ == 0 {
                    lean_ctor_set_tag(v___x_4765_, 3);
                    v___x_4768_ = v___x_4765_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4769_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4769_, 0, v_s_4763_);
                    v___x_4768_ = v_reuseFailAlloc_4769_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___y_4752_ = v___x_4768_;
                state = 2;
                continue;
            }
            5 => {
                if v_isShared_4774_ == 0 {
                    lean_ctor_set_tag(v___x_4773_, 2);
                    v___x_4776_ = v___x_4773_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4777_ = lean_alloc_ctor(2, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4777_, 0, v_n_4771_);
                    v___x_4776_ = v_reuseFailAlloc_4777_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___y_4752_ = v___x_4776_;
                state = 2;
                continue;
            }
            7 => {
                v___x_4785_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
                v___x_4786_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_4786_, 0, v_method_4780_);
                if v_isShared_4784_ == 0 {
                    lean_ctor_set_tag(v___x_4783_, 0);
                    lean_ctor_set(v___x_4783_, 1, v___x_4786_);
                    lean_ctor_set(v___x_4783_, 0, v___x_4785_);
                    v___x_4788_ = v___x_4783_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4792_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4792_, 0, v___x_4785_);
                    lean_ctor_set(v_reuseFailAlloc_4792_, 1, v___x_4786_);
                    v___x_4788_ = v_reuseFailAlloc_4792_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_4789_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6;
                v___x_4790_ =
                    l_Lean_Json_opt___redArg(v___x_4739_, v___x_4789_, v_params_x3f_4781_);
                v___x_4791_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4791_, 0, v___x_4788_);
                lean_ctor_set(v___x_4791_, 1, v___x_4790_);
                v___y_4744_ = v___x_4791_;
                state = 1;
                continue;
            }
            9 => {
                v___x_4799_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4;
                match lean_obj_tag(v_id_4794_) {
                    0 => {
                        v_s_4810_ = lean_ctor_get(v_id_4794_, 0);
                        v_isSharedCheck_4817_ = (!lean_is_exclusive(v_id_4794_)) as u8;
                        if v_isSharedCheck_4817_ == 0 {
                            v___x_4812_ = v_id_4794_;
                            v_isShared_4813_ = v_isSharedCheck_4817_;
                            state = 12;
                            continue;
                        } else {
                            lean_inc(v_s_4810_);
                            lean_dec(v_id_4794_);
                            v___x_4812_ = lean_box(0);
                            v_isShared_4813_ = v_isSharedCheck_4817_;
                            state = 12;
                            continue;
                        }
                    }
                    1 => {
                        v_n_4818_ = lean_ctor_get(v_id_4794_, 0);
                        v_isSharedCheck_4825_ = (!lean_is_exclusive(v_id_4794_)) as u8;
                        if v_isSharedCheck_4825_ == 0 {
                            v___x_4820_ = v_id_4794_;
                            v_isShared_4821_ = v_isSharedCheck_4825_;
                            state = 14;
                            continue;
                        } else {
                            lean_inc(v_n_4818_);
                            lean_dec(v_id_4794_);
                            v___x_4820_ = lean_box(0);
                            v_isShared_4821_ = v_isSharedCheck_4825_;
                            state = 14;
                            continue;
                        }
                    }
                    _ => {
                        v___x_4826_ = lean_box(0);
                        v___y_4801_ = v___x_4826_;
                        state = 10;
                        continue;
                    }
                }
            }
            10 => {
                if v_isShared_4798_ == 0 {
                    lean_ctor_set_tag(v___x_4797_, 0);
                    lean_ctor_set(v___x_4797_, 1, v___y_4801_);
                    lean_ctor_set(v___x_4797_, 0, v___x_4799_);
                    v___x_4803_ = v___x_4797_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4809_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4809_, 0, v___x_4799_);
                    lean_ctor_set(v_reuseFailAlloc_4809_, 1, v___y_4801_);
                    v___x_4803_ = v_reuseFailAlloc_4809_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_4804_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7;
                v___x_4805_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4805_, 0, v___x_4804_);
                lean_ctor_set(v___x_4805_, 1, v_result_4795_);
                v___x_4806_ = lean_box(0);
                v___x_4807_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4807_, 0, v___x_4805_);
                lean_ctor_set(v___x_4807_, 1, v___x_4806_);
                v___x_4808_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4808_, 0, v___x_4803_);
                lean_ctor_set(v___x_4808_, 1, v___x_4807_);
                v___y_4744_ = v___x_4808_;
                state = 1;
                continue;
            }
            12 => {
                if v_isShared_4813_ == 0 {
                    lean_ctor_set_tag(v___x_4812_, 3);
                    v___x_4815_ = v___x_4812_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4816_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4816_, 0, v_s_4810_);
                    v___x_4815_ = v_reuseFailAlloc_4816_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___y_4801_ = v___x_4815_;
                state = 10;
                continue;
            }
            14 => {
                if v_isShared_4821_ == 0 {
                    lean_ctor_set_tag(v___x_4820_, 2);
                    v___x_4823_ = v___x_4820_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4824_ = lean_alloc_ctor(2, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4824_, 0, v_n_4818_);
                    v___x_4823_ = v_reuseFailAlloc_4824_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___y_4801_ = v___x_4823_;
                state = 10;
                continue;
            }
            16 => {
                lean_inc(v___y_4836_);
                lean_inc_ref(v___y_4834_);
                v___x_4837_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4837_, 0, v___y_4834_);
                lean_ctor_set(v___x_4837_, 1, v___y_4836_);
                v___x_4838_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8;
                v___x_4839_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_4839_, 0, v_message_4830_);
                v___x_4840_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4840_, 0, v___x_4838_);
                lean_ctor_set(v___x_4840_, 1, v___x_4839_);
                v___x_4841_ = lean_box(0);
                v___x_4842_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4842_, 0, v___x_4840_);
                lean_ctor_set(v___x_4842_, 1, v___x_4841_);
                v___x_4843_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4843_, 0, v___x_4837_);
                lean_ctor_set(v___x_4843_, 1, v___x_4842_);
                v___x_4844_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9;
                v___x_4845_ = l_Lean_Json_opt___redArg(v___x_4740_, v___x_4844_, v_data_x3f_4831_);
                v___x_4846_ = l_List_appendTR___redArg(v___x_4843_, v___x_4845_);
                v___x_4847_ = l_Lean_Json_mkObj(v___x_4846_);
                lean_dec(v___x_4846_);
                lean_inc_ref(v___y_4833_);
                v___x_4848_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4848_, 0, v___y_4833_);
                lean_ctor_set(v___x_4848_, 1, v___x_4847_);
                v___x_4849_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4849_, 0, v___x_4848_);
                lean_ctor_set(v___x_4849_, 1, v___x_4841_);
                v___x_4850_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4850_, 0, v___y_4835_);
                lean_ctor_set(v___x_4850_, 1, v___x_4849_);
                v___y_4744_ = v___x_4850_;
                state = 1;
                continue;
            }
            17 => {
                v___x_4854_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4854_, 0, v___x_4851_);
                lean_ctor_set(v___x_4854_, 1, v___y_4853_);
                v___x_4855_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10;
                v___x_4856_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11;
                match v_code_4829_ {
                    0 => {
                        v___x_4857_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1_once
                            ),
                            _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1,
                        );
                        v___y_4833_ = v___x_4855_;
                        v___y_4834_ = v___x_4856_;
                        v___y_4835_ = v___x_4854_;
                        v___y_4836_ = v___x_4857_;
                        state = 16;
                        continue;
                    }
                    1 => {
                        v___x_4858_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3_once
                            ),
                            _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3,
                        );
                        v___y_4833_ = v___x_4855_;
                        v___y_4834_ = v___x_4856_;
                        v___y_4835_ = v___x_4854_;
                        v___y_4836_ = v___x_4858_;
                        state = 16;
                        continue;
                    }
                    2 => {
                        v___x_4859_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5_once
                            ),
                            _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5,
                        );
                        v___y_4833_ = v___x_4855_;
                        v___y_4834_ = v___x_4856_;
                        v___y_4835_ = v___x_4854_;
                        v___y_4836_ = v___x_4859_;
                        state = 16;
                        continue;
                    }
                    3 => {
                        v___x_4860_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7_once
                            ),
                            _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7,
                        );
                        v___y_4833_ = v___x_4855_;
                        v___y_4834_ = v___x_4856_;
                        v___y_4835_ = v___x_4854_;
                        v___y_4836_ = v___x_4860_;
                        state = 16;
                        continue;
                    }
                    4 => {
                        v___x_4861_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9_once
                            ),
                            _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9,
                        );
                        v___y_4833_ = v___x_4855_;
                        v___y_4834_ = v___x_4856_;
                        v___y_4835_ = v___x_4854_;
                        v___y_4836_ = v___x_4861_;
                        state = 16;
                        continue;
                    }
                    5 => {
                        v___x_4862_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11_once
                            ),
                            _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11,
                        );
                        v___y_4833_ = v___x_4855_;
                        v___y_4834_ = v___x_4856_;
                        v___y_4835_ = v___x_4854_;
                        v___y_4836_ = v___x_4862_;
                        state = 16;
                        continue;
                    }
                    6 => {
                        v___x_4863_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13_once
                            ),
                            _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13,
                        );
                        v___y_4833_ = v___x_4855_;
                        v___y_4834_ = v___x_4856_;
                        v___y_4835_ = v___x_4854_;
                        v___y_4836_ = v___x_4863_;
                        state = 16;
                        continue;
                    }
                    7 => {
                        v___x_4864_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15_once
                            ),
                            _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15,
                        );
                        v___y_4833_ = v___x_4855_;
                        v___y_4834_ = v___x_4856_;
                        v___y_4835_ = v___x_4854_;
                        v___y_4836_ = v___x_4864_;
                        state = 16;
                        continue;
                    }
                    8 => {
                        v___x_4865_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17_once
                            ),
                            _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17,
                        );
                        v___y_4833_ = v___x_4855_;
                        v___y_4834_ = v___x_4856_;
                        v___y_4835_ = v___x_4854_;
                        v___y_4836_ = v___x_4865_;
                        state = 16;
                        continue;
                    }
                    9 => {
                        v___x_4866_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19_once
                            ),
                            _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19,
                        );
                        v___y_4833_ = v___x_4855_;
                        v___y_4834_ = v___x_4856_;
                        v___y_4835_ = v___x_4854_;
                        v___y_4836_ = v___x_4866_;
                        state = 16;
                        continue;
                    }
                    10 => {
                        v___x_4867_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21_once
                            ),
                            _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21,
                        );
                        v___y_4833_ = v___x_4855_;
                        v___y_4834_ = v___x_4856_;
                        v___y_4835_ = v___x_4854_;
                        v___y_4836_ = v___x_4867_;
                        state = 16;
                        continue;
                    }
                    _ => {
                        v___x_4868_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23_once
                            ),
                            _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23,
                        );
                        v___y_4833_ = v___x_4855_;
                        v___y_4834_ = v___x_4856_;
                        v___y_4835_ = v___x_4854_;
                        v___y_4836_ = v___x_4868_;
                        state = 16;
                        continue;
                    }
                }
            }
            18 => {
                if v_isShared_4872_ == 0 {
                    lean_ctor_set_tag(v___x_4871_, 3);
                    v___x_4874_ = v___x_4871_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_4875_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4875_, 0, v_s_4869_);
                    v___x_4874_ = v_reuseFailAlloc_4875_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                v___y_4853_ = v___x_4874_;
                state = 17;
                continue;
            }
            20 => {
                if v_isShared_4880_ == 0 {
                    lean_ctor_set_tag(v___x_4879_, 2);
                    v___x_4882_ = v___x_4879_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_4883_ = lean_alloc_ctor(2, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4883_, 0, v_n_4877_);
                    v___x_4882_ = v_reuseFailAlloc_4883_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v___y_4853_ = v___x_4882_;
                state = 17;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_JsonRpc_instFromJsonMessage___lam__0(
    mut v___f_4895_: *mut LeanObject,
    mut v___f_4896_: *mut LeanObject,
    mut v___x_4897_: *mut LeanObject,
    mut v___x_4898_: *mut LeanObject,
    mut v_j_4899_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4905_: u8 = 0;
    let mut v___y_4906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4919_: u8 = 0;
    let mut v___x_4921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4923_: u8 = 0;
    let mut v_a_4924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_4925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4927_: u8 = 0;
    let mut v___x_4928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4934_: u8 = 0;
    let mut v___x_4936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4938_: u8 = 0;
    let mut v_a_4939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4945_: u8 = 0;
    let mut v___x_4947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4949_: u8 = 0;
    let mut v_a_4950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4956_: u8 = 0;
    let mut v___x_4958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4960_: u8 = 0;
    let mut v_a_4961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4967_: u8 = 0;
    let mut v___x_4969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4971_: u8 = 0;
    let mut v_a_4972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4976_: u8 = 0;
    let mut v_a_4977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4980_: u8 = 0;
    let mut v___x_4982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4983_: u8 = 0;
    let mut v_reuseFailAlloc_4984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4985_: u8 = 0;
    let mut v___x_4987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4995_: u8 = 0;
    let mut v___x_4996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5000_: u8 = 0;
    let mut v_a_5001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5008_: u8 = 0;
    let mut v___x_5010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5012_: u8 = 0;
    let mut v_a_5013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5019_: u8 = 0;
    let mut v___y_5021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5032_: u8 = 0;
    let mut v___x_5034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5036_: u8 = 0;
    let mut v_isSharedCheck_5037_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4914_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__0;
                lean_inc(v_j_4899_);
                v___x_4915_ = l_Lean_Json_getObjVal_x3f(v_j_4899_, v___x_4914_);
                if lean_obj_tag(v___x_4915_) == 0 {
                    lean_dec(v_j_4899_);
                    lean_dec_ref(v___x_4898_);
                    lean_dec_ref(v___x_4897_);
                    lean_dec_ref(v___f_4896_);
                    lean_dec_ref(v___f_4895_);
                    v_a_4916_ = lean_ctor_get(v___x_4915_, 0);
                    v_isSharedCheck_4923_ = (!lean_is_exclusive(v___x_4915_)) as u8;
                    if v_isSharedCheck_4923_ == 0 {
                        v___x_4918_ = v___x_4915_;
                        v_isShared_4919_ = v_isSharedCheck_4923_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_4916_);
                        lean_dec(v___x_4915_);
                        v___x_4918_ = lean_box(0);
                        v_isShared_4919_ = v_isSharedCheck_4923_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_4924_ = lean_ctor_get(v___x_4915_, 0);
                    lean_inc(v_a_4924_);
                    lean_dec_ref_known(v___x_4915_, 1);
                    if lean_obj_tag(v_a_4924_) == 3 {
                        v_s_4925_ = lean_ctor_get(v_a_4924_, 0);
                        lean_inc_ref(v_s_4925_);
                        lean_dec_ref_known(v_a_4924_, 1);
                        v___x_4926_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__1;
                        v___x_4927_ = lean_string_dec_eq(v_s_4925_, v___x_4926_);
                        lean_dec_ref(v_s_4925_);
                        if v___x_4927_ == 0 {
                            lean_dec(v_j_4899_);
                            lean_dec_ref(v___x_4898_);
                            lean_dec_ref(v___x_4897_);
                            lean_dec_ref(v___f_4896_);
                            lean_dec_ref(v___f_4895_);
                            state = 1;
                            continue;
                        } else {
                            v___x_4928_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4;
                            lean_inc(v_j_4899_);
                            v___x_4929_ = l_Lean_Json_getObjValAs_x3f___redArg(
                                v_j_4899_,
                                v___f_4895_,
                                v___x_4928_,
                            );
                            if lean_obj_tag(v___x_4929_) == 0 {
                                state = 17;
                                continue;
                            } else {
                                v_a_5013_ = lean_ctor_get(v___x_4929_, 0);
                                lean_inc(v_a_5013_);
                                v___x_5014_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
                                lean_inc_ref(v___x_4897_);
                                lean_inc(v_j_4899_);
                                v___x_5015_ = l_Lean_Json_getObjValAs_x3f___redArg(
                                    v_j_4899_,
                                    v___x_4897_,
                                    v___x_5014_,
                                );
                                if lean_obj_tag(v___x_5015_) == 0 {
                                    lean_dec_ref_known(v___x_5015_, 1);
                                    lean_dec(v_a_5013_);
                                    state = 17;
                                    continue;
                                } else {
                                    lean_dec_ref_known(v___x_4929_, 1);
                                    lean_dec_ref(v___x_4897_);
                                    lean_dec_ref(v___f_4896_);
                                    v_a_5016_ = lean_ctor_get(v___x_5015_, 0);
                                    v_isSharedCheck_5037_ = (!lean_is_exclusive(v___x_5015_)) as u8;
                                    if v_isSharedCheck_5037_ == 0 {
                                        v___x_5018_ = v___x_5015_;
                                        v_isShared_5019_ = v_isSharedCheck_5037_;
                                        state = 22;
                                        continue;
                                    } else {
                                        lean_inc(v_a_5016_);
                                        lean_dec(v___x_5015_);
                                        v___x_5018_ = lean_box(0);
                                        v_isShared_5019_ = v_isSharedCheck_5037_;
                                        state = 22;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        lean_dec(v_a_4924_);
                        lean_dec(v_j_4899_);
                        lean_dec_ref(v___x_4898_);
                        lean_dec_ref(v___x_4897_);
                        lean_dec_ref(v___f_4896_);
                        lean_dec_ref(v___f_4895_);
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4901_ = l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__1;
                return v___x_4901_;
            }
            2 => {
                v___x_4907_ = lean_alloc_ctor(3, 3, (1) as u32);
                lean_ctor_set(v___x_4907_, 0, v___y_4903_);
                lean_ctor_set(v___x_4907_, 1, v___y_4904_);
                lean_ctor_set(v___x_4907_, 2, v___y_4906_);
                lean_ctor_set_uint8(
                    v___x_4907_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___y_4905_,
                );
                v___x_4908_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4908_, 0, v___x_4907_);
                return v___x_4908_;
            }
            3 => {
                v___x_4912_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4912_, 0, v___y_4910_);
                lean_ctor_set(v___x_4912_, 1, v___y_4911_);
                v___x_4913_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4913_, 0, v___x_4912_);
                return v___x_4913_;
            }
            4 => {
                if v_isShared_4919_ == 0 {
                    v___x_4921_ = v___x_4918_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4922_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4922_, 0, v_a_4916_);
                    v___x_4921_ = v_reuseFailAlloc_4922_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4921_;
            }
            6 => {
                if lean_obj_tag(v___x_4929_) == 0 {
                    lean_dec(v_j_4899_);
                    lean_dec_ref(v___x_4897_);
                    lean_dec_ref(v___f_4896_);
                    v_a_4931_ = lean_ctor_get(v___x_4929_, 0);
                    v_isSharedCheck_4938_ = (!lean_is_exclusive(v___x_4929_)) as u8;
                    if v_isSharedCheck_4938_ == 0 {
                        v___x_4933_ = v___x_4929_;
                        v_isShared_4934_ = v_isSharedCheck_4938_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_4931_);
                        lean_dec(v___x_4929_);
                        v___x_4933_ = lean_box(0);
                        v_isShared_4934_ = v_isSharedCheck_4938_;
                        state = 7;
                        continue;
                    }
                } else {
                    v_a_4939_ = lean_ctor_get(v___x_4929_, 0);
                    lean_inc(v_a_4939_);
                    lean_dec_ref_known(v___x_4929_, 1);
                    v___x_4940_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10;
                    v___x_4941_ = l_Lean_Json_getObjVal_x3f(v_j_4899_, v___x_4940_);
                    if lean_obj_tag(v___x_4941_) == 0 {
                        lean_dec(v_a_4939_);
                        lean_dec_ref(v___x_4897_);
                        lean_dec_ref(v___f_4896_);
                        v_a_4942_ = lean_ctor_get(v___x_4941_, 0);
                        v_isSharedCheck_4949_ = (!lean_is_exclusive(v___x_4941_)) as u8;
                        if v_isSharedCheck_4949_ == 0 {
                            v___x_4944_ = v___x_4941_;
                            v_isShared_4945_ = v_isSharedCheck_4949_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_4942_);
                            lean_dec(v___x_4941_);
                            v___x_4944_ = lean_box(0);
                            v_isShared_4945_ = v_isSharedCheck_4949_;
                            state = 9;
                            continue;
                        }
                    } else {
                        v_a_4950_ = lean_ctor_get(v___x_4941_, 0);
                        lean_inc_n(v_a_4950_, 2);
                        lean_dec_ref_known(v___x_4941_, 1);
                        v___x_4951_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11;
                        v___x_4952_ = l_Lean_Json_getObjValAs_x3f___redArg(
                            v_a_4950_,
                            v___f_4896_,
                            v___x_4951_,
                        );
                        if lean_obj_tag(v___x_4952_) == 0 {
                            lean_dec(v_a_4950_);
                            lean_dec(v_a_4939_);
                            lean_dec_ref(v___x_4897_);
                            v_a_4953_ = lean_ctor_get(v___x_4952_, 0);
                            v_isSharedCheck_4960_ = (!lean_is_exclusive(v___x_4952_)) as u8;
                            if v_isSharedCheck_4960_ == 0 {
                                v___x_4955_ = v___x_4952_;
                                v_isShared_4956_ = v_isSharedCheck_4960_;
                                state = 11;
                                continue;
                            } else {
                                lean_inc(v_a_4953_);
                                lean_dec(v___x_4952_);
                                v___x_4955_ = lean_box(0);
                                v_isShared_4956_ = v_isSharedCheck_4960_;
                                state = 11;
                                continue;
                            }
                        } else {
                            v_a_4961_ = lean_ctor_get(v___x_4952_, 0);
                            lean_inc(v_a_4961_);
                            lean_dec_ref_known(v___x_4952_, 1);
                            v___x_4962_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8;
                            lean_inc(v_a_4950_);
                            v___x_4963_ = l_Lean_Json_getObjValAs_x3f___redArg(
                                v_a_4950_,
                                v___x_4897_,
                                v___x_4962_,
                            );
                            if lean_obj_tag(v___x_4963_) == 0 {
                                lean_dec(v_a_4961_);
                                lean_dec(v_a_4950_);
                                lean_dec(v_a_4939_);
                                v_a_4964_ = lean_ctor_get(v___x_4963_, 0);
                                v_isSharedCheck_4971_ = (!lean_is_exclusive(v___x_4963_)) as u8;
                                if v_isSharedCheck_4971_ == 0 {
                                    v___x_4966_ = v___x_4963_;
                                    v_isShared_4967_ = v_isSharedCheck_4971_;
                                    state = 13;
                                    continue;
                                } else {
                                    lean_inc(v_a_4964_);
                                    lean_dec(v___x_4963_);
                                    v___x_4966_ = lean_box(0);
                                    v_isShared_4967_ = v_isSharedCheck_4971_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                v_a_4972_ = lean_ctor_get(v___x_4963_, 0);
                                lean_inc(v_a_4972_);
                                lean_dec_ref_known(v___x_4963_, 1);
                                v___x_4973_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9;
                                v___x_4974_ = l_Lean_Json_getObjVal_x3f(v_a_4950_, v___x_4973_);
                                if lean_obj_tag(v___x_4974_) == 0 {
                                    lean_dec_ref_known(v___x_4974_, 1);
                                    v___x_4975_ = lean_box(0);
                                    v___x_4976_ = (lean_unbox(v_a_4961_) as u8);
                                    lean_dec(v_a_4961_);
                                    v___y_4903_ = v_a_4939_;
                                    v___y_4904_ = v_a_4972_;
                                    v___y_4905_ = v___x_4976_;
                                    v___y_4906_ = v___x_4975_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_a_4977_ = lean_ctor_get(v___x_4974_, 0);
                                    v_isSharedCheck_4985_ = (!lean_is_exclusive(v___x_4974_)) as u8;
                                    if v_isSharedCheck_4985_ == 0 {
                                        v___x_4979_ = v___x_4974_;
                                        v_isShared_4980_ = v_isSharedCheck_4985_;
                                        state = 15;
                                        continue;
                                    } else {
                                        lean_inc(v_a_4977_);
                                        lean_dec(v___x_4974_);
                                        v___x_4979_ = lean_box(0);
                                        v_isShared_4980_ = v_isSharedCheck_4985_;
                                        state = 15;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            7 => {
                if v_isShared_4934_ == 0 {
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
                if v_isShared_4945_ == 0 {
                    v___x_4947_ = v___x_4944_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4948_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4948_, 0, v_a_4942_);
                    v___x_4947_ = v_reuseFailAlloc_4948_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4947_;
            }
            11 => {
                if v_isShared_4956_ == 0 {
                    v___x_4958_ = v___x_4955_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4959_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4959_, 0, v_a_4953_);
                    v___x_4958_ = v_reuseFailAlloc_4959_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4958_;
            }
            13 => {
                if v_isShared_4967_ == 0 {
                    v___x_4969_ = v___x_4966_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4970_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4970_, 0, v_a_4964_);
                    v___x_4969_ = v_reuseFailAlloc_4970_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4969_;
            }
            15 => {
                if v_isShared_4980_ == 0 {
                    v___x_4982_ = v___x_4979_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4984_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4984_, 0, v_a_4977_);
                    v___x_4982_ = v_reuseFailAlloc_4984_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___x_4983_ = (lean_unbox(v_a_4961_) as u8);
                lean_dec(v_a_4961_);
                v___y_4903_ = v_a_4939_;
                v___y_4904_ = v_a_4972_;
                v___y_4905_ = v___x_4983_;
                v___y_4906_ = v___x_4982_;
                state = 2;
                continue;
            }
            17 => {
                v___x_4987_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
                lean_inc_ref(v___x_4897_);
                lean_inc(v_j_4899_);
                v___x_4988_ =
                    l_Lean_Json_getObjValAs_x3f___redArg(v_j_4899_, v___x_4897_, v___x_4987_);
                if lean_obj_tag(v___x_4988_) == 0 {
                    lean_dec_ref_known(v___x_4988_, 1);
                    lean_dec_ref(v___x_4898_);
                    if lean_obj_tag(v___x_4929_) == 0 {
                        state = 6;
                        continue;
                    } else {
                        v_a_4989_ = lean_ctor_get(v___x_4929_, 0);
                        lean_inc(v_a_4989_);
                        v___x_4990_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7;
                        lean_inc(v_j_4899_);
                        v___x_4991_ = l_Lean_Json_getObjVal_x3f(v_j_4899_, v___x_4990_);
                        if lean_obj_tag(v___x_4991_) == 0 {
                            lean_dec_ref_known(v___x_4991_, 1);
                            lean_dec(v_a_4989_);
                            state = 6;
                            continue;
                        } else {
                            lean_dec_ref_known(v___x_4929_, 1);
                            lean_dec(v_j_4899_);
                            lean_dec_ref(v___x_4897_);
                            lean_dec_ref(v___f_4896_);
                            v_a_4992_ = lean_ctor_get(v___x_4991_, 0);
                            v_isSharedCheck_5000_ = (!lean_is_exclusive(v___x_4991_)) as u8;
                            if v_isSharedCheck_5000_ == 0 {
                                v___x_4994_ = v___x_4991_;
                                v_isShared_4995_ = v_isSharedCheck_5000_;
                                state = 18;
                                continue;
                            } else {
                                lean_inc(v_a_4992_);
                                lean_dec(v___x_4991_);
                                v___x_4994_ = lean_box(0);
                                v_isShared_4995_ = v_isSharedCheck_5000_;
                                state = 18;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v___x_4929_);
                    lean_dec_ref(v___x_4897_);
                    lean_dec_ref(v___f_4896_);
                    v_a_5001_ = lean_ctor_get(v___x_4988_, 0);
                    lean_inc(v_a_5001_);
                    lean_dec_ref_known(v___x_4988_, 1);
                    v___x_5002_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6;
                    v___x_5003_ =
                        l_Lean_Json_getObjValAs_x3f___redArg(v_j_4899_, v___x_4898_, v___x_5002_);
                    if lean_obj_tag(v___x_5003_) == 0 {
                        lean_dec_ref_known(v___x_5003_, 1);
                        v___x_5004_ = lean_box(0);
                        v___y_4910_ = v_a_5001_;
                        v___y_4911_ = v___x_5004_;
                        state = 3;
                        continue;
                    } else {
                        v_a_5005_ = lean_ctor_get(v___x_5003_, 0);
                        v_isSharedCheck_5012_ = (!lean_is_exclusive(v___x_5003_)) as u8;
                        if v_isSharedCheck_5012_ == 0 {
                            v___x_5007_ = v___x_5003_;
                            v_isShared_5008_ = v_isSharedCheck_5012_;
                            state = 20;
                            continue;
                        } else {
                            lean_inc(v_a_5005_);
                            lean_dec(v___x_5003_);
                            v___x_5007_ = lean_box(0);
                            v_isShared_5008_ = v_isSharedCheck_5012_;
                            state = 20;
                            continue;
                        }
                    }
                }
            }
            18 => {
                v___x_4996_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4996_, 0, v_a_4989_);
                lean_ctor_set(v___x_4996_, 1, v_a_4992_);
                if v_isShared_4995_ == 0 {
                    lean_ctor_set(v___x_4994_, 0, v___x_4996_);
                    v___x_4998_ = v___x_4994_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_4999_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4999_, 0, v___x_4996_);
                    v___x_4998_ = v_reuseFailAlloc_4999_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_4998_;
            }
            20 => {
                if v_isShared_5008_ == 0 {
                    v___x_5010_ = v___x_5007_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_5011_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5011_, 0, v_a_5005_);
                    v___x_5010_ = v_reuseFailAlloc_5011_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v___y_4910_ = v_a_5001_;
                v___y_4911_ = v___x_5010_;
                state = 3;
                continue;
            }
            22 => {
                v___x_5026_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6;
                v___x_5027_ =
                    l_Lean_Json_getObjValAs_x3f___redArg(v_j_4899_, v___x_4898_, v___x_5026_);
                if lean_obj_tag(v___x_5027_) == 0 {
                    lean_dec_ref_known(v___x_5027_, 1);
                    v___x_5028_ = lean_box(0);
                    v___y_5021_ = v___x_5028_;
                    state = 23;
                    continue;
                } else {
                    v_a_5029_ = lean_ctor_get(v___x_5027_, 0);
                    v_isSharedCheck_5036_ = (!lean_is_exclusive(v___x_5027_)) as u8;
                    if v_isSharedCheck_5036_ == 0 {
                        v___x_5031_ = v___x_5027_;
                        v_isShared_5032_ = v_isSharedCheck_5036_;
                        state = 25;
                        continue;
                    } else {
                        lean_inc(v_a_5029_);
                        lean_dec(v___x_5027_);
                        v___x_5031_ = lean_box(0);
                        v_isShared_5032_ = v_isSharedCheck_5036_;
                        state = 25;
                        continue;
                    }
                }
            }
            23 => {
                v___x_5022_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_5022_, 0, v_a_5013_);
                lean_ctor_set(v___x_5022_, 1, v_a_5016_);
                lean_ctor_set(v___x_5022_, 2, v___y_5021_);
                if v_isShared_5019_ == 0 {
                    lean_ctor_set(v___x_5018_, 0, v___x_5022_);
                    v___x_5024_ = v___x_5018_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_5025_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5025_, 0, v___x_5022_);
                    v___x_5024_ = v_reuseFailAlloc_5025_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_5024_;
            }
            25 => {
                if v_isShared_5032_ == 0 {
                    v___x_5034_ = v___x_5031_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_5035_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5035_, 0, v_a_5029_);
                    v___x_5034_ = v_reuseFailAlloc_5035_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                v___y_5021_ = v___x_5034_;
                state = 23;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0(
    mut v___x_5051_: *mut LeanObject,
    mut v_inst_5052_: *mut LeanObject,
    mut v_j_5053_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_method_5057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_x3f_5058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5064_: u8 = 0;
    let mut v___x_5066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5068_: u8 = 0;
    let mut v_a_5069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5072_: u8 = 0;
    let mut v___x_5073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5077_: u8 = 0;
    let mut v___x_5079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5085_: u8 = 0;
    let mut v___x_5087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5089_: u8 = 0;
    let mut v_a_5090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_5091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5093_: u8 = 0;
    let mut v___f_5094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5104_: u8 = 0;
    let mut v___x_5106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5108_: u8 = 0;
    let mut v___x_5109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5114_: u8 = 0;
    let mut v___x_5116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5118_: u8 = 0;
    let mut v_a_5119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5125_: u8 = 0;
    let mut v___x_5127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5129_: u8 = 0;
    let mut v___x_5130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5135_: u8 = 0;
    let mut v___x_5137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5139_: u8 = 0;
    let mut v___x_5141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5152_: u8 = 0;
    let mut v___x_5154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5156_: u8 = 0;
    let mut v___x_5157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5158_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5080_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__0;
                lean_inc(v_j_5053_);
                v___x_5081_ = l_Lean_Json_getObjVal_x3f(v_j_5053_, v___x_5080_);
                if lean_obj_tag(v___x_5081_) == 0 {
                    lean_dec(v_j_5053_);
                    lean_dec_ref(v_inst_5052_);
                    lean_dec_ref(v___x_5051_);
                    v_a_5082_ = lean_ctor_get(v___x_5081_, 0);
                    v_isSharedCheck_5089_ = (!lean_is_exclusive(v___x_5081_)) as u8;
                    if v_isSharedCheck_5089_ == 0 {
                        v___x_5084_ = v___x_5081_;
                        v_isShared_5085_ = v_isSharedCheck_5089_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_5082_);
                        lean_dec(v___x_5081_);
                        v___x_5084_ = lean_box(0);
                        v_isShared_5085_ = v_isSharedCheck_5089_;
                        state = 8;
                        continue;
                    }
                } else {
                    v_a_5090_ = lean_ctor_get(v___x_5081_, 0);
                    lean_inc(v_a_5090_);
                    lean_dec_ref_known(v___x_5081_, 1);
                    if lean_obj_tag(v_a_5090_) == 3 {
                        v_s_5091_ = lean_ctor_get(v_a_5090_, 0);
                        lean_inc_ref(v_s_5091_);
                        lean_dec_ref_known(v_a_5090_, 1);
                        v___x_5092_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__1;
                        v___x_5093_ = lean_string_dec_eq(v_s_5091_, v___x_5092_);
                        lean_dec_ref(v_s_5091_);
                        if v___x_5093_ == 0 {
                            lean_dec(v_j_5053_);
                            lean_dec_ref(v_inst_5052_);
                            lean_dec_ref(v___x_5051_);
                            state = 7;
                            continue;
                        } else {
                            v___f_5094_ = l_Lean_JsonRpc_instFromJsonRequestID___closed__0;
                            v___x_5095_ = l_Lean_JsonRpc_instFromJsonMessage___closed__0;
                            v___x_5096_ = l_Lean_JsonRpc_instFromJsonMessage___closed__1;
                            v___f_5097_ = l_Lean_JsonRpc_instFromJsonErrorCode___closed__0;
                            v___x_5098_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4;
                            lean_inc(v_j_5053_);
                            v___x_5099_ = l_Lean_Json_getObjValAs_x3f___redArg(
                                v_j_5053_,
                                v___f_5094_,
                                v___x_5098_,
                            );
                            if lean_obj_tag(v___x_5099_) == 0 {
                                state = 19;
                                continue;
                            } else {
                                v___x_5157_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
                                lean_inc(v_j_5053_);
                                v___x_5158_ = l_Lean_Json_getObjValAs_x3f___redArg(
                                    v_j_5053_,
                                    v___x_5095_,
                                    v___x_5157_,
                                );
                                if lean_obj_tag(v___x_5158_) == 0 {
                                    lean_dec_ref_known(v___x_5158_, 1);
                                    state = 19;
                                    continue;
                                } else {
                                    lean_dec_ref_known(v___x_5158_, 1);
                                    lean_dec_ref_known(v___x_5099_, 1);
                                    lean_dec(v_j_5053_);
                                    lean_dec_ref(v_inst_5052_);
                                    lean_dec_ref(v___x_5051_);
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec(v_a_5090_);
                        lean_dec(v_j_5053_);
                        lean_dec_ref(v_inst_5052_);
                        lean_dec_ref(v___x_5051_);
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5055_ = l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0___closed__1;
                return v___x_5055_;
            }
            2 => {
                v___x_5059_ = l_Option_toJson___redArg(v___x_5051_, v_params_x3f_5058_);
                v___x_5060_ = lean_apply_1(v_inst_5052_, v___x_5059_);
                if lean_obj_tag(v___x_5060_) == 0 {
                    lean_dec_ref(v_method_5057_);
                    v_a_5061_ = lean_ctor_get(v___x_5060_, 0);
                    v_isSharedCheck_5068_ = (!lean_is_exclusive(v___x_5060_)) as u8;
                    if v_isSharedCheck_5068_ == 0 {
                        v___x_5063_ = v___x_5060_;
                        v_isShared_5064_ = v_isSharedCheck_5068_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5061_);
                        lean_dec(v___x_5060_);
                        v___x_5063_ = lean_box(0);
                        v_isShared_5064_ = v_isSharedCheck_5068_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_5069_ = lean_ctor_get(v___x_5060_, 0);
                    v_isSharedCheck_5077_ = (!lean_is_exclusive(v___x_5060_)) as u8;
                    if v_isSharedCheck_5077_ == 0 {
                        v___x_5071_ = v___x_5060_;
                        v_isShared_5072_ = v_isSharedCheck_5077_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_5069_);
                        lean_dec(v___x_5060_);
                        v___x_5071_ = lean_box(0);
                        v_isShared_5072_ = v_isSharedCheck_5077_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_5064_ == 0 {
                    v___x_5066_ = v___x_5063_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5067_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5067_, 0, v_a_5061_);
                    v___x_5066_ = v_reuseFailAlloc_5067_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5066_;
            }
            5 => {
                v___x_5073_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5073_, 0, v_method_5057_);
                lean_ctor_set(v___x_5073_, 1, v_a_5069_);
                if v_isShared_5072_ == 0 {
                    lean_ctor_set(v___x_5071_, 0, v___x_5073_);
                    v___x_5075_ = v___x_5071_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5076_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5076_, 0, v___x_5073_);
                    v___x_5075_ = v_reuseFailAlloc_5076_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5075_;
            }
            7 => {
                v___x_5079_ = l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0___closed__2;
                return v___x_5079_;
            }
            8 => {
                if v_isShared_5085_ == 0 {
                    v___x_5087_ = v___x_5084_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5088_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5088_, 0, v_a_5082_);
                    v___x_5087_ = v_reuseFailAlloc_5088_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5087_;
            }
            10 => {
                if lean_obj_tag(v___x_5099_) == 0 {
                    lean_dec(v_j_5053_);
                    v_a_5101_ = lean_ctor_get(v___x_5099_, 0);
                    v_isSharedCheck_5108_ = (!lean_is_exclusive(v___x_5099_)) as u8;
                    if v_isSharedCheck_5108_ == 0 {
                        v___x_5103_ = v___x_5099_;
                        v_isShared_5104_ = v_isSharedCheck_5108_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_5101_);
                        lean_dec(v___x_5099_);
                        v___x_5103_ = lean_box(0);
                        v_isShared_5104_ = v_isSharedCheck_5108_;
                        state = 11;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v___x_5099_, 1);
                    v___x_5109_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10;
                    v___x_5110_ = l_Lean_Json_getObjVal_x3f(v_j_5053_, v___x_5109_);
                    if lean_obj_tag(v___x_5110_) == 0 {
                        v_a_5111_ = lean_ctor_get(v___x_5110_, 0);
                        v_isSharedCheck_5118_ = (!lean_is_exclusive(v___x_5110_)) as u8;
                        if v_isSharedCheck_5118_ == 0 {
                            v___x_5113_ = v___x_5110_;
                            v_isShared_5114_ = v_isSharedCheck_5118_;
                            state = 13;
                            continue;
                        } else {
                            lean_inc(v_a_5111_);
                            lean_dec(v___x_5110_);
                            v___x_5113_ = lean_box(0);
                            v_isShared_5114_ = v_isSharedCheck_5118_;
                            state = 13;
                            continue;
                        }
                    } else {
                        v_a_5119_ = lean_ctor_get(v___x_5110_, 0);
                        lean_inc_n(v_a_5119_, 2);
                        lean_dec_ref_known(v___x_5110_, 1);
                        v___x_5120_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11;
                        v___x_5121_ = l_Lean_Json_getObjValAs_x3f___redArg(
                            v_a_5119_,
                            v___f_5097_,
                            v___x_5120_,
                        );
                        if lean_obj_tag(v___x_5121_) == 0 {
                            lean_dec(v_a_5119_);
                            v_a_5122_ = lean_ctor_get(v___x_5121_, 0);
                            v_isSharedCheck_5129_ = (!lean_is_exclusive(v___x_5121_)) as u8;
                            if v_isSharedCheck_5129_ == 0 {
                                v___x_5124_ = v___x_5121_;
                                v_isShared_5125_ = v_isSharedCheck_5129_;
                                state = 15;
                                continue;
                            } else {
                                lean_inc(v_a_5122_);
                                lean_dec(v___x_5121_);
                                v___x_5124_ = lean_box(0);
                                v_isShared_5125_ = v_isSharedCheck_5129_;
                                state = 15;
                                continue;
                            }
                        } else {
                            lean_dec_ref_known(v___x_5121_, 1);
                            v___x_5130_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8;
                            v___x_5131_ = l_Lean_Json_getObjValAs_x3f___redArg(
                                v_a_5119_,
                                v___x_5095_,
                                v___x_5130_,
                            );
                            if lean_obj_tag(v___x_5131_) == 0 {
                                v_a_5132_ = lean_ctor_get(v___x_5131_, 0);
                                v_isSharedCheck_5139_ = (!lean_is_exclusive(v___x_5131_)) as u8;
                                if v_isSharedCheck_5139_ == 0 {
                                    v___x_5134_ = v___x_5131_;
                                    v_isShared_5135_ = v_isSharedCheck_5139_;
                                    state = 17;
                                    continue;
                                } else {
                                    lean_inc(v_a_5132_);
                                    lean_dec(v___x_5131_);
                                    v___x_5134_ = lean_box(0);
                                    v_isShared_5135_ = v_isSharedCheck_5139_;
                                    state = 17;
                                    continue;
                                }
                            } else {
                                lean_dec_ref_known(v___x_5131_, 1);
                                state = 1;
                                continue;
                            }
                        }
                    }
                }
            }
            11 => {
                if v_isShared_5104_ == 0 {
                    v___x_5106_ = v___x_5103_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5107_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5107_, 0, v_a_5101_);
                    v___x_5106_ = v_reuseFailAlloc_5107_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5106_;
            }
            13 => {
                if v_isShared_5114_ == 0 {
                    v___x_5116_ = v___x_5113_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5117_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5117_, 0, v_a_5111_);
                    v___x_5116_ = v_reuseFailAlloc_5117_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_5116_;
            }
            15 => {
                if v_isShared_5125_ == 0 {
                    v___x_5127_ = v___x_5124_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_5128_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5128_, 0, v_a_5122_);
                    v___x_5127_ = v_reuseFailAlloc_5128_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_5127_;
            }
            17 => {
                if v_isShared_5135_ == 0 {
                    v___x_5137_ = v___x_5134_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_5138_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5138_, 0, v_a_5132_);
                    v___x_5137_ = v_reuseFailAlloc_5138_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_5137_;
            }
            19 => {
                v___x_5141_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
                lean_inc(v_j_5053_);
                v___x_5142_ =
                    l_Lean_Json_getObjValAs_x3f___redArg(v_j_5053_, v___x_5095_, v___x_5141_);
                if lean_obj_tag(v___x_5142_) == 0 {
                    lean_dec_ref_known(v___x_5142_, 1);
                    lean_dec_ref(v_inst_5052_);
                    lean_dec_ref(v___x_5051_);
                    if lean_obj_tag(v___x_5099_) == 0 {
                        state = 10;
                        continue;
                    } else {
                        v___x_5143_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7;
                        lean_inc(v_j_5053_);
                        v___x_5144_ = l_Lean_Json_getObjVal_x3f(v_j_5053_, v___x_5143_);
                        if lean_obj_tag(v___x_5144_) == 0 {
                            lean_dec_ref_known(v___x_5144_, 1);
                            state = 10;
                            continue;
                        } else {
                            lean_dec_ref_known(v___x_5144_, 1);
                            lean_dec_ref_known(v___x_5099_, 1);
                            lean_dec(v_j_5053_);
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___x_5099_);
                    v_a_5145_ = lean_ctor_get(v___x_5142_, 0);
                    lean_inc(v_a_5145_);
                    lean_dec_ref_known(v___x_5142_, 1);
                    v___x_5146_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6;
                    v___x_5147_ =
                        l_Lean_Json_getObjValAs_x3f___redArg(v_j_5053_, v___x_5096_, v___x_5146_);
                    if lean_obj_tag(v___x_5147_) == 0 {
                        lean_dec_ref_known(v___x_5147_, 1);
                        v___x_5148_ = lean_box(0);
                        v_method_5057_ = v_a_5145_;
                        v_params_x3f_5058_ = v___x_5148_;
                        state = 2;
                        continue;
                    } else {
                        v_a_5149_ = lean_ctor_get(v___x_5147_, 0);
                        v_isSharedCheck_5156_ = (!lean_is_exclusive(v___x_5147_)) as u8;
                        if v_isSharedCheck_5156_ == 0 {
                            v___x_5151_ = v___x_5147_;
                            v_isShared_5152_ = v_isSharedCheck_5156_;
                            state = 20;
                            continue;
                        } else {
                            lean_inc(v_a_5149_);
                            lean_dec(v___x_5147_);
                            v___x_5151_ = lean_box(0);
                            v_isShared_5152_ = v_isSharedCheck_5156_;
                            state = 20;
                            continue;
                        }
                    }
                }
            }
            20 => {
                if v_isShared_5152_ == 0 {
                    v___x_5154_ = v___x_5151_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_5155_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5155_, 0, v_a_5149_);
                    v___x_5154_ = v_reuseFailAlloc_5155_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v_method_5057_ = v_a_5145_;
                v_params_x3f_5058_ = v___x_5154_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_JsonRpc_instFromJsonNotification___redArg(
    mut v_inst_5159_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5161_: *mut LeanObject = core::ptr::null_mut();
    v___x_5160_ = l_Lean_JsonRpc_instToJsonMessage___closed__0;
    v___f_5161_ = lean_alloc_closure(
        l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_5161_, 0, v___x_5160_);
    lean_closure_set(v___f_5161_, 1, v_inst_5159_);
    return v___f_5161_;
}
pub unsafe fn l_Lean_JsonRpc_instFromJsonNotification(
    mut v_00_u03b1_5162_: *mut LeanObject,
    mut v_inst_5163_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5164_: *mut LeanObject = core::ptr::null_mut();
    v___x_5164_ = l_Lean_JsonRpc_instFromJsonNotification___redArg(v_inst_5163_);
    return v___x_5164_;
}
pub unsafe fn l_Lean_JsonRpc_MessageMetaData_ctorIdx(
    mut v_x_5165_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_5165_) {
        0 => {
            let mut v___x_5166_: *mut LeanObject = core::ptr::null_mut();
            v___x_5166_ = lean_unsigned_to_nat(0);
            return v___x_5166_;
        }
        1 => {
            let mut v___x_5167_: *mut LeanObject = core::ptr::null_mut();
            v___x_5167_ = lean_unsigned_to_nat(1);
            return v___x_5167_;
        }
        2 => {
            let mut v___x_5168_: *mut LeanObject = core::ptr::null_mut();
            v___x_5168_ = lean_unsigned_to_nat(2);
            return v___x_5168_;
        }
        _ => {
            let mut v___x_5169_: *mut LeanObject = core::ptr::null_mut();
            v___x_5169_ = lean_unsigned_to_nat(3);
            return v___x_5169_;
        }
    }
}
pub unsafe fn l_Lean_JsonRpc_MessageMetaData_ctorIdx___boxed(
    mut v_x_5170_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5171_: *mut LeanObject = core::ptr::null_mut();
    v_res_5171_ = l_Lean_JsonRpc_MessageMetaData_ctorIdx(v_x_5170_);
    lean_dec_ref(v_x_5170_);
    return v_res_5171_;
}
pub unsafe fn l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(
    mut v_t_5172_: *mut LeanObject,
    mut v_k_5173_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_t_5172_) {
        0 => {
            let mut v_id_5174_: *mut LeanObject = core::ptr::null_mut();
            let mut v_method_5175_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5176_: *mut LeanObject = core::ptr::null_mut();
            v_id_5174_ = lean_ctor_get(v_t_5172_, 0);
            lean_inc(v_id_5174_);
            v_method_5175_ = lean_ctor_get(v_t_5172_, 1);
            lean_inc_ref(v_method_5175_);
            lean_dec_ref_known(v_t_5172_, 2);
            v___x_5176_ = lean_apply_2(v_k_5173_, v_id_5174_, v_method_5175_);
            return v___x_5176_;
        }
        1 => {
            let mut v_method_5177_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5178_: *mut LeanObject = core::ptr::null_mut();
            v_method_5177_ = lean_ctor_get(v_t_5172_, 0);
            lean_inc_ref(v_method_5177_);
            lean_dec_ref_known(v_t_5172_, 1);
            v___x_5178_ = lean_apply_1(v_k_5173_, v_method_5177_);
            return v___x_5178_;
        }
        2 => {
            let mut v_id_5179_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5180_: *mut LeanObject = core::ptr::null_mut();
            v_id_5179_ = lean_ctor_get(v_t_5172_, 0);
            lean_inc(v_id_5179_);
            lean_dec_ref_known(v_t_5172_, 1);
            v___x_5180_ = lean_apply_1(v_k_5173_, v_id_5179_);
            return v___x_5180_;
        }
        _ => {
            let mut v_id_5181_: *mut LeanObject = core::ptr::null_mut();
            let mut v_code_5182_: u8 = 0;
            let mut v_message_5183_: *mut LeanObject = core::ptr::null_mut();
            let mut v_data_x3f_5184_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5185_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5186_: *mut LeanObject = core::ptr::null_mut();
            v_id_5181_ = lean_ctor_get(v_t_5172_, 0);
            lean_inc(v_id_5181_);
            v_code_5182_ = lean_ctor_get_uint8(
                v_t_5172_,
                (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
            );
            v_message_5183_ = lean_ctor_get(v_t_5172_, 1);
            lean_inc_ref(v_message_5183_);
            v_data_x3f_5184_ = lean_ctor_get(v_t_5172_, 2);
            lean_inc(v_data_x3f_5184_);
            lean_dec_ref_known(v_t_5172_, 3);
            v___x_5185_ = lean_box((v_code_5182_) as usize);
            v___x_5186_ = lean_apply_4(
                v_k_5173_,
                v_id_5181_,
                v___x_5185_,
                v_message_5183_,
                v_data_x3f_5184_,
            );
            return v___x_5186_;
        }
    }
}
pub unsafe fn l_Lean_JsonRpc_MessageMetaData_ctorElim(
    mut v_motive_5187_: *mut LeanObject,
    mut v_ctorIdx_5188_: *mut LeanObject,
    mut v_t_5189_: *mut LeanObject,
    mut v_h_5190_: *mut LeanObject,
    mut v_k_5191_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5192_: *mut LeanObject = core::ptr::null_mut();
    v___x_5192_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_5189_, v_k_5191_);
    return v___x_5192_;
}
pub unsafe fn l_Lean_JsonRpc_MessageMetaData_ctorElim___boxed(
    mut v_motive_5193_: *mut LeanObject,
    mut v_ctorIdx_5194_: *mut LeanObject,
    mut v_t_5195_: *mut LeanObject,
    mut v_h_5196_: *mut LeanObject,
    mut v_k_5197_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5198_: *mut LeanObject = core::ptr::null_mut();
    v_res_5198_ = l_Lean_JsonRpc_MessageMetaData_ctorElim(
        v_motive_5193_,
        v_ctorIdx_5194_,
        v_t_5195_,
        v_h_5196_,
        v_k_5197_,
    );
    lean_dec(v_ctorIdx_5194_);
    return v_res_5198_;
}
pub unsafe fn l_Lean_JsonRpc_MessageMetaData_request_elim___redArg(
    mut v_t_5199_: *mut LeanObject,
    mut v_request_5200_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5201_: *mut LeanObject = core::ptr::null_mut();
    v___x_5201_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_5199_, v_request_5200_);
    return v___x_5201_;
}
pub unsafe fn l_Lean_JsonRpc_MessageMetaData_request_elim(
    mut v_motive_5202_: *mut LeanObject,
    mut v_t_5203_: *mut LeanObject,
    mut v_h_5204_: *mut LeanObject,
    mut v_request_5205_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5206_: *mut LeanObject = core::ptr::null_mut();
    v___x_5206_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_5203_, v_request_5205_);
    return v___x_5206_;
}
pub unsafe fn l_Lean_JsonRpc_MessageMetaData_notification_elim___redArg(
    mut v_t_5207_: *mut LeanObject,
    mut v_notification_5208_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5209_: *mut LeanObject = core::ptr::null_mut();
    v___x_5209_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_5207_, v_notification_5208_);
    return v___x_5209_;
}
pub unsafe fn l_Lean_JsonRpc_MessageMetaData_notification_elim(
    mut v_motive_5210_: *mut LeanObject,
    mut v_t_5211_: *mut LeanObject,
    mut v_h_5212_: *mut LeanObject,
    mut v_notification_5213_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5214_: *mut LeanObject = core::ptr::null_mut();
    v___x_5214_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_5211_, v_notification_5213_);
    return v___x_5214_;
}
pub unsafe fn l_Lean_JsonRpc_MessageMetaData_response_elim___redArg(
    mut v_t_5215_: *mut LeanObject,
    mut v_response_5216_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5217_: *mut LeanObject = core::ptr::null_mut();
    v___x_5217_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_5215_, v_response_5216_);
    return v___x_5217_;
}
pub unsafe fn l_Lean_JsonRpc_MessageMetaData_response_elim(
    mut v_motive_5218_: *mut LeanObject,
    mut v_t_5219_: *mut LeanObject,
    mut v_h_5220_: *mut LeanObject,
    mut v_response_5221_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5222_: *mut LeanObject = core::ptr::null_mut();
    v___x_5222_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_5219_, v_response_5221_);
    return v___x_5222_;
}
pub unsafe fn l_Lean_JsonRpc_MessageMetaData_responseError_elim___redArg(
    mut v_t_5223_: *mut LeanObject,
    mut v_responseError_5224_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5225_: *mut LeanObject = core::ptr::null_mut();
    v___x_5225_ =
        l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_5223_, v_responseError_5224_);
    return v___x_5225_;
}
pub unsafe fn l_Lean_JsonRpc_MessageMetaData_responseError_elim(
    mut v_motive_5226_: *mut LeanObject,
    mut v_t_5227_: *mut LeanObject,
    mut v_h_5228_: *mut LeanObject,
    mut v_responseError_5229_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5230_: *mut LeanObject = core::ptr::null_mut();
    v___x_5230_ =
        l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_5227_, v_responseError_5229_);
    return v___x_5230_;
}
pub unsafe fn l_Lean_JsonRpc_Message_metaData(mut v_x_5236_: *mut LeanObject) -> *mut LeanObject {
    let mut v_id_5237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_method_5238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_method_5240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_5242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_5244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_5245_: u8 = 0;
    let mut v_message_5246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_x3f_5247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5250_: u8 = 0;
    let mut v___x_5252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5254_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_5236_) {
                0 => {
                    v_id_5237_ = lean_ctor_get(v_x_5236_, 0);
                    lean_inc(v_id_5237_);
                    v_method_5238_ = lean_ctor_get(v_x_5236_, 1);
                    lean_inc_ref(v_method_5238_);
                    lean_dec_ref_known(v_x_5236_, 3);
                    v___x_5239_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_5239_, 0, v_id_5237_);
                    lean_ctor_set(v___x_5239_, 1, v_method_5238_);
                    return v___x_5239_;
                }
                1 => {
                    v_method_5240_ = lean_ctor_get(v_x_5236_, 0);
                    lean_inc_ref(v_method_5240_);
                    lean_dec_ref_known(v_x_5236_, 2);
                    v___x_5241_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5241_, 0, v_method_5240_);
                    return v___x_5241_;
                }
                2 => {
                    v_id_5242_ = lean_ctor_get(v_x_5236_, 0);
                    lean_inc(v_id_5242_);
                    lean_dec_ref_known(v_x_5236_, 2);
                    v___x_5243_ = lean_alloc_ctor(2, 1, (0) as u32);
                    lean_ctor_set(v___x_5243_, 0, v_id_5242_);
                    return v___x_5243_;
                }
                _ => {
                    v_id_5244_ = lean_ctor_get(v_x_5236_, 0);
                    v_code_5245_ = lean_ctor_get_uint8(
                        v_x_5236_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    v_message_5246_ = lean_ctor_get(v_x_5236_, 1);
                    v_data_x3f_5247_ = lean_ctor_get(v_x_5236_, 2);
                    v_isSharedCheck_5254_ = (!lean_is_exclusive(v_x_5236_)) as u8;
                    if v_isSharedCheck_5254_ == 0 {
                        v___x_5249_ = v_x_5236_;
                        v_isShared_5250_ = v_isSharedCheck_5254_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_data_x3f_5247_);
                        lean_inc(v_message_5246_);
                        lean_inc(v_id_5244_);
                        lean_dec(v_x_5236_);
                        v___x_5249_ = lean_box(0);
                        v_isShared_5250_ = v_isSharedCheck_5254_;
                        state = 1;
                        continue;
                    }
                }
            },
            1 => {
                if v_isShared_5250_ == 0 {
                    v___x_5252_ = v___x_5249_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5253_ = lean_alloc_ctor(3, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5253_, 0, v_id_5244_);
                    lean_ctor_set(v_reuseFailAlloc_5253_, 1, v_message_5246_);
                    lean_ctor_set(v_reuseFailAlloc_5253_, 2, v_data_x3f_5247_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5253_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_code_5245_,
                    );
                    v___x_5252_ = v_reuseFailAlloc_5253_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5252_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_JsonRpc_MessageMetaData_toMessage(
    mut v_x_5255_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_id_5256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_method_5257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_method_5260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_5263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_5266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_5267_: u8 = 0;
    let mut v_message_5268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_x3f_5269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5272_: u8 = 0;
    let mut v___x_5274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5276_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_5255_) {
                0 => {
                    v_id_5256_ = lean_ctor_get(v_x_5255_, 0);
                    lean_inc(v_id_5256_);
                    v_method_5257_ = lean_ctor_get(v_x_5255_, 1);
                    lean_inc_ref(v_method_5257_);
                    lean_dec_ref_known(v_x_5255_, 2);
                    v___x_5258_ = lean_box(0);
                    v___x_5259_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_5259_, 0, v_id_5256_);
                    lean_ctor_set(v___x_5259_, 1, v_method_5257_);
                    lean_ctor_set(v___x_5259_, 2, v___x_5258_);
                    return v___x_5259_;
                }
                1 => {
                    v_method_5260_ = lean_ctor_get(v_x_5255_, 0);
                    lean_inc_ref(v_method_5260_);
                    lean_dec_ref_known(v_x_5255_, 1);
                    v___x_5261_ = lean_box(0);
                    v___x_5262_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_5262_, 0, v_method_5260_);
                    lean_ctor_set(v___x_5262_, 1, v___x_5261_);
                    return v___x_5262_;
                }
                2 => {
                    v_id_5263_ = lean_ctor_get(v_x_5255_, 0);
                    lean_inc(v_id_5263_);
                    lean_dec_ref_known(v_x_5255_, 1);
                    v___x_5264_ = lean_box(0);
                    v___x_5265_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_5265_, 0, v_id_5263_);
                    lean_ctor_set(v___x_5265_, 1, v___x_5264_);
                    return v___x_5265_;
                }
                _ => {
                    v_id_5266_ = lean_ctor_get(v_x_5255_, 0);
                    v_code_5267_ = lean_ctor_get_uint8(
                        v_x_5255_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    v_message_5268_ = lean_ctor_get(v_x_5255_, 1);
                    v_data_x3f_5269_ = lean_ctor_get(v_x_5255_, 2);
                    v_isSharedCheck_5276_ = (!lean_is_exclusive(v_x_5255_)) as u8;
                    if v_isSharedCheck_5276_ == 0 {
                        v___x_5271_ = v_x_5255_;
                        v_isShared_5272_ = v_isSharedCheck_5276_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_data_x3f_5269_);
                        lean_inc(v_message_5268_);
                        lean_inc(v_id_5266_);
                        lean_dec(v_x_5255_);
                        v___x_5271_ = lean_box(0);
                        v_isShared_5272_ = v_isSharedCheck_5276_;
                        state = 1;
                        continue;
                    }
                }
            },
            1 => {
                if v_isShared_5272_ == 0 {
                    v___x_5274_ = v___x_5271_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5275_ = lean_alloc_ctor(3, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5275_, 0, v_id_5266_);
                    lean_ctor_set(v_reuseFailAlloc_5275_, 1, v_message_5268_);
                    lean_ctor_set(v_reuseFailAlloc_5275_, 2, v_data_x3f_5269_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5275_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_code_5267_,
                    );
                    v___x_5274_ = v_reuseFailAlloc_5275_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5274_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(
    mut v_a_5280_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_5281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5284_: u8 = 0;
    let mut v___x_5285_: u32 = 0;
    let mut v___x_5286_: u32 = 0;
    let mut v___x_5287_: u8 = 0;
    let mut v___x_5288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5292_: u8 = 0;
    let mut v___x_5293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5299_: u8 = 0;
    let mut v_unused_5300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5305_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_5281_ = lean_ctor_get(v_a_5280_, 0);
                v_snd_5282_ = lean_ctor_get(v_a_5280_, 1);
                v___x_5283_ = lean_string_utf8_byte_size(v_fst_5281_);
                v___x_5284_ = lean_nat_dec_eq(v_snd_5282_, v___x_5283_);
                if v___x_5284_ == 0 {
                    v___x_5285_ = lean_string_utf8_get_fast(v_fst_5281_, v_snd_5282_);
                    v___x_5286_ = 34;
                    v___x_5287_ = lean_uint32_dec_eq(v___x_5285_, v___x_5286_);
                    if v___x_5287_ == 0 {
                        v___x_5288_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr___closed__1;
                        v___x_5289_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_5289_, 0, v_a_5280_);
                        lean_ctor_set(v___x_5289_, 1, v___x_5288_);
                        return v___x_5289_;
                    } else {
                        if v___x_5284_ == 0 {
                            lean_inc(v_snd_5282_);
                            lean_inc(v_fst_5281_);
                            v_isSharedCheck_5299_ = (!lean_is_exclusive(v_a_5280_)) as u8;
                            if v_isSharedCheck_5299_ == 0 {
                                v_unused_5300_ = lean_ctor_get(v_a_5280_, 1);
                                lean_dec(v_unused_5300_);
                                v_unused_5301_ = lean_ctor_get(v_a_5280_, 0);
                                lean_dec(v_unused_5301_);
                                v___x_5291_ = v_a_5280_;
                                v_isShared_5292_ = v_isSharedCheck_5299_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec(v_a_5280_);
                                v___x_5291_ = lean_box(0);
                                v_isShared_5292_ = v_isSharedCheck_5299_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_5302_ = lean_box(0);
                            v___x_5303_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v___x_5303_, 0, v_a_5280_);
                            lean_ctor_set(v___x_5303_, 1, v___x_5302_);
                            return v___x_5303_;
                        }
                    }
                } else {
                    v___x_5304_ = lean_box(0);
                    v___x_5305_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_5305_, 0, v_a_5280_);
                    lean_ctor_set(v___x_5305_, 1, v___x_5304_);
                    return v___x_5305_;
                }
            }
            1 => {
                v___x_5293_ = lean_string_utf8_next_fast(v_fst_5281_, v_snd_5282_);
                lean_dec(v_snd_5282_);
                if v_isShared_5292_ == 0 {
                    lean_ctor_set(v___x_5291_, 1, v___x_5293_);
                    v___x_5295_ = v___x_5291_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5298_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5298_, 0, v_fst_5281_);
                    lean_ctor_set(v_reuseFailAlloc_5298_, 1, v___x_5293_);
                    v___x_5295_ = v_reuseFailAlloc_5298_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5296_ = l_Lean_JsonRpc_instInhabitedRequestID_default___closed__0;
                v___x_5297_ = l_Lean_Json_Parser_strCore(v___x_5296_, v___x_5295_);
                return v___x_5297_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseRequestID(
    mut v_a_5306_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_5308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_5309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5312_: u8 = 0;
    let mut v___x_5313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5317_: u8 = 0;
    let mut v_pos_5318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_5319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5322_: u8 = 0;
    let mut v_snd_5323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5325_: u8 = 0;
    let mut v___x_5327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_5330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_5331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5334_: u8 = 0;
    let mut v___x_5335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5339_: u8 = 0;
    let mut v_pos_5340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_5341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5344_: u8 = 0;
    let mut v_snd_5345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5346_: u8 = 0;
    let mut v___x_5348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_5352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5355_: u8 = 0;
    let mut v___x_5356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5360_: u8 = 0;
    let mut v_unused_5361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_5362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_5363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5366_: u8 = 0;
    let mut v___x_5368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5370_: u8 = 0;
    let mut v_isSharedCheck_5371_: u8 = 0;
    let mut v_isSharedCheck_5372_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_a_5306_);
                v___x_5307_ = l_Lean_Json_Parser_num(v_a_5306_);
                if lean_obj_tag(v___x_5307_) == 0 {
                    lean_dec_ref(v_a_5306_);
                    v_pos_5308_ = lean_ctor_get(v___x_5307_, 0);
                    v_res_5309_ = lean_ctor_get(v___x_5307_, 1);
                    v_isSharedCheck_5317_ = (!lean_is_exclusive(v___x_5307_)) as u8;
                    if v_isSharedCheck_5317_ == 0 {
                        v___x_5311_ = v___x_5307_;
                        v_isShared_5312_ = v_isSharedCheck_5317_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_res_5309_);
                        lean_inc(v_pos_5308_);
                        lean_dec(v___x_5307_);
                        v___x_5311_ = lean_box(0);
                        v_isShared_5312_ = v_isSharedCheck_5317_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_pos_5318_ = lean_ctor_get(v___x_5307_, 0);
                    v_err_5319_ = lean_ctor_get(v___x_5307_, 1);
                    v_isSharedCheck_5372_ = (!lean_is_exclusive(v___x_5307_)) as u8;
                    if v_isSharedCheck_5372_ == 0 {
                        v___x_5321_ = v___x_5307_;
                        v_isShared_5322_ = v_isSharedCheck_5372_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_err_5319_);
                        lean_inc(v_pos_5318_);
                        lean_dec(v___x_5307_);
                        v___x_5321_ = lean_box(0);
                        v_isShared_5322_ = v_isSharedCheck_5372_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5313_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_5313_, 0, v_res_5309_);
                if v_isShared_5312_ == 0 {
                    lean_ctor_set(v___x_5311_, 1, v___x_5313_);
                    v___x_5315_ = v___x_5311_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5316_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5316_, 0, v_pos_5308_);
                    lean_ctor_set(v_reuseFailAlloc_5316_, 1, v___x_5313_);
                    v___x_5315_ = v_reuseFailAlloc_5316_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5315_;
            }
            3 => {
                v_snd_5323_ = lean_ctor_get(v_a_5306_, 1);
                lean_inc(v_snd_5323_);
                lean_dec_ref(v_a_5306_);
                v_snd_5324_ = lean_ctor_get(v_pos_5318_, 1);
                v___x_5325_ = lean_nat_dec_eq(v_snd_5323_, v_snd_5324_);
                lean_dec(v_snd_5323_);
                if v___x_5325_ == 0 {
                    if v_isShared_5322_ == 0 {
                        v___x_5327_ = v___x_5321_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5328_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5328_, 0, v_pos_5318_);
                        lean_ctor_set(v_reuseFailAlloc_5328_, 1, v_err_5319_);
                        v___x_5327_ = v_reuseFailAlloc_5328_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_inc(v_snd_5324_);
                    lean_del_object(v___x_5321_);
                    lean_dec(v_err_5319_);
                    v___x_5329_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v_pos_5318_);
                    if lean_obj_tag(v___x_5329_) == 0 {
                        lean_dec(v_snd_5324_);
                        v_pos_5330_ = lean_ctor_get(v___x_5329_, 0);
                        v_res_5331_ = lean_ctor_get(v___x_5329_, 1);
                        v_isSharedCheck_5339_ = (!lean_is_exclusive(v___x_5329_)) as u8;
                        if v_isSharedCheck_5339_ == 0 {
                            v___x_5333_ = v___x_5329_;
                            v_isShared_5334_ = v_isSharedCheck_5339_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_res_5331_);
                            lean_inc(v_pos_5330_);
                            lean_dec(v___x_5329_);
                            v___x_5333_ = lean_box(0);
                            v_isShared_5334_ = v_isSharedCheck_5339_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v_pos_5340_ = lean_ctor_get(v___x_5329_, 0);
                        v_err_5341_ = lean_ctor_get(v___x_5329_, 1);
                        v_isSharedCheck_5371_ = (!lean_is_exclusive(v___x_5329_)) as u8;
                        if v_isSharedCheck_5371_ == 0 {
                            v___x_5343_ = v___x_5329_;
                            v_isShared_5344_ = v_isSharedCheck_5371_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_err_5341_);
                            lean_inc(v_pos_5340_);
                            lean_dec(v___x_5329_);
                            v___x_5343_ = lean_box(0);
                            v_isShared_5344_ = v_isSharedCheck_5371_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            4 => {
                return v___x_5327_;
            }
            5 => {
                v___x_5335_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5335_, 0, v_res_5331_);
                if v_isShared_5334_ == 0 {
                    lean_ctor_set(v___x_5333_, 1, v___x_5335_);
                    v___x_5337_ = v___x_5333_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5338_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5338_, 0, v_pos_5330_);
                    lean_ctor_set(v_reuseFailAlloc_5338_, 1, v___x_5335_);
                    v___x_5337_ = v_reuseFailAlloc_5338_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5337_;
            }
            7 => {
                v_snd_5345_ = lean_ctor_get(v_pos_5340_, 1);
                v___x_5346_ = lean_nat_dec_eq(v_snd_5324_, v_snd_5345_);
                lean_dec(v_snd_5324_);
                if v___x_5346_ == 0 {
                    if v_isShared_5344_ == 0 {
                        v___x_5348_ = v___x_5343_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_5349_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5349_, 0, v_pos_5340_);
                        lean_ctor_set(v_reuseFailAlloc_5349_, 1, v_err_5341_);
                        v___x_5348_ = v_reuseFailAlloc_5349_;
                        state = 8;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5343_);
                    lean_dec(v_err_5341_);
                    v___x_5350_ = l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__1;
                    v___x_5351_ = l_Std_Internal_Parsec_String_pstring(v___x_5350_, v_pos_5340_);
                    if lean_obj_tag(v___x_5351_) == 0 {
                        v_pos_5352_ = lean_ctor_get(v___x_5351_, 0);
                        v_isSharedCheck_5360_ = (!lean_is_exclusive(v___x_5351_)) as u8;
                        if v_isSharedCheck_5360_ == 0 {
                            v_unused_5361_ = lean_ctor_get(v___x_5351_, 1);
                            lean_dec(v_unused_5361_);
                            v___x_5354_ = v___x_5351_;
                            v_isShared_5355_ = v_isSharedCheck_5360_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_pos_5352_);
                            lean_dec(v___x_5351_);
                            v___x_5354_ = lean_box(0);
                            v_isShared_5355_ = v_isSharedCheck_5360_;
                            state = 9;
                            continue;
                        }
                    } else {
                        v_pos_5362_ = lean_ctor_get(v___x_5351_, 0);
                        v_err_5363_ = lean_ctor_get(v___x_5351_, 1);
                        v_isSharedCheck_5370_ = (!lean_is_exclusive(v___x_5351_)) as u8;
                        if v_isSharedCheck_5370_ == 0 {
                            v___x_5365_ = v___x_5351_;
                            v_isShared_5366_ = v_isSharedCheck_5370_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_err_5363_);
                            lean_inc(v_pos_5362_);
                            lean_dec(v___x_5351_);
                            v___x_5365_ = lean_box(0);
                            v_isShared_5366_ = v_isSharedCheck_5370_;
                            state = 11;
                            continue;
                        }
                    }
                }
            }
            8 => {
                return v___x_5348_;
            }
            9 => {
                v___x_5356_ = lean_box(2);
                if v_isShared_5355_ == 0 {
                    lean_ctor_set(v___x_5354_, 1, v___x_5356_);
                    v___x_5358_ = v___x_5354_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5359_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5359_, 0, v_pos_5352_);
                    lean_ctor_set(v_reuseFailAlloc_5359_, 1, v___x_5356_);
                    v___x_5358_ = v_reuseFailAlloc_5359_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5358_;
            }
            11 => {
                if v_isShared_5366_ == 0 {
                    v___x_5368_ = v___x_5365_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5369_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5369_, 0, v_pos_5362_);
                    lean_ctor_set(v_reuseFailAlloc_5369_, 1, v_err_5363_);
                    v___x_5368_ = v_reuseFailAlloc_5369_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5368_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0(
    mut v_j_5373_: *mut LeanObject,
    mut v_k_5374_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_5376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5379_: u8 = 0;
    let mut v___x_5381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5384_: u8 = 0;
    let mut v_n_5385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5388_: u8 = 0;
    let mut v___x_5390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5393_: u8 = 0;
    let mut v___x_5394_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5375_ = l_Lean_Json_getObjValD(v_j_5373_, v_k_5374_);
                match lean_obj_tag(v___x_5375_) {
                    3 => {
                        v_s_5376_ = lean_ctor_get(v___x_5375_, 0);
                        v_isSharedCheck_5384_ = (!lean_is_exclusive(v___x_5375_)) as u8;
                        if v_isSharedCheck_5384_ == 0 {
                            v___x_5378_ = v___x_5375_;
                            v_isShared_5379_ = v_isSharedCheck_5384_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_s_5376_);
                            lean_dec(v___x_5375_);
                            v___x_5378_ = lean_box(0);
                            v_isShared_5379_ = v_isSharedCheck_5384_;
                            state = 1;
                            continue;
                        }
                    }
                    2 => {
                        v_n_5385_ = lean_ctor_get(v___x_5375_, 0);
                        v_isSharedCheck_5393_ = (!lean_is_exclusive(v___x_5375_)) as u8;
                        if v_isSharedCheck_5393_ == 0 {
                            v___x_5387_ = v___x_5375_;
                            v_isShared_5388_ = v_isSharedCheck_5393_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_n_5385_);
                            lean_dec(v___x_5375_);
                            v___x_5387_ = lean_box(0);
                            v_isShared_5388_ = v_isSharedCheck_5393_;
                            state = 3;
                            continue;
                        }
                    }
                    _ => {
                        lean_dec(v___x_5375_);
                        v___x_5394_ = l_Lean_JsonRpc_instFromJsonRequestID___lam__0___closed__1;
                        return v___x_5394_;
                    }
                }
            }
            1 => {
                if v_isShared_5379_ == 0 {
                    lean_ctor_set_tag(v___x_5378_, 0);
                    v___x_5381_ = v___x_5378_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5383_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5383_, 0, v_s_5376_);
                    v___x_5381_ = v_reuseFailAlloc_5383_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5382_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_5382_, 0, v___x_5381_);
                return v___x_5382_;
            }
            3 => {
                if v_isShared_5388_ == 0 {
                    lean_ctor_set_tag(v___x_5387_, 1);
                    v___x_5390_ = v___x_5387_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5392_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5392_, 0, v_n_5385_);
                    v___x_5390_ = v_reuseFailAlloc_5392_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5391_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_5391_, 0, v___x_5390_);
                return v___x_5391_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0___boxed(
    mut v_j_5395_: *mut LeanObject,
    mut v_k_5396_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5397_: *mut LeanObject = core::ptr::null_mut();
    v_res_5397_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0(v_j_5395_, v_k_5396_);
    lean_dec_ref(v_k_5396_);
    return v_res_5397_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1(
    mut v_j_5398_: *mut LeanObject,
    mut v_k_5399_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_5403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mantissa_5404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exponent_5405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5407_: u8 = 0;
    let mut v___x_5408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5409_: u8 = 0;
    let mut v___x_5410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5411_: u8 = 0;
    let mut v___x_5412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5413_: u8 = 0;
    let mut v___x_5414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5415_: u8 = 0;
    let mut v___x_5416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5417_: u8 = 0;
    let mut v___x_5418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5419_: u8 = 0;
    let mut v___x_5420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5421_: u8 = 0;
    let mut v___x_5422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5423_: u8 = 0;
    let mut v___x_5424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5425_: u8 = 0;
    let mut v___x_5426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5427_: u8 = 0;
    let mut v___x_5428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5429_: u8 = 0;
    let mut v___x_5430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5431_: u8 = 0;
    let mut v___x_5432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5434_: u8 = 0;
    let mut v___x_5435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5437_: u8 = 0;
    let mut v___x_5438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5440_: u8 = 0;
    let mut v___x_5441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5443_: u8 = 0;
    let mut v___x_5444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5446_: u8 = 0;
    let mut v___x_5447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5449_: u8 = 0;
    let mut v___x_5450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5452_: u8 = 0;
    let mut v___x_5453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5455_: u8 = 0;
    let mut v___x_5456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5458_: u8 = 0;
    let mut v___x_5459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5461_: u8 = 0;
    let mut v___x_5462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5464_: u8 = 0;
    let mut v___x_5465_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5402_ = l_Lean_Json_getObjValD(v_j_5398_, v_k_5399_);
                if lean_obj_tag(v___x_5402_) == 2 {
                    v_n_5403_ = lean_ctor_get(v___x_5402_, 0);
                    lean_inc_ref(v_n_5403_);
                    lean_dec_ref_known(v___x_5402_, 1);
                    v_mantissa_5404_ = lean_ctor_get(v_n_5403_, 0);
                    lean_inc(v_mantissa_5404_);
                    v_exponent_5405_ = lean_ctor_get(v_n_5403_, 1);
                    lean_inc(v_exponent_5405_);
                    lean_dec_ref(v_n_5403_);
                    v___x_5406_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3_once
                        ),
                        _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3,
                    );
                    v___x_5407_ = lean_int_dec_eq(v_mantissa_5404_, v___x_5406_);
                    if v___x_5407_ == 0 {
                        v___x_5408_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5_once
                            ),
                            _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5,
                        );
                        v___x_5409_ = lean_int_dec_eq(v_mantissa_5404_, v___x_5408_);
                        if v___x_5409_ == 0 {
                            v___x_5410_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7_once
                                ),
                                _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7,
                            );
                            v___x_5411_ = lean_int_dec_eq(v_mantissa_5404_, v___x_5410_);
                            if v___x_5411_ == 0 {
                                v___x_5412_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9), core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9_once), _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9);
                                v___x_5413_ = lean_int_dec_eq(v_mantissa_5404_, v___x_5412_);
                                if v___x_5413_ == 0 {
                                    v___x_5414_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11), core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11_once), _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11);
                                    v___x_5415_ = lean_int_dec_eq(v_mantissa_5404_, v___x_5414_);
                                    if v___x_5415_ == 0 {
                                        v___x_5416_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13), core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13_once), _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13);
                                        v___x_5417_ =
                                            lean_int_dec_eq(v_mantissa_5404_, v___x_5416_);
                                        if v___x_5417_ == 0 {
                                            v___x_5418_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15), core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15_once), _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15);
                                            v___x_5419_ =
                                                lean_int_dec_eq(v_mantissa_5404_, v___x_5418_);
                                            if v___x_5419_ == 0 {
                                                v___x_5420_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17), core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17_once), _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17);
                                                v___x_5421_ =
                                                    lean_int_dec_eq(v_mantissa_5404_, v___x_5420_);
                                                if v___x_5421_ == 0 {
                                                    v___x_5422_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19), core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19_once), _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19);
                                                    v___x_5423_ = lean_int_dec_eq(
                                                        v_mantissa_5404_,
                                                        v___x_5422_,
                                                    );
                                                    if v___x_5423_ == 0 {
                                                        v___x_5424_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21), core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21_once), _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21);
                                                        v___x_5425_ = lean_int_dec_eq(
                                                            v_mantissa_5404_,
                                                            v___x_5424_,
                                                        );
                                                        if v___x_5425_ == 0 {
                                                            v___x_5426_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23), core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23_once), _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23);
                                                            v___x_5427_ = lean_int_dec_eq(
                                                                v_mantissa_5404_,
                                                                v___x_5426_,
                                                            );
                                                            if v___x_5427_ == 0 {
                                                                v___x_5428_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25), core::ptr::addr_of_mut!(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25_once), _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25);
                                                                v___x_5429_ = lean_int_dec_eq(
                                                                    v_mantissa_5404_,
                                                                    v___x_5428_,
                                                                );
                                                                lean_dec(v_mantissa_5404_);
                                                                if v___x_5429_ == 0 {
                                                                    lean_dec(v_exponent_5405_);
                                                                    state = 1;
                                                                    continue;
                                                                } else {
                                                                    v___x_5430_ =
                                                                        lean_unsigned_to_nat(0);
                                                                    v___x_5431_ = lean_nat_dec_eq(
                                                                        v_exponent_5405_,
                                                                        v___x_5430_,
                                                                    );
                                                                    lean_dec(v_exponent_5405_);
                                                                    if v___x_5431_ == 0 {
                                                                        state = 1;
                                                                        continue;
                                                                    } else {
                                                                        v___x_5432_ = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__26;
                                                                        return v___x_5432_;
                                                                    }
                                                                }
                                                            } else {
                                                                lean_dec(v_mantissa_5404_);
                                                                v___x_5433_ =
                                                                    lean_unsigned_to_nat(0);
                                                                v___x_5434_ = lean_nat_dec_eq(
                                                                    v_exponent_5405_,
                                                                    v___x_5433_,
                                                                );
                                                                lean_dec(v_exponent_5405_);
                                                                if v___x_5434_ == 0 {
                                                                    state = 1;
                                                                    continue;
                                                                } else {
                                                                    v___x_5435_ = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__27;
                                                                    return v___x_5435_;
                                                                }
                                                            }
                                                        } else {
                                                            lean_dec(v_mantissa_5404_);
                                                            v___x_5436_ = lean_unsigned_to_nat(0);
                                                            v___x_5437_ = lean_nat_dec_eq(
                                                                v_exponent_5405_,
                                                                v___x_5436_,
                                                            );
                                                            lean_dec(v_exponent_5405_);
                                                            if v___x_5437_ == 0 {
                                                                state = 1;
                                                                continue;
                                                            } else {
                                                                v___x_5438_ = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__28;
                                                                return v___x_5438_;
                                                            }
                                                        }
                                                    } else {
                                                        lean_dec(v_mantissa_5404_);
                                                        v___x_5439_ = lean_unsigned_to_nat(0);
                                                        v___x_5440_ = lean_nat_dec_eq(
                                                            v_exponent_5405_,
                                                            v___x_5439_,
                                                        );
                                                        lean_dec(v_exponent_5405_);
                                                        if v___x_5440_ == 0 {
                                                            state = 1;
                                                            continue;
                                                        } else {
                                                            v___x_5441_ = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__29;
                                                            return v___x_5441_;
                                                        }
                                                    }
                                                } else {
                                                    lean_dec(v_mantissa_5404_);
                                                    v___x_5442_ = lean_unsigned_to_nat(0);
                                                    v___x_5443_ = lean_nat_dec_eq(
                                                        v_exponent_5405_,
                                                        v___x_5442_,
                                                    );
                                                    lean_dec(v_exponent_5405_);
                                                    if v___x_5443_ == 0 {
                                                        state = 1;
                                                        continue;
                                                    } else {
                                                        v___x_5444_ = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__30;
                                                        return v___x_5444_;
                                                    }
                                                }
                                            } else {
                                                lean_dec(v_mantissa_5404_);
                                                v___x_5445_ = lean_unsigned_to_nat(0);
                                                v___x_5446_ =
                                                    lean_nat_dec_eq(v_exponent_5405_, v___x_5445_);
                                                lean_dec(v_exponent_5405_);
                                                if v___x_5446_ == 0 {
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    v___x_5447_ = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__31;
                                                    return v___x_5447_;
                                                }
                                            }
                                        } else {
                                            lean_dec(v_mantissa_5404_);
                                            v___x_5448_ = lean_unsigned_to_nat(0);
                                            v___x_5449_ =
                                                lean_nat_dec_eq(v_exponent_5405_, v___x_5448_);
                                            lean_dec(v_exponent_5405_);
                                            if v___x_5449_ == 0 {
                                                state = 1;
                                                continue;
                                            } else {
                                                v___x_5450_ = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__32;
                                                return v___x_5450_;
                                            }
                                        }
                                    } else {
                                        lean_dec(v_mantissa_5404_);
                                        v___x_5451_ = lean_unsigned_to_nat(0);
                                        v___x_5452_ =
                                            lean_nat_dec_eq(v_exponent_5405_, v___x_5451_);
                                        lean_dec(v_exponent_5405_);
                                        if v___x_5452_ == 0 {
                                            state = 1;
                                            continue;
                                        } else {
                                            v___x_5453_ = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__33;
                                            return v___x_5453_;
                                        }
                                    }
                                } else {
                                    lean_dec(v_mantissa_5404_);
                                    v___x_5454_ = lean_unsigned_to_nat(0);
                                    v___x_5455_ = lean_nat_dec_eq(v_exponent_5405_, v___x_5454_);
                                    lean_dec(v_exponent_5405_);
                                    if v___x_5455_ == 0 {
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_5456_ = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__34;
                                        return v___x_5456_;
                                    }
                                }
                            } else {
                                lean_dec(v_mantissa_5404_);
                                v___x_5457_ = lean_unsigned_to_nat(0);
                                v___x_5458_ = lean_nat_dec_eq(v_exponent_5405_, v___x_5457_);
                                lean_dec(v_exponent_5405_);
                                if v___x_5458_ == 0 {
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_5459_ =
                                        l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__35;
                                    return v___x_5459_;
                                }
                            }
                        } else {
                            lean_dec(v_mantissa_5404_);
                            v___x_5460_ = lean_unsigned_to_nat(0);
                            v___x_5461_ = lean_nat_dec_eq(v_exponent_5405_, v___x_5460_);
                            lean_dec(v_exponent_5405_);
                            if v___x_5461_ == 0 {
                                state = 1;
                                continue;
                            } else {
                                v___x_5462_ =
                                    l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__36;
                                return v___x_5462_;
                            }
                        }
                    } else {
                        lean_dec(v_mantissa_5404_);
                        v___x_5463_ = lean_unsigned_to_nat(0);
                        v___x_5464_ = lean_nat_dec_eq(v_exponent_5405_, v___x_5463_);
                        lean_dec(v_exponent_5405_);
                        if v___x_5464_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            v___x_5465_ =
                                l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__37;
                            return v___x_5465_;
                        }
                    }
                } else {
                    lean_dec(v___x_5402_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5401_ = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__1;
                return v___x_5401_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1___boxed(
    mut v_j_5466_: *mut LeanObject,
    mut v_k_5467_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5468_: *mut LeanObject = core::ptr::null_mut();
    v_res_5468_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1(v_j_5466_, v_k_5467_);
    lean_dec_ref(v_k_5467_);
    return v_res_5468_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(
    mut v_j_5469_: *mut LeanObject,
    mut v_k_5470_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5472_: *mut LeanObject = core::ptr::null_mut();
    v___x_5471_ = l_Lean_Json_getObjValD(v_j_5469_, v_k_5470_);
    v___x_5472_ = l_Lean_Json_getStr_x3f(v___x_5471_);
    return v___x_5472_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2___boxed(
    mut v_j_5473_: *mut LeanObject,
    mut v_k_5474_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5475_: *mut LeanObject = core::ptr::null_mut();
    v_res_5475_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_j_5473_, v_k_5474_);
    lean_dec_ref(v_k_5474_);
    return v_res_5475_;
}
pub unsafe fn l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser(
    mut v_input_5485_: *mut LeanObject,
    mut v_a_5486_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_5488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_5493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_5494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5497_: u8 = 0;
    let mut v___x_5498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5502_: u8 = 0;
    let mut v_pos_5503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_5504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5507_: u8 = 0;
    let mut v___x_5509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5511_: u8 = 0;
    let mut v_fst_5512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5515_: u8 = 0;
    let mut v___x_5517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5518_: u8 = 0;
    let mut v___x_5519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_5523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_5524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5527_: u8 = 0;
    let mut v_fst_5528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5531_: u8 = 0;
    let mut v___x_5533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5534_: u8 = 0;
    let mut v___x_5535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_5539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_5540_: u8 = 0;
    let mut v_message_5541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_x3f_5542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5557_: u8 = 0;
    let mut v___x_5558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5559_: u8 = 0;
    let mut v___x_5560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5561_: u8 = 0;
    let mut v___x_5562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5568_: u8 = 0;
    let mut v___x_5570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5573_: u8 = 0;
    let mut v_a_5574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_5578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5580_: u8 = 0;
    let mut v___x_5581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5599_: u8 = 0;
    let mut v_a_5600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5603_: u8 = 0;
    let mut v___x_5605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5606_: u8 = 0;
    let mut v_reuseFailAlloc_5607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5608_: u8 = 0;
    let mut v___x_5610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_5617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5620_: u8 = 0;
    let mut v_fst_5621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5624_: u8 = 0;
    let mut v___x_5625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5631_: u8 = 0;
    let mut v___x_5632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_5636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5639_: u8 = 0;
    let mut v_fst_5640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5643_: u8 = 0;
    let mut v___x_5644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5648_: u8 = 0;
    let mut v_unused_5649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_5650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_5651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5654_: u8 = 0;
    let mut v___x_5656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5658_: u8 = 0;
    let mut v_reuseFailAlloc_5659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5660_: u8 = 0;
    let mut v_unused_5661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5664_: u8 = 0;
    let mut v_isSharedCheck_5665_: u8 = 0;
    let mut v_unused_5666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_5667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_5668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5671_: u8 = 0;
    let mut v___x_5673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5675_: u8 = 0;
    let mut v___x_5676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_5677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_5678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5681_: u8 = 0;
    let mut v___x_5683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5690_: u8 = 0;
    let mut v___x_5692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5693_: u8 = 0;
    let mut v___x_5694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_5698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5701_: u8 = 0;
    let mut v_fst_5702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5705_: u8 = 0;
    let mut v___x_5707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5708_: u8 = 0;
    let mut v___x_5709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_5713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5716_: u8 = 0;
    let mut v_fst_5717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5720_: u8 = 0;
    let mut v___x_5722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5723_: u8 = 0;
    let mut v___x_5724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_5728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_5729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5732_: u8 = 0;
    let mut v___x_5734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5739_: u8 = 0;
    let mut v___x_5740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5741_: u8 = 0;
    let mut v___x_5742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5753_: u8 = 0;
    let mut v___x_5755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5756_: u8 = 0;
    let mut v___x_5757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_5761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_5762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5765_: u8 = 0;
    let mut v___x_5766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5770_: u8 = 0;
    let mut v_pos_5771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_5772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5775_: u8 = 0;
    let mut v___x_5777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5779_: u8 = 0;
    let mut v_reuseFailAlloc_5780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5781_: u8 = 0;
    let mut v_unused_5782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5784_: u8 = 0;
    let mut v_pos_5785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_5786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5789_: u8 = 0;
    let mut v___x_5791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5793_: u8 = 0;
    let mut v_reuseFailAlloc_5794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5795_: u8 = 0;
    let mut v_unused_5796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5802_: u8 = 0;
    let mut v_unused_5803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_5804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_5805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5808_: u8 = 0;
    let mut v___x_5810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5812_: u8 = 0;
    let mut v_reuseFailAlloc_5813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5814_: u8 = 0;
    let mut v_unused_5815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5821_: u8 = 0;
    let mut v_unused_5822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_5823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_5824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5827_: u8 = 0;
    let mut v___x_5829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5831_: u8 = 0;
    let mut v_reuseFailAlloc_5832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5833_: u8 = 0;
    let mut v_unused_5834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5836_: u8 = 0;
    let mut v_pos_5837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_5838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5841_: u8 = 0;
    let mut v___x_5843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5845_: u8 = 0;
    let mut v_reuseFailAlloc_5846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5847_: u8 = 0;
    let mut v_unused_5848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5854_: u8 = 0;
    let mut v_pos_5855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_5856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5859_: u8 = 0;
    let mut v___x_5861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5863_: u8 = 0;
    let mut v_reuseFailAlloc_5864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5865_: u8 = 0;
    let mut v_unused_5866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5869_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_5512_ = lean_ctor_get(v_a_5486_, 0);
                v_snd_5513_ = lean_ctor_get(v_a_5486_, 1);
                v___x_5514_ = lean_string_utf8_byte_size(v_fst_5512_);
                v___x_5515_ = lean_nat_dec_eq(v_snd_5513_, v___x_5514_);
                if v___x_5515_ == 0 {
                    lean_inc(v_snd_5513_);
                    lean_inc(v_fst_5512_);
                    v_isSharedCheck_5865_ = (!lean_is_exclusive(v_a_5486_)) as u8;
                    if v_isSharedCheck_5865_ == 0 {
                        v_unused_5866_ = lean_ctor_get(v_a_5486_, 1);
                        lean_dec(v_unused_5866_);
                        v_unused_5867_ = lean_ctor_get(v_a_5486_, 0);
                        lean_dec(v_unused_5867_);
                        v___x_5517_ = v_a_5486_;
                        v_isShared_5518_ = v_isSharedCheck_5865_;
                        state = 6;
                        continue;
                    } else {
                        lean_dec(v_a_5486_);
                        v___x_5517_ = lean_box(0);
                        v_isShared_5518_ = v_isSharedCheck_5865_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_input_5485_);
                    v___x_5868_ = lean_box(0);
                    v___x_5869_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_5869_, 0, v_a_5486_);
                    lean_ctor_set(v___x_5869_, 1, v___x_5868_);
                    return v___x_5869_;
                }
            }
            1 => {
                v___x_5490_ = lean_string_utf8_next_fast(v___y_5488_, v___y_5489_);
                lean_dec(v___y_5489_);
                v___x_5491_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5491_, 0, v___y_5488_);
                lean_ctor_set(v___x_5491_, 1, v___x_5490_);
                v___x_5492_ =
                    l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(
                        v___x_5491_,
                    );
                if lean_obj_tag(v___x_5492_) == 0 {
                    v_pos_5493_ = lean_ctor_get(v___x_5492_, 0);
                    v_res_5494_ = lean_ctor_get(v___x_5492_, 1);
                    v_isSharedCheck_5502_ = (!lean_is_exclusive(v___x_5492_)) as u8;
                    if v_isSharedCheck_5502_ == 0 {
                        v___x_5496_ = v___x_5492_;
                        v_isShared_5497_ = v_isSharedCheck_5502_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_res_5494_);
                        lean_inc(v_pos_5493_);
                        lean_dec(v___x_5492_);
                        v___x_5496_ = lean_box(0);
                        v_isShared_5497_ = v_isSharedCheck_5502_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_pos_5503_ = lean_ctor_get(v___x_5492_, 0);
                    v_err_5504_ = lean_ctor_get(v___x_5492_, 1);
                    v_isSharedCheck_5511_ = (!lean_is_exclusive(v___x_5492_)) as u8;
                    if v_isSharedCheck_5511_ == 0 {
                        v___x_5506_ = v___x_5492_;
                        v_isShared_5507_ = v_isSharedCheck_5511_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_err_5504_);
                        lean_inc(v_pos_5503_);
                        lean_dec(v___x_5492_);
                        v___x_5506_ = lean_box(0);
                        v_isShared_5507_ = v_isSharedCheck_5511_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5498_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_5498_, 0, v_res_5494_);
                if v_isShared_5497_ == 0 {
                    lean_ctor_set(v___x_5496_, 1, v___x_5498_);
                    v___x_5500_ = v___x_5496_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5501_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5501_, 0, v_pos_5493_);
                    lean_ctor_set(v_reuseFailAlloc_5501_, 1, v___x_5498_);
                    v___x_5500_ = v_reuseFailAlloc_5501_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5500_;
            }
            4 => {
                if v_isShared_5507_ == 0 {
                    v___x_5509_ = v___x_5506_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5510_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5510_, 0, v_pos_5503_);
                    lean_ctor_set(v_reuseFailAlloc_5510_, 1, v_err_5504_);
                    v___x_5509_ = v_reuseFailAlloc_5510_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5509_;
            }
            6 => {
                v___x_5519_ = lean_string_utf8_next_fast(v_fst_5512_, v_snd_5513_);
                lean_dec(v_snd_5513_);
                if v_isShared_5518_ == 0 {
                    lean_ctor_set(v___x_5517_, 1, v___x_5519_);
                    v___x_5521_ = v___x_5517_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5864_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5864_, 0, v_fst_5512_);
                    lean_ctor_set(v_reuseFailAlloc_5864_, 1, v___x_5519_);
                    v___x_5521_ = v_reuseFailAlloc_5864_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_5522_ =
                    l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(
                        v___x_5521_,
                    );
                if lean_obj_tag(v___x_5522_) == 0 {
                    v_pos_5523_ = lean_ctor_get(v___x_5522_, 0);
                    v_res_5524_ = lean_ctor_get(v___x_5522_, 1);
                    v_isSharedCheck_5854_ = (!lean_is_exclusive(v___x_5522_)) as u8;
                    if v_isSharedCheck_5854_ == 0 {
                        v___x_5526_ = v___x_5522_;
                        v_isShared_5527_ = v_isSharedCheck_5854_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_res_5524_);
                        lean_inc(v_pos_5523_);
                        lean_dec(v___x_5522_);
                        v___x_5526_ = lean_box(0);
                        v_isShared_5527_ = v_isSharedCheck_5854_;
                        state = 8;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_input_5485_);
                    v_pos_5855_ = lean_ctor_get(v___x_5522_, 0);
                    v_err_5856_ = lean_ctor_get(v___x_5522_, 1);
                    v_isSharedCheck_5863_ = (!lean_is_exclusive(v___x_5522_)) as u8;
                    if v_isSharedCheck_5863_ == 0 {
                        v___x_5858_ = v___x_5522_;
                        v_isShared_5859_ = v_isSharedCheck_5863_;
                        state = 66;
                        continue;
                    } else {
                        lean_inc(v_err_5856_);
                        lean_inc(v_pos_5855_);
                        lean_dec(v___x_5522_);
                        v___x_5858_ = lean_box(0);
                        v_isShared_5859_ = v_isSharedCheck_5863_;
                        state = 66;
                        continue;
                    }
                }
            }
            8 => {
                v_fst_5528_ = lean_ctor_get(v_pos_5523_, 0);
                v_snd_5529_ = lean_ctor_get(v_pos_5523_, 1);
                v___x_5530_ = lean_string_utf8_byte_size(v_fst_5528_);
                v___x_5531_ = lean_nat_dec_eq(v_snd_5529_, v___x_5530_);
                if v___x_5531_ == 0 {
                    lean_inc(v_snd_5529_);
                    lean_inc(v_fst_5528_);
                    v_isSharedCheck_5847_ = (!lean_is_exclusive(v_pos_5523_)) as u8;
                    if v_isSharedCheck_5847_ == 0 {
                        v_unused_5848_ = lean_ctor_get(v_pos_5523_, 1);
                        lean_dec(v_unused_5848_);
                        v_unused_5849_ = lean_ctor_get(v_pos_5523_, 0);
                        lean_dec(v_unused_5849_);
                        v___x_5533_ = v_pos_5523_;
                        v_isShared_5534_ = v_isSharedCheck_5847_;
                        state = 9;
                        continue;
                    } else {
                        lean_dec(v_pos_5523_);
                        v___x_5533_ = lean_box(0);
                        v_isShared_5534_ = v_isSharedCheck_5847_;
                        state = 9;
                        continue;
                    }
                } else {
                    lean_dec(v_res_5524_);
                    lean_dec_ref(v_input_5485_);
                    v___x_5850_ = lean_box(0);
                    if v_isShared_5527_ == 0 {
                        lean_ctor_set_tag(v___x_5526_, 1);
                        lean_ctor_set(v___x_5526_, 1, v___x_5850_);
                        v___x_5852_ = v___x_5526_;
                        state = 65;
                        continue;
                    } else {
                        v_reuseFailAlloc_5853_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5853_, 0, v_pos_5523_);
                        lean_ctor_set(v_reuseFailAlloc_5853_, 1, v___x_5850_);
                        v___x_5852_ = v_reuseFailAlloc_5853_;
                        state = 65;
                        continue;
                    }
                }
            }
            9 => {
                v___x_5535_ = lean_string_utf8_next_fast(v_fst_5528_, v_snd_5529_);
                lean_dec(v_snd_5529_);
                if v_isShared_5534_ == 0 {
                    lean_ctor_set(v___x_5533_, 1, v___x_5535_);
                    v___x_5537_ = v___x_5533_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5846_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5846_, 0, v_fst_5528_);
                    lean_ctor_set(v_reuseFailAlloc_5846_, 1, v___x_5535_);
                    v___x_5537_ = v_reuseFailAlloc_5846_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_5556_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4;
                v___x_5557_ = lean_string_dec_eq(v_res_5524_, v___x_5556_);
                if v___x_5557_ == 0 {
                    v___x_5558_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__0;
                    v___x_5559_ = lean_string_dec_eq(v_res_5524_, v___x_5558_);
                    if v___x_5559_ == 0 {
                        v___x_5560_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10;
                        v___x_5561_ = lean_string_dec_eq(v_res_5524_, v___x_5560_);
                        lean_dec(v_res_5524_);
                        if v___x_5561_ == 0 {
                            lean_del_object(v___x_5526_);
                            lean_dec_ref(v_input_5485_);
                            v___x_5562_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__3;
                            v___x_5563_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v___x_5563_, 0, v___x_5537_);
                            lean_ctor_set(v___x_5563_, 1, v___x_5562_);
                            return v___x_5563_;
                        } else {
                            v___x_5564_ = l_Lean_Json_parse(v_input_5485_);
                            if lean_obj_tag(v___x_5564_) == 0 {
                                lean_del_object(v___x_5526_);
                                v_a_5565_ = lean_ctor_get(v___x_5564_, 0);
                                v_isSharedCheck_5573_ = (!lean_is_exclusive(v___x_5564_)) as u8;
                                if v_isSharedCheck_5573_ == 0 {
                                    v___x_5567_ = v___x_5564_;
                                    v_isShared_5568_ = v_isSharedCheck_5573_;
                                    state = 16;
                                    continue;
                                } else {
                                    lean_inc(v_a_5565_);
                                    lean_dec(v___x_5564_);
                                    v___x_5567_ = lean_box(0);
                                    v_isShared_5568_ = v_isSharedCheck_5573_;
                                    state = 16;
                                    continue;
                                }
                            } else {
                                v_a_5574_ = lean_ctor_get(v___x_5564_, 0);
                                lean_inc_n(v_a_5574_, 2);
                                lean_dec_ref_known(v___x_5564_, 1);
                                v___x_5575_ = l_Lean_Json_getObjVal_x3f(v_a_5574_, v___x_5558_);
                                if lean_obj_tag(v___x_5575_) == 0 {
                                    lean_dec(v_a_5574_);
                                    lean_del_object(v___x_5526_);
                                    v_a_5576_ = lean_ctor_get(v___x_5575_, 0);
                                    lean_inc(v_a_5576_);
                                    lean_dec_ref_known(v___x_5575_, 1);
                                    v_a_5551_ = v_a_5576_;
                                    state = 14;
                                    continue;
                                } else {
                                    v_a_5577_ = lean_ctor_get(v___x_5575_, 0);
                                    lean_inc(v_a_5577_);
                                    lean_dec_ref_known(v___x_5575_, 1);
                                    if lean_obj_tag(v_a_5577_) == 3 {
                                        v_s_5578_ = lean_ctor_get(v_a_5577_, 0);
                                        lean_inc_ref(v_s_5578_);
                                        lean_dec_ref_known(v_a_5577_, 1);
                                        v___x_5579_ =
                                            l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__1;
                                        v___x_5580_ = lean_string_dec_eq(v_s_5578_, v___x_5579_);
                                        lean_dec_ref(v_s_5578_);
                                        if v___x_5580_ == 0 {
                                            lean_dec(v_a_5574_);
                                            lean_del_object(v___x_5526_);
                                            state = 15;
                                            continue;
                                        } else {
                                            lean_inc(v_a_5574_);
                                            v___x_5581_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0(v_a_5574_, v___x_5556_);
                                            if lean_obj_tag(v___x_5581_) == 0 {
                                                state = 21;
                                                continue;
                                            } else {
                                                v___x_5614_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
                                                lean_inc(v_a_5574_);
                                                v___x_5615_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_a_5574_, v___x_5614_);
                                                if lean_obj_tag(v___x_5615_) == 0 {
                                                    lean_dec_ref_known(v___x_5615_, 1);
                                                    state = 21;
                                                    continue;
                                                } else {
                                                    lean_dec_ref_known(v___x_5615_, 1);
                                                    lean_dec_ref_known(v___x_5581_, 1);
                                                    lean_dec(v_a_5574_);
                                                    lean_del_object(v___x_5526_);
                                                    state = 13;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        lean_dec(v_a_5577_);
                                        lean_dec(v_a_5574_);
                                        lean_del_object(v___x_5526_);
                                        state = 15;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        lean_del_object(v___x_5526_);
                        lean_dec(v_res_5524_);
                        lean_dec_ref(v_input_5485_);
                        v___x_5616_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_5537_);
                        if lean_obj_tag(v___x_5616_) == 0 {
                            v_pos_5617_ = lean_ctor_get(v___x_5616_, 0);
                            v_isSharedCheck_5665_ = (!lean_is_exclusive(v___x_5616_)) as u8;
                            if v_isSharedCheck_5665_ == 0 {
                                v_unused_5666_ = lean_ctor_get(v___x_5616_, 1);
                                lean_dec(v_unused_5666_);
                                v___x_5619_ = v___x_5616_;
                                v_isShared_5620_ = v_isSharedCheck_5665_;
                                state = 22;
                                continue;
                            } else {
                                lean_inc(v_pos_5617_);
                                lean_dec(v___x_5616_);
                                v___x_5619_ = lean_box(0);
                                v_isShared_5620_ = v_isSharedCheck_5665_;
                                state = 22;
                                continue;
                            }
                        } else {
                            v_pos_5667_ = lean_ctor_get(v___x_5616_, 0);
                            v_err_5668_ = lean_ctor_get(v___x_5616_, 1);
                            v_isSharedCheck_5675_ = (!lean_is_exclusive(v___x_5616_)) as u8;
                            if v_isSharedCheck_5675_ == 0 {
                                v___x_5670_ = v___x_5616_;
                                v_isShared_5671_ = v_isSharedCheck_5675_;
                                state = 31;
                                continue;
                            } else {
                                lean_inc(v_err_5668_);
                                lean_inc(v_pos_5667_);
                                lean_dec(v___x_5616_);
                                v___x_5670_ = lean_box(0);
                                v_isShared_5671_ = v_isSharedCheck_5675_;
                                state = 31;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_del_object(v___x_5526_);
                    lean_dec(v_res_5524_);
                    lean_dec_ref(v_input_5485_);
                    v___x_5676_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseRequestID(v___x_5537_);
                    if lean_obj_tag(v___x_5676_) == 0 {
                        v_pos_5677_ = lean_ctor_get(v___x_5676_, 0);
                        v_res_5678_ = lean_ctor_get(v___x_5676_, 1);
                        v_isSharedCheck_5836_ = (!lean_is_exclusive(v___x_5676_)) as u8;
                        if v_isSharedCheck_5836_ == 0 {
                            v___x_5680_ = v___x_5676_;
                            v_isShared_5681_ = v_isSharedCheck_5836_;
                            state = 33;
                            continue;
                        } else {
                            lean_inc(v_res_5678_);
                            lean_inc(v_pos_5677_);
                            lean_dec(v___x_5676_);
                            v___x_5680_ = lean_box(0);
                            v_isShared_5681_ = v_isSharedCheck_5836_;
                            state = 33;
                            continue;
                        }
                    } else {
                        v_pos_5837_ = lean_ctor_get(v___x_5676_, 0);
                        v_err_5838_ = lean_ctor_get(v___x_5676_, 1);
                        v_isSharedCheck_5845_ = (!lean_is_exclusive(v___x_5676_)) as u8;
                        if v_isSharedCheck_5845_ == 0 {
                            v___x_5840_ = v___x_5676_;
                            v_isShared_5841_ = v_isSharedCheck_5845_;
                            state = 63;
                            continue;
                        } else {
                            lean_inc(v_err_5838_);
                            lean_inc(v_pos_5837_);
                            lean_dec(v___x_5676_);
                            v___x_5840_ = lean_box(0);
                            v_isShared_5841_ = v_isSharedCheck_5845_;
                            state = 63;
                            continue;
                        }
                    }
                }
            }
            11 => {
                v___x_5543_ = lean_alloc_ctor(3, 3, (1) as u32);
                lean_ctor_set(v___x_5543_, 0, v_id_5539_);
                lean_ctor_set(v___x_5543_, 1, v_message_5541_);
                lean_ctor_set(v___x_5543_, 2, v_data_x3f_5542_);
                lean_ctor_set_uint8(
                    v___x_5543_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v_code_5540_,
                );
                if v_isShared_5527_ == 0 {
                    lean_ctor_set(v___x_5526_, 1, v___x_5543_);
                    lean_ctor_set(v___x_5526_, 0, v___x_5537_);
                    v___x_5545_ = v___x_5526_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5546_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5546_, 0, v___x_5537_);
                    lean_ctor_set(v_reuseFailAlloc_5546_, 1, v___x_5543_);
                    v___x_5545_ = v_reuseFailAlloc_5546_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5545_;
            }
            13 => {
                v___x_5548_ =
                    l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__1;
                v___x_5549_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_5549_, 0, v___x_5537_);
                lean_ctor_set(v___x_5549_, 1, v___x_5548_);
                return v___x_5549_;
            }
            14 => {
                v___x_5552_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_5552_, 0, v_a_5551_);
                v___x_5553_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_5553_, 0, v___x_5537_);
                lean_ctor_set(v___x_5553_, 1, v___x_5552_);
                return v___x_5553_;
            }
            15 => {
                v___x_5555_ = l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__0;
                v_a_5551_ = v___x_5555_;
                state = 14;
                continue;
            }
            16 => {
                if v_isShared_5568_ == 0 {
                    lean_ctor_set_tag(v___x_5567_, 1);
                    v___x_5570_ = v___x_5567_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_5572_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5572_, 0, v_a_5565_);
                    v___x_5570_ = v_reuseFailAlloc_5572_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_5571_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_5571_, 0, v___x_5537_);
                lean_ctor_set(v___x_5571_, 1, v___x_5570_);
                return v___x_5571_;
            }
            18 => {
                if lean_obj_tag(v___x_5581_) == 0 {
                    lean_dec(v_a_5574_);
                    lean_del_object(v___x_5526_);
                    v_a_5583_ = lean_ctor_get(v___x_5581_, 0);
                    lean_inc(v_a_5583_);
                    lean_dec_ref_known(v___x_5581_, 1);
                    v_a_5551_ = v_a_5583_;
                    state = 14;
                    continue;
                } else {
                    v_a_5584_ = lean_ctor_get(v___x_5581_, 0);
                    lean_inc(v_a_5584_);
                    lean_dec_ref_known(v___x_5581_, 1);
                    v___x_5585_ = l_Lean_Json_getObjVal_x3f(v_a_5574_, v___x_5560_);
                    if lean_obj_tag(v___x_5585_) == 0 {
                        lean_dec(v_a_5584_);
                        lean_del_object(v___x_5526_);
                        v_a_5586_ = lean_ctor_get(v___x_5585_, 0);
                        lean_inc(v_a_5586_);
                        lean_dec_ref_known(v___x_5585_, 1);
                        v_a_5551_ = v_a_5586_;
                        state = 14;
                        continue;
                    } else {
                        v_a_5587_ = lean_ctor_get(v___x_5585_, 0);
                        lean_inc_n(v_a_5587_, 2);
                        lean_dec_ref_known(v___x_5585_, 1);
                        v___x_5588_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11;
                        v___x_5589_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1(v_a_5587_, v___x_5588_);
                        if lean_obj_tag(v___x_5589_) == 0 {
                            lean_dec(v_a_5587_);
                            lean_dec(v_a_5584_);
                            lean_del_object(v___x_5526_);
                            v_a_5590_ = lean_ctor_get(v___x_5589_, 0);
                            lean_inc(v_a_5590_);
                            lean_dec_ref_known(v___x_5589_, 1);
                            v_a_5551_ = v_a_5590_;
                            state = 14;
                            continue;
                        } else {
                            v_a_5591_ = lean_ctor_get(v___x_5589_, 0);
                            lean_inc(v_a_5591_);
                            lean_dec_ref_known(v___x_5589_, 1);
                            v___x_5592_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8;
                            lean_inc(v_a_5587_);
                            v___x_5593_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_a_5587_, v___x_5592_);
                            if lean_obj_tag(v___x_5593_) == 0 {
                                lean_dec(v_a_5591_);
                                lean_dec(v_a_5587_);
                                lean_dec(v_a_5584_);
                                lean_del_object(v___x_5526_);
                                v_a_5594_ = lean_ctor_get(v___x_5593_, 0);
                                lean_inc(v_a_5594_);
                                lean_dec_ref_known(v___x_5593_, 1);
                                v_a_5551_ = v_a_5594_;
                                state = 14;
                                continue;
                            } else {
                                v_a_5595_ = lean_ctor_get(v___x_5593_, 0);
                                lean_inc(v_a_5595_);
                                lean_dec_ref_known(v___x_5593_, 1);
                                v___x_5596_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9;
                                v___x_5597_ = l_Lean_Json_getObjVal_x3f(v_a_5587_, v___x_5596_);
                                if lean_obj_tag(v___x_5597_) == 0 {
                                    lean_dec_ref_known(v___x_5597_, 1);
                                    v___x_5598_ = lean_box(0);
                                    v___x_5599_ = (lean_unbox(v_a_5591_) as u8);
                                    lean_dec(v_a_5591_);
                                    v_id_5539_ = v_a_5584_;
                                    v_code_5540_ = v___x_5599_;
                                    v_message_5541_ = v_a_5595_;
                                    v_data_x3f_5542_ = v___x_5598_;
                                    state = 11;
                                    continue;
                                } else {
                                    v_a_5600_ = lean_ctor_get(v___x_5597_, 0);
                                    v_isSharedCheck_5608_ = (!lean_is_exclusive(v___x_5597_)) as u8;
                                    if v_isSharedCheck_5608_ == 0 {
                                        v___x_5602_ = v___x_5597_;
                                        v_isShared_5603_ = v_isSharedCheck_5608_;
                                        state = 19;
                                        continue;
                                    } else {
                                        lean_inc(v_a_5600_);
                                        lean_dec(v___x_5597_);
                                        v___x_5602_ = lean_box(0);
                                        v_isShared_5603_ = v_isSharedCheck_5608_;
                                        state = 19;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            19 => {
                if v_isShared_5603_ == 0 {
                    v___x_5605_ = v___x_5602_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_5607_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5607_, 0, v_a_5600_);
                    v___x_5605_ = v_reuseFailAlloc_5607_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                v___x_5606_ = (lean_unbox(v_a_5591_) as u8);
                lean_dec(v_a_5591_);
                v_id_5539_ = v_a_5584_;
                v_code_5540_ = v___x_5606_;
                v_message_5541_ = v_a_5595_;
                v_data_x3f_5542_ = v___x_5605_;
                state = 11;
                continue;
            }
            21 => {
                v___x_5610_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
                lean_inc(v_a_5574_);
                v___x_5611_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_a_5574_, v___x_5610_);
                if lean_obj_tag(v___x_5611_) == 0 {
                    lean_dec_ref_known(v___x_5611_, 1);
                    if lean_obj_tag(v___x_5581_) == 0 {
                        state = 18;
                        continue;
                    } else {
                        v___x_5612_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7;
                        lean_inc(v_a_5574_);
                        v___x_5613_ = l_Lean_Json_getObjVal_x3f(v_a_5574_, v___x_5612_);
                        if lean_obj_tag(v___x_5613_) == 0 {
                            lean_dec_ref_known(v___x_5613_, 1);
                            state = 18;
                            continue;
                        } else {
                            lean_dec_ref_known(v___x_5613_, 1);
                            lean_dec_ref_known(v___x_5581_, 1);
                            lean_dec(v_a_5574_);
                            lean_del_object(v___x_5526_);
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref_known(v___x_5611_, 1);
                    lean_dec_ref(v___x_5581_);
                    lean_dec(v_a_5574_);
                    lean_del_object(v___x_5526_);
                    state = 13;
                    continue;
                }
            }
            22 => {
                v_fst_5621_ = lean_ctor_get(v_pos_5617_, 0);
                v_snd_5622_ = lean_ctor_get(v_pos_5617_, 1);
                v___x_5663_ = lean_string_utf8_byte_size(v_fst_5621_);
                v___x_5664_ = lean_nat_dec_eq(v_snd_5622_, v___x_5663_);
                if v___x_5664_ == 0 {
                    v___y_5624_ = v___x_5559_;
                    state = 23;
                    continue;
                } else {
                    v___y_5624_ = v___x_5557_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                if v___y_5624_ == 0 {
                    v___x_5625_ = lean_box(0);
                    if v_isShared_5620_ == 0 {
                        lean_ctor_set_tag(v___x_5619_, 1);
                        lean_ctor_set(v___x_5619_, 1, v___x_5625_);
                        v___x_5627_ = v___x_5619_;
                        state = 24;
                        continue;
                    } else {
                        v_reuseFailAlloc_5628_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5628_, 0, v_pos_5617_);
                        lean_ctor_set(v_reuseFailAlloc_5628_, 1, v___x_5625_);
                        v___x_5627_ = v_reuseFailAlloc_5628_;
                        state = 24;
                        continue;
                    }
                } else {
                    lean_inc(v_snd_5622_);
                    lean_inc(v_fst_5621_);
                    lean_del_object(v___x_5619_);
                    v_isSharedCheck_5660_ = (!lean_is_exclusive(v_pos_5617_)) as u8;
                    if v_isSharedCheck_5660_ == 0 {
                        v_unused_5661_ = lean_ctor_get(v_pos_5617_, 1);
                        lean_dec(v_unused_5661_);
                        v_unused_5662_ = lean_ctor_get(v_pos_5617_, 0);
                        lean_dec(v_unused_5662_);
                        v___x_5630_ = v_pos_5617_;
                        v_isShared_5631_ = v_isSharedCheck_5660_;
                        state = 25;
                        continue;
                    } else {
                        lean_dec(v_pos_5617_);
                        v___x_5630_ = lean_box(0);
                        v_isShared_5631_ = v_isSharedCheck_5660_;
                        state = 25;
                        continue;
                    }
                }
            }
            24 => {
                return v___x_5627_;
            }
            25 => {
                v___x_5632_ = lean_string_utf8_next_fast(v_fst_5621_, v_snd_5622_);
                lean_dec(v_snd_5622_);
                if v_isShared_5631_ == 0 {
                    lean_ctor_set(v___x_5630_, 1, v___x_5632_);
                    v___x_5634_ = v___x_5630_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_5659_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5659_, 0, v_fst_5621_);
                    lean_ctor_set(v_reuseFailAlloc_5659_, 1, v___x_5632_);
                    v___x_5634_ = v_reuseFailAlloc_5659_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                v___x_5635_ =
                    l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(
                        v___x_5634_,
                    );
                if lean_obj_tag(v___x_5635_) == 0 {
                    v_pos_5636_ = lean_ctor_get(v___x_5635_, 0);
                    v_isSharedCheck_5648_ = (!lean_is_exclusive(v___x_5635_)) as u8;
                    if v_isSharedCheck_5648_ == 0 {
                        v_unused_5649_ = lean_ctor_get(v___x_5635_, 1);
                        lean_dec(v_unused_5649_);
                        v___x_5638_ = v___x_5635_;
                        v_isShared_5639_ = v_isSharedCheck_5648_;
                        state = 27;
                        continue;
                    } else {
                        lean_inc(v_pos_5636_);
                        lean_dec(v___x_5635_);
                        v___x_5638_ = lean_box(0);
                        v_isShared_5639_ = v_isSharedCheck_5648_;
                        state = 27;
                        continue;
                    }
                } else {
                    v_pos_5650_ = lean_ctor_get(v___x_5635_, 0);
                    v_err_5651_ = lean_ctor_get(v___x_5635_, 1);
                    v_isSharedCheck_5658_ = (!lean_is_exclusive(v___x_5635_)) as u8;
                    if v_isSharedCheck_5658_ == 0 {
                        v___x_5653_ = v___x_5635_;
                        v_isShared_5654_ = v_isSharedCheck_5658_;
                        state = 29;
                        continue;
                    } else {
                        lean_inc(v_err_5651_);
                        lean_inc(v_pos_5650_);
                        lean_dec(v___x_5635_);
                        v___x_5653_ = lean_box(0);
                        v_isShared_5654_ = v_isSharedCheck_5658_;
                        state = 29;
                        continue;
                    }
                }
            }
            27 => {
                v_fst_5640_ = lean_ctor_get(v_pos_5636_, 0);
                v_snd_5641_ = lean_ctor_get(v_pos_5636_, 1);
                v___x_5642_ = lean_string_utf8_byte_size(v_fst_5640_);
                v___x_5643_ = lean_nat_dec_eq(v_snd_5641_, v___x_5642_);
                if v___x_5643_ == 0 {
                    lean_inc(v_snd_5641_);
                    lean_inc(v_fst_5640_);
                    lean_del_object(v___x_5638_);
                    lean_dec(v_pos_5636_);
                    v___y_5488_ = v_fst_5640_;
                    v___y_5489_ = v_snd_5641_;
                    state = 1;
                    continue;
                } else {
                    if v___x_5557_ == 0 {
                        v___x_5644_ = lean_box(0);
                        if v_isShared_5639_ == 0 {
                            lean_ctor_set_tag(v___x_5638_, 1);
                            lean_ctor_set(v___x_5638_, 1, v___x_5644_);
                            v___x_5646_ = v___x_5638_;
                            state = 28;
                            continue;
                        } else {
                            v_reuseFailAlloc_5647_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_5647_, 0, v_pos_5636_);
                            lean_ctor_set(v_reuseFailAlloc_5647_, 1, v___x_5644_);
                            v___x_5646_ = v_reuseFailAlloc_5647_;
                            state = 28;
                            continue;
                        }
                    } else {
                        lean_inc(v_snd_5641_);
                        lean_inc(v_fst_5640_);
                        lean_del_object(v___x_5638_);
                        lean_dec(v_pos_5636_);
                        v___y_5488_ = v_fst_5640_;
                        v___y_5489_ = v_snd_5641_;
                        state = 1;
                        continue;
                    }
                }
            }
            28 => {
                return v___x_5646_;
            }
            29 => {
                if v_isShared_5654_ == 0 {
                    v___x_5656_ = v___x_5653_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_5657_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5657_, 0, v_pos_5650_);
                    lean_ctor_set(v_reuseFailAlloc_5657_, 1, v_err_5651_);
                    v___x_5656_ = v_reuseFailAlloc_5657_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_5656_;
            }
            31 => {
                if v_isShared_5671_ == 0 {
                    v___x_5673_ = v___x_5670_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_5674_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5674_, 0, v_pos_5667_);
                    lean_ctor_set(v_reuseFailAlloc_5674_, 1, v_err_5668_);
                    v___x_5673_ = v_reuseFailAlloc_5674_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_5673_;
            }
            33 => {
                v_fst_5687_ = lean_ctor_get(v_pos_5677_, 0);
                v_snd_5688_ = lean_ctor_get(v_pos_5677_, 1);
                v___x_5689_ = lean_string_utf8_byte_size(v_fst_5687_);
                v___x_5690_ = lean_nat_dec_eq(v_snd_5688_, v___x_5689_);
                if v___x_5690_ == 0 {
                    if v___x_5557_ == 0 {
                        lean_dec(v_res_5678_);
                        state = 34;
                        continue;
                    } else {
                        lean_inc(v_snd_5688_);
                        lean_inc(v_fst_5687_);
                        lean_del_object(v___x_5680_);
                        v_isSharedCheck_5833_ = (!lean_is_exclusive(v_pos_5677_)) as u8;
                        if v_isSharedCheck_5833_ == 0 {
                            v_unused_5834_ = lean_ctor_get(v_pos_5677_, 1);
                            lean_dec(v_unused_5834_);
                            v_unused_5835_ = lean_ctor_get(v_pos_5677_, 0);
                            lean_dec(v_unused_5835_);
                            v___x_5692_ = v_pos_5677_;
                            v_isShared_5693_ = v_isSharedCheck_5833_;
                            state = 36;
                            continue;
                        } else {
                            lean_dec(v_pos_5677_);
                            v___x_5692_ = lean_box(0);
                            v_isShared_5693_ = v_isSharedCheck_5833_;
                            state = 36;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_res_5678_);
                    state = 34;
                    continue;
                }
            }
            34 => {
                v___x_5683_ = lean_box(0);
                if v_isShared_5681_ == 0 {
                    lean_ctor_set_tag(v___x_5680_, 1);
                    lean_ctor_set(v___x_5680_, 1, v___x_5683_);
                    v___x_5685_ = v___x_5680_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_5686_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5686_, 0, v_pos_5677_);
                    lean_ctor_set(v_reuseFailAlloc_5686_, 1, v___x_5683_);
                    v___x_5685_ = v_reuseFailAlloc_5686_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_5685_;
            }
            36 => {
                v___x_5694_ = lean_string_utf8_next_fast(v_fst_5687_, v_snd_5688_);
                lean_dec(v_snd_5688_);
                if v_isShared_5693_ == 0 {
                    lean_ctor_set(v___x_5692_, 1, v___x_5694_);
                    v___x_5696_ = v___x_5692_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_5832_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5832_, 0, v_fst_5687_);
                    lean_ctor_set(v_reuseFailAlloc_5832_, 1, v___x_5694_);
                    v___x_5696_ = v_reuseFailAlloc_5832_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                v___x_5697_ =
                    l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(
                        v___x_5696_,
                    );
                if lean_obj_tag(v___x_5697_) == 0 {
                    v_pos_5698_ = lean_ctor_get(v___x_5697_, 0);
                    v_isSharedCheck_5821_ = (!lean_is_exclusive(v___x_5697_)) as u8;
                    if v_isSharedCheck_5821_ == 0 {
                        v_unused_5822_ = lean_ctor_get(v___x_5697_, 1);
                        lean_dec(v_unused_5822_);
                        v___x_5700_ = v___x_5697_;
                        v_isShared_5701_ = v_isSharedCheck_5821_;
                        state = 38;
                        continue;
                    } else {
                        lean_inc(v_pos_5698_);
                        lean_dec(v___x_5697_);
                        v___x_5700_ = lean_box(0);
                        v_isShared_5701_ = v_isSharedCheck_5821_;
                        state = 38;
                        continue;
                    }
                } else {
                    lean_dec(v_res_5678_);
                    v_pos_5823_ = lean_ctor_get(v___x_5697_, 0);
                    v_err_5824_ = lean_ctor_get(v___x_5697_, 1);
                    v_isSharedCheck_5831_ = (!lean_is_exclusive(v___x_5697_)) as u8;
                    if v_isSharedCheck_5831_ == 0 {
                        v___x_5826_ = v___x_5697_;
                        v_isShared_5827_ = v_isSharedCheck_5831_;
                        state = 61;
                        continue;
                    } else {
                        lean_inc(v_err_5824_);
                        lean_inc(v_pos_5823_);
                        lean_dec(v___x_5697_);
                        v___x_5826_ = lean_box(0);
                        v_isShared_5827_ = v_isSharedCheck_5831_;
                        state = 61;
                        continue;
                    }
                }
            }
            38 => {
                v_fst_5702_ = lean_ctor_get(v_pos_5698_, 0);
                v_snd_5703_ = lean_ctor_get(v_pos_5698_, 1);
                v___x_5704_ = lean_string_utf8_byte_size(v_fst_5702_);
                v___x_5705_ = lean_nat_dec_eq(v_snd_5703_, v___x_5704_);
                if v___x_5705_ == 0 {
                    lean_inc(v_snd_5703_);
                    lean_inc(v_fst_5702_);
                    lean_del_object(v___x_5700_);
                    v_isSharedCheck_5814_ = (!lean_is_exclusive(v_pos_5698_)) as u8;
                    if v_isSharedCheck_5814_ == 0 {
                        v_unused_5815_ = lean_ctor_get(v_pos_5698_, 1);
                        lean_dec(v_unused_5815_);
                        v_unused_5816_ = lean_ctor_get(v_pos_5698_, 0);
                        lean_dec(v_unused_5816_);
                        v___x_5707_ = v_pos_5698_;
                        v_isShared_5708_ = v_isSharedCheck_5814_;
                        state = 39;
                        continue;
                    } else {
                        lean_dec(v_pos_5698_);
                        v___x_5707_ = lean_box(0);
                        v_isShared_5708_ = v_isSharedCheck_5814_;
                        state = 39;
                        continue;
                    }
                } else {
                    lean_dec(v_res_5678_);
                    v___x_5817_ = lean_box(0);
                    if v_isShared_5701_ == 0 {
                        lean_ctor_set_tag(v___x_5700_, 1);
                        lean_ctor_set(v___x_5700_, 1, v___x_5817_);
                        v___x_5819_ = v___x_5700_;
                        state = 60;
                        continue;
                    } else {
                        v_reuseFailAlloc_5820_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5820_, 0, v_pos_5698_);
                        lean_ctor_set(v_reuseFailAlloc_5820_, 1, v___x_5817_);
                        v___x_5819_ = v_reuseFailAlloc_5820_;
                        state = 60;
                        continue;
                    }
                }
            }
            39 => {
                v___x_5709_ = lean_string_utf8_next_fast(v_fst_5702_, v_snd_5703_);
                lean_dec(v_snd_5703_);
                if v_isShared_5708_ == 0 {
                    lean_ctor_set(v___x_5707_, 1, v___x_5709_);
                    v___x_5711_ = v___x_5707_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_5813_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5813_, 0, v_fst_5702_);
                    lean_ctor_set(v_reuseFailAlloc_5813_, 1, v___x_5709_);
                    v___x_5711_ = v_reuseFailAlloc_5813_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                v___x_5712_ =
                    l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(
                        v___x_5711_,
                    );
                if lean_obj_tag(v___x_5712_) == 0 {
                    v_pos_5713_ = lean_ctor_get(v___x_5712_, 0);
                    v_isSharedCheck_5802_ = (!lean_is_exclusive(v___x_5712_)) as u8;
                    if v_isSharedCheck_5802_ == 0 {
                        v_unused_5803_ = lean_ctor_get(v___x_5712_, 1);
                        lean_dec(v_unused_5803_);
                        v___x_5715_ = v___x_5712_;
                        v_isShared_5716_ = v_isSharedCheck_5802_;
                        state = 41;
                        continue;
                    } else {
                        lean_inc(v_pos_5713_);
                        lean_dec(v___x_5712_);
                        v___x_5715_ = lean_box(0);
                        v_isShared_5716_ = v_isSharedCheck_5802_;
                        state = 41;
                        continue;
                    }
                } else {
                    lean_dec(v_res_5678_);
                    v_pos_5804_ = lean_ctor_get(v___x_5712_, 0);
                    v_err_5805_ = lean_ctor_get(v___x_5712_, 1);
                    v_isSharedCheck_5812_ = (!lean_is_exclusive(v___x_5712_)) as u8;
                    if v_isSharedCheck_5812_ == 0 {
                        v___x_5807_ = v___x_5712_;
                        v_isShared_5808_ = v_isSharedCheck_5812_;
                        state = 58;
                        continue;
                    } else {
                        lean_inc(v_err_5805_);
                        lean_inc(v_pos_5804_);
                        lean_dec(v___x_5712_);
                        v___x_5807_ = lean_box(0);
                        v_isShared_5808_ = v_isSharedCheck_5812_;
                        state = 58;
                        continue;
                    }
                }
            }
            41 => {
                v_fst_5717_ = lean_ctor_get(v_pos_5713_, 0);
                v_snd_5718_ = lean_ctor_get(v_pos_5713_, 1);
                v___x_5719_ = lean_string_utf8_byte_size(v_fst_5717_);
                v___x_5720_ = lean_nat_dec_eq(v_snd_5718_, v___x_5719_);
                if v___x_5720_ == 0 {
                    lean_inc(v_snd_5718_);
                    lean_inc(v_fst_5717_);
                    v_isSharedCheck_5795_ = (!lean_is_exclusive(v_pos_5713_)) as u8;
                    if v_isSharedCheck_5795_ == 0 {
                        v_unused_5796_ = lean_ctor_get(v_pos_5713_, 1);
                        lean_dec(v_unused_5796_);
                        v_unused_5797_ = lean_ctor_get(v_pos_5713_, 0);
                        lean_dec(v_unused_5797_);
                        v___x_5722_ = v_pos_5713_;
                        v_isShared_5723_ = v_isSharedCheck_5795_;
                        state = 42;
                        continue;
                    } else {
                        lean_dec(v_pos_5713_);
                        v___x_5722_ = lean_box(0);
                        v_isShared_5723_ = v_isSharedCheck_5795_;
                        state = 42;
                        continue;
                    }
                } else {
                    lean_dec(v_res_5678_);
                    v___x_5798_ = lean_box(0);
                    if v_isShared_5716_ == 0 {
                        lean_ctor_set_tag(v___x_5715_, 1);
                        lean_ctor_set(v___x_5715_, 1, v___x_5798_);
                        v___x_5800_ = v___x_5715_;
                        state = 57;
                        continue;
                    } else {
                        v_reuseFailAlloc_5801_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5801_, 0, v_pos_5713_);
                        lean_ctor_set(v_reuseFailAlloc_5801_, 1, v___x_5798_);
                        v___x_5800_ = v_reuseFailAlloc_5801_;
                        state = 57;
                        continue;
                    }
                }
            }
            42 => {
                v___x_5724_ = lean_string_utf8_next_fast(v_fst_5717_, v_snd_5718_);
                lean_dec(v_snd_5718_);
                if v_isShared_5723_ == 0 {
                    lean_ctor_set(v___x_5722_, 1, v___x_5724_);
                    v___x_5726_ = v___x_5722_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_5794_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5794_, 0, v_fst_5717_);
                    lean_ctor_set(v_reuseFailAlloc_5794_, 1, v___x_5724_);
                    v___x_5726_ = v_reuseFailAlloc_5794_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                v___x_5727_ =
                    l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(
                        v___x_5726_,
                    );
                if lean_obj_tag(v___x_5727_) == 0 {
                    v_pos_5728_ = lean_ctor_get(v___x_5727_, 0);
                    v_res_5729_ = lean_ctor_get(v___x_5727_, 1);
                    v_isSharedCheck_5784_ = (!lean_is_exclusive(v___x_5727_)) as u8;
                    if v_isSharedCheck_5784_ == 0 {
                        v___x_5731_ = v___x_5727_;
                        v_isShared_5732_ = v_isSharedCheck_5784_;
                        state = 44;
                        continue;
                    } else {
                        lean_inc(v_res_5729_);
                        lean_inc(v_pos_5728_);
                        lean_dec(v___x_5727_);
                        v___x_5731_ = lean_box(0);
                        v_isShared_5732_ = v_isSharedCheck_5784_;
                        state = 44;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5715_);
                    lean_dec(v_res_5678_);
                    v_pos_5785_ = lean_ctor_get(v___x_5727_, 0);
                    v_err_5786_ = lean_ctor_get(v___x_5727_, 1);
                    v_isSharedCheck_5793_ = (!lean_is_exclusive(v___x_5727_)) as u8;
                    if v_isSharedCheck_5793_ == 0 {
                        v___x_5788_ = v___x_5727_;
                        v_isShared_5789_ = v_isSharedCheck_5793_;
                        state = 55;
                        continue;
                    } else {
                        lean_inc(v_err_5786_);
                        lean_inc(v_pos_5785_);
                        lean_dec(v___x_5727_);
                        v___x_5788_ = lean_box(0);
                        v_isShared_5789_ = v_isSharedCheck_5793_;
                        state = 55;
                        continue;
                    }
                }
            }
            44 => {
                v___x_5738_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
                v___x_5739_ = lean_string_dec_eq(v_res_5729_, v___x_5738_);
                if v___x_5739_ == 0 {
                    lean_del_object(v___x_5731_);
                    v___x_5740_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7;
                    v___x_5741_ = lean_string_dec_eq(v_res_5729_, v___x_5740_);
                    lean_dec(v_res_5729_);
                    if v___x_5741_ == 0 {
                        lean_dec(v_res_5678_);
                        v___x_5742_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__5;
                        if v_isShared_5716_ == 0 {
                            lean_ctor_set_tag(v___x_5715_, 1);
                            lean_ctor_set(v___x_5715_, 1, v___x_5742_);
                            lean_ctor_set(v___x_5715_, 0, v_pos_5728_);
                            v___x_5744_ = v___x_5715_;
                            state = 47;
                            continue;
                        } else {
                            v_reuseFailAlloc_5745_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_5745_, 0, v_pos_5728_);
                            lean_ctor_set(v_reuseFailAlloc_5745_, 1, v___x_5742_);
                            v___x_5744_ = v_reuseFailAlloc_5745_;
                            state = 47;
                            continue;
                        }
                    } else {
                        v___x_5746_ = lean_alloc_ctor(2, 1, (0) as u32);
                        lean_ctor_set(v___x_5746_, 0, v_res_5678_);
                        if v_isShared_5716_ == 0 {
                            lean_ctor_set(v___x_5715_, 1, v___x_5746_);
                            lean_ctor_set(v___x_5715_, 0, v_pos_5728_);
                            v___x_5748_ = v___x_5715_;
                            state = 48;
                            continue;
                        } else {
                            v_reuseFailAlloc_5749_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_5749_, 0, v_pos_5728_);
                            lean_ctor_set(v_reuseFailAlloc_5749_, 1, v___x_5746_);
                            v___x_5748_ = v_reuseFailAlloc_5749_;
                            state = 48;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_res_5729_);
                    lean_del_object(v___x_5715_);
                    v_fst_5750_ = lean_ctor_get(v_pos_5728_, 0);
                    v_snd_5751_ = lean_ctor_get(v_pos_5728_, 1);
                    v___x_5752_ = lean_string_utf8_byte_size(v_fst_5750_);
                    v___x_5753_ = lean_nat_dec_eq(v_snd_5751_, v___x_5752_);
                    if v___x_5753_ == 0 {
                        if v___x_5739_ == 0 {
                            lean_dec(v_res_5678_);
                            state = 45;
                            continue;
                        } else {
                            lean_inc(v_snd_5751_);
                            lean_inc(v_fst_5750_);
                            lean_del_object(v___x_5731_);
                            v_isSharedCheck_5781_ = (!lean_is_exclusive(v_pos_5728_)) as u8;
                            if v_isSharedCheck_5781_ == 0 {
                                v_unused_5782_ = lean_ctor_get(v_pos_5728_, 1);
                                lean_dec(v_unused_5782_);
                                v_unused_5783_ = lean_ctor_get(v_pos_5728_, 0);
                                lean_dec(v_unused_5783_);
                                v___x_5755_ = v_pos_5728_;
                                v_isShared_5756_ = v_isSharedCheck_5781_;
                                state = 49;
                                continue;
                            } else {
                                lean_dec(v_pos_5728_);
                                v___x_5755_ = lean_box(0);
                                v_isShared_5756_ = v_isSharedCheck_5781_;
                                state = 49;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_res_5678_);
                        state = 45;
                        continue;
                    }
                }
            }
            45 => {
                v___x_5734_ = lean_box(0);
                if v_isShared_5732_ == 0 {
                    lean_ctor_set_tag(v___x_5731_, 1);
                    lean_ctor_set(v___x_5731_, 1, v___x_5734_);
                    v___x_5736_ = v___x_5731_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_5737_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5737_, 0, v_pos_5728_);
                    lean_ctor_set(v_reuseFailAlloc_5737_, 1, v___x_5734_);
                    v___x_5736_ = v_reuseFailAlloc_5737_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                return v___x_5736_;
            }
            47 => {
                return v___x_5744_;
            }
            48 => {
                return v___x_5748_;
            }
            49 => {
                v___x_5757_ = lean_string_utf8_next_fast(v_fst_5750_, v_snd_5751_);
                lean_dec(v_snd_5751_);
                if v_isShared_5756_ == 0 {
                    lean_ctor_set(v___x_5755_, 1, v___x_5757_);
                    v___x_5759_ = v___x_5755_;
                    state = 50;
                    continue;
                } else {
                    v_reuseFailAlloc_5780_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5780_, 0, v_fst_5750_);
                    lean_ctor_set(v_reuseFailAlloc_5780_, 1, v___x_5757_);
                    v___x_5759_ = v_reuseFailAlloc_5780_;
                    state = 50;
                    continue;
                }
            }
            50 => {
                v___x_5760_ =
                    l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(
                        v___x_5759_,
                    );
                if lean_obj_tag(v___x_5760_) == 0 {
                    v_pos_5761_ = lean_ctor_get(v___x_5760_, 0);
                    v_res_5762_ = lean_ctor_get(v___x_5760_, 1);
                    v_isSharedCheck_5770_ = (!lean_is_exclusive(v___x_5760_)) as u8;
                    if v_isSharedCheck_5770_ == 0 {
                        v___x_5764_ = v___x_5760_;
                        v_isShared_5765_ = v_isSharedCheck_5770_;
                        state = 51;
                        continue;
                    } else {
                        lean_inc(v_res_5762_);
                        lean_inc(v_pos_5761_);
                        lean_dec(v___x_5760_);
                        v___x_5764_ = lean_box(0);
                        v_isShared_5765_ = v_isSharedCheck_5770_;
                        state = 51;
                        continue;
                    }
                } else {
                    lean_dec(v_res_5678_);
                    v_pos_5771_ = lean_ctor_get(v___x_5760_, 0);
                    v_err_5772_ = lean_ctor_get(v___x_5760_, 1);
                    v_isSharedCheck_5779_ = (!lean_is_exclusive(v___x_5760_)) as u8;
                    if v_isSharedCheck_5779_ == 0 {
                        v___x_5774_ = v___x_5760_;
                        v_isShared_5775_ = v_isSharedCheck_5779_;
                        state = 53;
                        continue;
                    } else {
                        lean_inc(v_err_5772_);
                        lean_inc(v_pos_5771_);
                        lean_dec(v___x_5760_);
                        v___x_5774_ = lean_box(0);
                        v_isShared_5775_ = v_isSharedCheck_5779_;
                        state = 53;
                        continue;
                    }
                }
            }
            51 => {
                v___x_5766_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5766_, 0, v_res_5678_);
                lean_ctor_set(v___x_5766_, 1, v_res_5762_);
                if v_isShared_5765_ == 0 {
                    lean_ctor_set(v___x_5764_, 1, v___x_5766_);
                    v___x_5768_ = v___x_5764_;
                    state = 52;
                    continue;
                } else {
                    v_reuseFailAlloc_5769_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5769_, 0, v_pos_5761_);
                    lean_ctor_set(v_reuseFailAlloc_5769_, 1, v___x_5766_);
                    v___x_5768_ = v_reuseFailAlloc_5769_;
                    state = 52;
                    continue;
                }
            }
            52 => {
                return v___x_5768_;
            }
            53 => {
                if v_isShared_5775_ == 0 {
                    v___x_5777_ = v___x_5774_;
                    state = 54;
                    continue;
                } else {
                    v_reuseFailAlloc_5778_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5778_, 0, v_pos_5771_);
                    lean_ctor_set(v_reuseFailAlloc_5778_, 1, v_err_5772_);
                    v___x_5777_ = v_reuseFailAlloc_5778_;
                    state = 54;
                    continue;
                }
            }
            54 => {
                return v___x_5777_;
            }
            55 => {
                if v_isShared_5789_ == 0 {
                    v___x_5791_ = v___x_5788_;
                    state = 56;
                    continue;
                } else {
                    v_reuseFailAlloc_5792_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5792_, 0, v_pos_5785_);
                    lean_ctor_set(v_reuseFailAlloc_5792_, 1, v_err_5786_);
                    v___x_5791_ = v_reuseFailAlloc_5792_;
                    state = 56;
                    continue;
                }
            }
            56 => {
                return v___x_5791_;
            }
            57 => {
                return v___x_5800_;
            }
            58 => {
                if v_isShared_5808_ == 0 {
                    v___x_5810_ = v___x_5807_;
                    state = 59;
                    continue;
                } else {
                    v_reuseFailAlloc_5811_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5811_, 0, v_pos_5804_);
                    lean_ctor_set(v_reuseFailAlloc_5811_, 1, v_err_5805_);
                    v___x_5810_ = v_reuseFailAlloc_5811_;
                    state = 59;
                    continue;
                }
            }
            59 => {
                return v___x_5810_;
            }
            60 => {
                return v___x_5819_;
            }
            61 => {
                if v_isShared_5827_ == 0 {
                    v___x_5829_ = v___x_5826_;
                    state = 62;
                    continue;
                } else {
                    v_reuseFailAlloc_5830_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5830_, 0, v_pos_5823_);
                    lean_ctor_set(v_reuseFailAlloc_5830_, 1, v_err_5824_);
                    v___x_5829_ = v_reuseFailAlloc_5830_;
                    state = 62;
                    continue;
                }
            }
            62 => {
                return v___x_5829_;
            }
            63 => {
                if v_isShared_5841_ == 0 {
                    v___x_5843_ = v___x_5840_;
                    state = 64;
                    continue;
                } else {
                    v_reuseFailAlloc_5844_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5844_, 0, v_pos_5837_);
                    lean_ctor_set(v_reuseFailAlloc_5844_, 1, v_err_5838_);
                    v___x_5843_ = v_reuseFailAlloc_5844_;
                    state = 64;
                    continue;
                }
            }
            64 => {
                return v___x_5843_;
            }
            65 => {
                return v___x_5852_;
            }
            66 => {
                if v_isShared_5859_ == 0 {
                    v___x_5861_ = v___x_5858_;
                    state = 67;
                    continue;
                } else {
                    v_reuseFailAlloc_5862_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5862_, 0, v_pos_5855_);
                    lean_ctor_set(v_reuseFailAlloc_5862_, 1, v_err_5856_);
                    v___x_5861_ = v_reuseFailAlloc_5862_;
                    state = 67;
                    continue;
                }
            }
            67 => {
                return v___x_5861_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_JsonRpc_parseMessageMetaData(
    mut v_input_5870_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5872_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_input_5870_);
    v___x_5871_ = lean_alloc_closure(
        l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___x_5871_, 0, v_input_5870_);
    v___x_5872_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___x_5871_, v_input_5870_);
    return v___x_5872_;
}
pub unsafe fn l_Lean_JsonRpc_MessageDirection_ctorIdx(mut v_x_5873_: u8) -> *mut LeanObject {
    if v_x_5873_ == 0 {
        let mut v___x_5874_: *mut LeanObject = core::ptr::null_mut();
        v___x_5874_ = lean_unsigned_to_nat(0);
        return v___x_5874_;
    } else {
        let mut v___x_5875_: *mut LeanObject = core::ptr::null_mut();
        v___x_5875_ = lean_unsigned_to_nat(1);
        return v___x_5875_;
    }
}
pub unsafe fn l_Lean_JsonRpc_MessageDirection_ctorIdx___boxed(
    mut v_x_5876_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_5877_: u8 = 0;
    let mut v_res_5878_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_5877_ = (lean_unbox(v_x_5876_) as u8);
    v_res_5878_ = l_Lean_JsonRpc_MessageDirection_ctorIdx(v_x_boxed_5877_);
    return v_res_5878_;
}
pub unsafe fn l_Lean_JsonRpc_MessageDirection_toCtorIdx(mut v_x_5879_: u8) -> *mut LeanObject {
    let mut v___x_5880_: *mut LeanObject = core::ptr::null_mut();
    v___x_5880_ = l_Lean_JsonRpc_MessageDirection_ctorIdx(v_x_5879_);
    return v___x_5880_;
}
pub unsafe fn l_Lean_JsonRpc_MessageDirection_toCtorIdx___boxed(
    mut v_x_5881_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4__boxed_5882_: u8 = 0;
    let mut v_res_5883_: *mut LeanObject = core::ptr::null_mut();
    v_x_4__boxed_5882_ = (lean_unbox(v_x_5881_) as u8);
    v_res_5883_ = l_Lean_JsonRpc_MessageDirection_toCtorIdx(v_x_4__boxed_5882_);
    return v_res_5883_;
}
pub unsafe fn l_Lean_JsonRpc_MessageDirection_ctorElim___redArg(
    mut v_k_5884_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_5884_);
    return v_k_5884_;
}
pub unsafe fn l_Lean_JsonRpc_MessageDirection_ctorElim___redArg___boxed(
    mut v_k_5885_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5886_: *mut LeanObject = core::ptr::null_mut();
    v_res_5886_ = l_Lean_JsonRpc_MessageDirection_ctorElim___redArg(v_k_5885_);
    lean_dec(v_k_5885_);
    return v_res_5886_;
}
pub unsafe fn l_Lean_JsonRpc_MessageDirection_ctorElim(
    mut v_motive_5887_: *mut LeanObject,
    mut v_ctorIdx_5888_: *mut LeanObject,
    mut v_t_5889_: u8,
    mut v_h_5890_: *mut LeanObject,
    mut v_k_5891_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_5891_);
    return v_k_5891_;
}
pub unsafe fn l_Lean_JsonRpc_MessageDirection_ctorElim___boxed(
    mut v_motive_5892_: *mut LeanObject,
    mut v_ctorIdx_5893_: *mut LeanObject,
    mut v_t_5894_: *mut LeanObject,
    mut v_h_5895_: *mut LeanObject,
    mut v_k_5896_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_5897_: u8 = 0;
    let mut v_res_5898_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_5897_ = (lean_unbox(v_t_5894_) as u8);
    v_res_5898_ = l_Lean_JsonRpc_MessageDirection_ctorElim(
        v_motive_5892_,
        v_ctorIdx_5893_,
        v_t_boxed_5897_,
        v_h_5895_,
        v_k_5896_,
    );
    lean_dec(v_k_5896_);
    lean_dec(v_ctorIdx_5893_);
    return v_res_5898_;
}
pub unsafe fn l_Lean_JsonRpc_MessageDirection_clientToServer_elim___redArg(
    mut v_clientToServer_5899_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_clientToServer_5899_);
    return v_clientToServer_5899_;
}
pub unsafe fn l_Lean_JsonRpc_MessageDirection_clientToServer_elim___redArg___boxed(
    mut v_clientToServer_5900_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5901_: *mut LeanObject = core::ptr::null_mut();
    v_res_5901_ =
        l_Lean_JsonRpc_MessageDirection_clientToServer_elim___redArg(v_clientToServer_5900_);
    lean_dec(v_clientToServer_5900_);
    return v_res_5901_;
}
pub unsafe fn l_Lean_JsonRpc_MessageDirection_clientToServer_elim(
    mut v_motive_5902_: *mut LeanObject,
    mut v_t_5903_: u8,
    mut v_h_5904_: *mut LeanObject,
    mut v_clientToServer_5905_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_clientToServer_5905_);
    return v_clientToServer_5905_;
}
pub unsafe fn l_Lean_JsonRpc_MessageDirection_clientToServer_elim___boxed(
    mut v_motive_5906_: *mut LeanObject,
    mut v_t_5907_: *mut LeanObject,
    mut v_h_5908_: *mut LeanObject,
    mut v_clientToServer_5909_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_5910_: u8 = 0;
    let mut v_res_5911_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_5910_ = (lean_unbox(v_t_5907_) as u8);
    v_res_5911_ = l_Lean_JsonRpc_MessageDirection_clientToServer_elim(
        v_motive_5906_,
        v_t_boxed_5910_,
        v_h_5908_,
        v_clientToServer_5909_,
    );
    lean_dec(v_clientToServer_5909_);
    return v_res_5911_;
}
pub unsafe fn l_Lean_JsonRpc_MessageDirection_serverToClient_elim___redArg(
    mut v_serverToClient_5912_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_serverToClient_5912_);
    return v_serverToClient_5912_;
}
pub unsafe fn l_Lean_JsonRpc_MessageDirection_serverToClient_elim___redArg___boxed(
    mut v_serverToClient_5913_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5914_: *mut LeanObject = core::ptr::null_mut();
    v_res_5914_ =
        l_Lean_JsonRpc_MessageDirection_serverToClient_elim___redArg(v_serverToClient_5913_);
    lean_dec(v_serverToClient_5913_);
    return v_res_5914_;
}
pub unsafe fn l_Lean_JsonRpc_MessageDirection_serverToClient_elim(
    mut v_motive_5915_: *mut LeanObject,
    mut v_t_5916_: u8,
    mut v_h_5917_: *mut LeanObject,
    mut v_serverToClient_5918_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_serverToClient_5918_);
    return v_serverToClient_5918_;
}
pub unsafe fn l_Lean_JsonRpc_MessageDirection_serverToClient_elim___boxed(
    mut v_motive_5919_: *mut LeanObject,
    mut v_t_5920_: *mut LeanObject,
    mut v_h_5921_: *mut LeanObject,
    mut v_serverToClient_5922_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_5923_: u8 = 0;
    let mut v_res_5924_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_5923_ = (lean_unbox(v_t_5920_) as u8);
    v_res_5924_ = l_Lean_JsonRpc_MessageDirection_serverToClient_elim(
        v_motive_5919_,
        v_t_boxed_5923_,
        v_h_5921_,
        v_serverToClient_5922_,
    );
    lean_dec(v_serverToClient_5922_);
    return v_res_5924_;
}
pub unsafe fn _init_l_Lean_JsonRpc_instInhabitedMessageDirection_default() -> u8 {
    let mut v___x_5925_: u8 = 0;
    v___x_5925_ = 0;
    return v___x_5925_;
}
pub unsafe fn _init_l_Lean_JsonRpc_instInhabitedMessageDirection() -> u8 {
    let mut v___x_5926_: u8 = 0;
    v___x_5926_ = 0;
    return v___x_5926_;
}
pub unsafe fn l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson(
    mut v_json_5941_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5942_: *mut LeanObject = core::ptr::null_mut();
    v___x_5942_ = l_Lean_Json_getTag_x3f(v_json_5941_);
    if lean_obj_tag(v___x_5942_) == 0 {
        let mut v___x_5943_: *mut LeanObject = core::ptr::null_mut();
        v___x_5943_ = l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__1;
        return v___x_5943_;
    } else {
        let mut v_val_5944_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5945_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5946_: u8 = 0;
        v_val_5944_ = lean_ctor_get(v___x_5942_, 0);
        lean_inc(v_val_5944_);
        lean_dec_ref_known(v___x_5942_, 1);
        v___x_5945_ = l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__2;
        v___x_5946_ = lean_string_dec_eq(v_val_5944_, v___x_5945_);
        if v___x_5946_ == 0 {
            let mut v___x_5947_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5948_: u8 = 0;
            v___x_5947_ = l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__3;
            v___x_5948_ = lean_string_dec_eq(v_val_5944_, v___x_5947_);
            lean_dec(v_val_5944_);
            if v___x_5948_ == 0 {
                let mut v___x_5949_: *mut LeanObject = core::ptr::null_mut();
                v___x_5949_ = l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__5;
                return v___x_5949_;
            } else {
                let mut v___x_5950_: *mut LeanObject = core::ptr::null_mut();
                v___x_5950_ = l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__6;
                return v___x_5950_;
            }
        } else {
            let mut v___x_5951_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_val_5944_);
            v___x_5951_ = l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__7;
            return v___x_5951_;
        }
    }
}
pub unsafe fn l_Lean_JsonRpc_instToJsonMessageDirection_toJson(
    mut v_x_5958_: u8,
) -> *mut LeanObject {
    if v_x_5958_ == 0 {
        let mut v___x_5959_: *mut LeanObject = core::ptr::null_mut();
        v___x_5959_ = l_Lean_JsonRpc_instToJsonMessageDirection_toJson___closed__0;
        return v___x_5959_;
    } else {
        let mut v___x_5960_: *mut LeanObject = core::ptr::null_mut();
        v___x_5960_ = l_Lean_JsonRpc_instToJsonMessageDirection_toJson___closed__1;
        return v___x_5960_;
    }
}
pub unsafe fn l_Lean_JsonRpc_instToJsonMessageDirection_toJson___boxed(
    mut v_x_5961_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_44__boxed_5962_: u8 = 0;
    let mut v_res_5963_: *mut LeanObject = core::ptr::null_mut();
    v_x_44__boxed_5962_ = (lean_unbox(v_x_5961_) as u8);
    v_res_5963_ = l_Lean_JsonRpc_instToJsonMessageDirection_toJson(v_x_44__boxed_5962_);
    return v_res_5963_;
}
pub unsafe fn l_Lean_JsonRpc_MessageKind_ctorIdx(mut v_x_5966_: u8) -> *mut LeanObject {
    match v_x_5966_ {
        0 => {
            let mut v___x_5967_: *mut LeanObject = core::ptr::null_mut();
            v___x_5967_ = lean_unsigned_to_nat(0);
            return v___x_5967_;
        }
        1 => {
            let mut v___x_5968_: *mut LeanObject = core::ptr::null_mut();
            v___x_5968_ = lean_unsigned_to_nat(1);
            return v___x_5968_;
        }
        2 => {
            let mut v___x_5969_: *mut LeanObject = core::ptr::null_mut();
            v___x_5969_ = lean_unsigned_to_nat(2);
            return v___x_5969_;
        }
        _ => {
            let mut v___x_5970_: *mut LeanObject = core::ptr::null_mut();
            v___x_5970_ = lean_unsigned_to_nat(3);
            return v___x_5970_;
        }
    }
}
pub unsafe fn l_Lean_JsonRpc_MessageKind_ctorIdx___boxed(
    mut v_x_5971_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_5972_: u8 = 0;
    let mut v_res_5973_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_5972_ = (lean_unbox(v_x_5971_) as u8);
    v_res_5973_ = l_Lean_JsonRpc_MessageKind_ctorIdx(v_x_boxed_5972_);
    return v_res_5973_;
}
pub unsafe fn l_Lean_JsonRpc_MessageKind_toCtorIdx(mut v_x_5974_: u8) -> *mut LeanObject {
    let mut v___x_5975_: *mut LeanObject = core::ptr::null_mut();
    v___x_5975_ = l_Lean_JsonRpc_MessageKind_ctorIdx(v_x_5974_);
    return v___x_5975_;
}
pub unsafe fn l_Lean_JsonRpc_MessageKind_toCtorIdx___boxed(
    mut v_x_5976_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4__boxed_5977_: u8 = 0;
    let mut v_res_5978_: *mut LeanObject = core::ptr::null_mut();
    v_x_4__boxed_5977_ = (lean_unbox(v_x_5976_) as u8);
    v_res_5978_ = l_Lean_JsonRpc_MessageKind_toCtorIdx(v_x_4__boxed_5977_);
    return v_res_5978_;
}
pub unsafe fn l_Lean_JsonRpc_MessageKind_ctorElim___redArg(
    mut v_k_5979_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_5979_);
    return v_k_5979_;
}
pub unsafe fn l_Lean_JsonRpc_MessageKind_ctorElim___redArg___boxed(
    mut v_k_5980_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5981_: *mut LeanObject = core::ptr::null_mut();
    v_res_5981_ = l_Lean_JsonRpc_MessageKind_ctorElim___redArg(v_k_5980_);
    lean_dec(v_k_5980_);
    return v_res_5981_;
}
pub unsafe fn l_Lean_JsonRpc_MessageKind_ctorElim(
    mut v_motive_5982_: *mut LeanObject,
    mut v_ctorIdx_5983_: *mut LeanObject,
    mut v_t_5984_: u8,
    mut v_h_5985_: *mut LeanObject,
    mut v_k_5986_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_5986_);
    return v_k_5986_;
}
pub unsafe fn l_Lean_JsonRpc_MessageKind_ctorElim___boxed(
    mut v_motive_5987_: *mut LeanObject,
    mut v_ctorIdx_5988_: *mut LeanObject,
    mut v_t_5989_: *mut LeanObject,
    mut v_h_5990_: *mut LeanObject,
    mut v_k_5991_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_5992_: u8 = 0;
    let mut v_res_5993_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_5992_ = (lean_unbox(v_t_5989_) as u8);
    v_res_5993_ = l_Lean_JsonRpc_MessageKind_ctorElim(
        v_motive_5987_,
        v_ctorIdx_5988_,
        v_t_boxed_5992_,
        v_h_5990_,
        v_k_5991_,
    );
    lean_dec(v_k_5991_);
    lean_dec(v_ctorIdx_5988_);
    return v_res_5993_;
}
pub unsafe fn l_Lean_JsonRpc_MessageKind_request_elim___redArg(
    mut v_request_5994_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_request_5994_);
    return v_request_5994_;
}
pub unsafe fn l_Lean_JsonRpc_MessageKind_request_elim___redArg___boxed(
    mut v_request_5995_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5996_: *mut LeanObject = core::ptr::null_mut();
    v_res_5996_ = l_Lean_JsonRpc_MessageKind_request_elim___redArg(v_request_5995_);
    lean_dec(v_request_5995_);
    return v_res_5996_;
}
pub unsafe fn l_Lean_JsonRpc_MessageKind_request_elim(
    mut v_motive_5997_: *mut LeanObject,
    mut v_t_5998_: u8,
    mut v_h_5999_: *mut LeanObject,
    mut v_request_6000_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_request_6000_);
    return v_request_6000_;
}
pub unsafe fn l_Lean_JsonRpc_MessageKind_request_elim___boxed(
    mut v_motive_6001_: *mut LeanObject,
    mut v_t_6002_: *mut LeanObject,
    mut v_h_6003_: *mut LeanObject,
    mut v_request_6004_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_6005_: u8 = 0;
    let mut v_res_6006_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_6005_ = (lean_unbox(v_t_6002_) as u8);
    v_res_6006_ = l_Lean_JsonRpc_MessageKind_request_elim(
        v_motive_6001_,
        v_t_boxed_6005_,
        v_h_6003_,
        v_request_6004_,
    );
    lean_dec(v_request_6004_);
    return v_res_6006_;
}
pub unsafe fn l_Lean_JsonRpc_MessageKind_notification_elim___redArg(
    mut v_notification_6007_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_notification_6007_);
    return v_notification_6007_;
}
pub unsafe fn l_Lean_JsonRpc_MessageKind_notification_elim___redArg___boxed(
    mut v_notification_6008_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6009_: *mut LeanObject = core::ptr::null_mut();
    v_res_6009_ = l_Lean_JsonRpc_MessageKind_notification_elim___redArg(v_notification_6008_);
    lean_dec(v_notification_6008_);
    return v_res_6009_;
}
pub unsafe fn l_Lean_JsonRpc_MessageKind_notification_elim(
    mut v_motive_6010_: *mut LeanObject,
    mut v_t_6011_: u8,
    mut v_h_6012_: *mut LeanObject,
    mut v_notification_6013_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_notification_6013_);
    return v_notification_6013_;
}
pub unsafe fn l_Lean_JsonRpc_MessageKind_notification_elim___boxed(
    mut v_motive_6014_: *mut LeanObject,
    mut v_t_6015_: *mut LeanObject,
    mut v_h_6016_: *mut LeanObject,
    mut v_notification_6017_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_6018_: u8 = 0;
    let mut v_res_6019_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_6018_ = (lean_unbox(v_t_6015_) as u8);
    v_res_6019_ = l_Lean_JsonRpc_MessageKind_notification_elim(
        v_motive_6014_,
        v_t_boxed_6018_,
        v_h_6016_,
        v_notification_6017_,
    );
    lean_dec(v_notification_6017_);
    return v_res_6019_;
}
pub unsafe fn l_Lean_JsonRpc_MessageKind_response_elim___redArg(
    mut v_response_6020_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_response_6020_);
    return v_response_6020_;
}
pub unsafe fn l_Lean_JsonRpc_MessageKind_response_elim___redArg___boxed(
    mut v_response_6021_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6022_: *mut LeanObject = core::ptr::null_mut();
    v_res_6022_ = l_Lean_JsonRpc_MessageKind_response_elim___redArg(v_response_6021_);
    lean_dec(v_response_6021_);
    return v_res_6022_;
}
pub unsafe fn l_Lean_JsonRpc_MessageKind_response_elim(
    mut v_motive_6023_: *mut LeanObject,
    mut v_t_6024_: u8,
    mut v_h_6025_: *mut LeanObject,
    mut v_response_6026_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_response_6026_);
    return v_response_6026_;
}
pub unsafe fn l_Lean_JsonRpc_MessageKind_response_elim___boxed(
    mut v_motive_6027_: *mut LeanObject,
    mut v_t_6028_: *mut LeanObject,
    mut v_h_6029_: *mut LeanObject,
    mut v_response_6030_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_6031_: u8 = 0;
    let mut v_res_6032_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_6031_ = (lean_unbox(v_t_6028_) as u8);
    v_res_6032_ = l_Lean_JsonRpc_MessageKind_response_elim(
        v_motive_6027_,
        v_t_boxed_6031_,
        v_h_6029_,
        v_response_6030_,
    );
    lean_dec(v_response_6030_);
    return v_res_6032_;
}
pub unsafe fn l_Lean_JsonRpc_MessageKind_responseError_elim___redArg(
    mut v_responseError_6033_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_responseError_6033_);
    return v_responseError_6033_;
}
pub unsafe fn l_Lean_JsonRpc_MessageKind_responseError_elim___redArg___boxed(
    mut v_responseError_6034_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6035_: *mut LeanObject = core::ptr::null_mut();
    v_res_6035_ = l_Lean_JsonRpc_MessageKind_responseError_elim___redArg(v_responseError_6034_);
    lean_dec(v_responseError_6034_);
    return v_res_6035_;
}
pub unsafe fn l_Lean_JsonRpc_MessageKind_responseError_elim(
    mut v_motive_6036_: *mut LeanObject,
    mut v_t_6037_: u8,
    mut v_h_6038_: *mut LeanObject,
    mut v_responseError_6039_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_responseError_6039_);
    return v_responseError_6039_;
}
pub unsafe fn l_Lean_JsonRpc_MessageKind_responseError_elim___boxed(
    mut v_motive_6040_: *mut LeanObject,
    mut v_t_6041_: *mut LeanObject,
    mut v_h_6042_: *mut LeanObject,
    mut v_responseError_6043_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_6044_: u8 = 0;
    let mut v_res_6045_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_6044_ = (lean_unbox(v_t_6041_) as u8);
    v_res_6045_ = l_Lean_JsonRpc_MessageKind_responseError_elim(
        v_motive_6040_,
        v_t_boxed_6044_,
        v_h_6042_,
        v_responseError_6043_,
    );
    lean_dec(v_responseError_6043_);
    return v_res_6045_;
}
pub unsafe fn l_Lean_JsonRpc_instFromJsonMessageKind_fromJson(
    mut v_json_6066_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6067_: *mut LeanObject = core::ptr::null_mut();
    v___x_6067_ = l_Lean_Json_getTag_x3f(v_json_6066_);
    if lean_obj_tag(v___x_6067_) == 0 {
        let mut v___x_6068_: *mut LeanObject = core::ptr::null_mut();
        v___x_6068_ = l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__0;
        return v___x_6068_;
    } else {
        let mut v_val_6069_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6070_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6071_: u8 = 0;
        v_val_6069_ = lean_ctor_get(v___x_6067_, 0);
        lean_inc(v_val_6069_);
        lean_dec_ref_known(v___x_6067_, 1);
        v___x_6070_ = l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__1;
        v___x_6071_ = lean_string_dec_eq(v_val_6069_, v___x_6070_);
        if v___x_6071_ == 0 {
            let mut v___x_6072_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6073_: u8 = 0;
            v___x_6072_ = l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__2;
            v___x_6073_ = lean_string_dec_eq(v_val_6069_, v___x_6072_);
            if v___x_6073_ == 0 {
                let mut v___x_6074_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_6075_: u8 = 0;
                v___x_6074_ = l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__3;
                v___x_6075_ = lean_string_dec_eq(v_val_6069_, v___x_6074_);
                if v___x_6075_ == 0 {
                    let mut v___x_6076_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_6077_: u8 = 0;
                    v___x_6076_ = l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__4;
                    v___x_6077_ = lean_string_dec_eq(v_val_6069_, v___x_6076_);
                    lean_dec(v_val_6069_);
                    if v___x_6077_ == 0 {
                        let mut v___x_6078_: *mut LeanObject = core::ptr::null_mut();
                        v___x_6078_ = l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__5;
                        return v___x_6078_;
                    } else {
                        let mut v___x_6079_: *mut LeanObject = core::ptr::null_mut();
                        v___x_6079_ = l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__6;
                        return v___x_6079_;
                    }
                } else {
                    let mut v___x_6080_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec(v_val_6069_);
                    v___x_6080_ = l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__7;
                    return v___x_6080_;
                }
            } else {
                let mut v___x_6081_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_val_6069_);
                v___x_6081_ = l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__8;
                return v___x_6081_;
            }
        } else {
            let mut v___x_6082_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_val_6069_);
            v___x_6082_ = l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__9;
            return v___x_6082_;
        }
    }
}
pub unsafe fn l_Lean_JsonRpc_instToJsonMessageKind_toJson(mut v_x_6093_: u8) -> *mut LeanObject {
    match v_x_6093_ {
        0 => {
            let mut v___x_6094_: *mut LeanObject = core::ptr::null_mut();
            v___x_6094_ = l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__0;
            return v___x_6094_;
        }
        1 => {
            let mut v___x_6095_: *mut LeanObject = core::ptr::null_mut();
            v___x_6095_ = l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__1;
            return v___x_6095_;
        }
        2 => {
            let mut v___x_6096_: *mut LeanObject = core::ptr::null_mut();
            v___x_6096_ = l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__2;
            return v___x_6096_;
        }
        _ => {
            let mut v___x_6097_: *mut LeanObject = core::ptr::null_mut();
            v___x_6097_ = l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__3;
            return v___x_6097_;
        }
    }
}
pub unsafe fn l_Lean_JsonRpc_instToJsonMessageKind_toJson___boxed(
    mut v_x_6098_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_84__boxed_6099_: u8 = 0;
    let mut v_res_6100_: *mut LeanObject = core::ptr::null_mut();
    v_x_84__boxed_6099_ = (lean_unbox(v_x_6098_) as u8);
    v_res_6100_ = l_Lean_JsonRpc_instToJsonMessageKind_toJson(v_x_84__boxed_6099_);
    return v_res_6100_;
}
pub unsafe fn l_Lean_JsonRpc_MessageKind_ofMessage(mut v_x_6103_: *mut LeanObject) -> u8 {
    match lean_obj_tag(v_x_6103_) {
        0 => {
            let mut v___x_6104_: u8 = 0;
            v___x_6104_ = 0;
            return v___x_6104_;
        }
        1 => {
            let mut v___x_6105_: u8 = 0;
            v___x_6105_ = 1;
            return v___x_6105_;
        }
        2 => {
            let mut v___x_6106_: u8 = 0;
            v___x_6106_ = 2;
            return v___x_6106_;
        }
        _ => {
            let mut v___x_6107_: u8 = 0;
            v___x_6107_ = 3;
            return v___x_6107_;
        }
    }
}
pub unsafe fn l_Lean_JsonRpc_MessageKind_ofMessage___boxed(
    mut v_x_6108_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6109_: u8 = 0;
    let mut v_r_6110_: *mut LeanObject = core::ptr::null_mut();
    v_res_6109_ = l_Lean_JsonRpc_MessageKind_ofMessage(v_x_6108_);
    lean_dec_ref(v_x_6108_);
    v_r_6110_ = lean_box((v_res_6109_) as usize);
    return v_r_6110_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00IO_FS_Stream_readMessage_spec__0(
    mut v_j_6111_: *mut LeanObject,
    mut v_k_6112_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6114_: *mut LeanObject = core::ptr::null_mut();
    v___x_6113_ = l_Lean_Json_getObjValD(v_j_6111_, v_k_6112_);
    v___x_6114_ = l_Lean_Json_Structured_fromJson_x3f(v___x_6113_);
    return v___x_6114_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00IO_FS_Stream_readMessage_spec__0___boxed(
    mut v_j_6115_: *mut LeanObject,
    mut v_k_6116_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6117_: *mut LeanObject = core::ptr::null_mut();
    v_res_6117_ =
        l_Lean_Json_getObjValAs_x3f___at___00IO_FS_Stream_readMessage_spec__0(v_j_6115_, v_k_6116_);
    lean_dec_ref(v_k_6116_);
    return v_res_6117_;
}
pub unsafe fn l_IO_FS_Stream_readMessage(
    mut v_h_6120_: *mut LeanObject,
    mut v_nBytes_6121_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6127_: u8 = 0;
    let mut v___y_6129_: u8 = 0;
    let mut v___y_6130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_6158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6160_: u8 = 0;
    let mut v___x_6161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6181_: u8 = 0;
    let mut v_a_6182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6185_: u8 = 0;
    let mut v___x_6187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6188_: u8 = 0;
    let mut v_reuseFailAlloc_6189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6190_: u8 = 0;
    let mut v___x_6192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6200_: u8 = 0;
    let mut v___x_6201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6205_: u8 = 0;
    let mut v_a_6206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6213_: u8 = 0;
    let mut v___x_6215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6217_: u8 = 0;
    let mut v_a_6218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6224_: u8 = 0;
    let mut v___y_6226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6237_: u8 = 0;
    let mut v___x_6239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6241_: u8 = 0;
    let mut v_isSharedCheck_6242_: u8 = 0;
    let mut v_isSharedCheck_6243_: u8 = 0;
    let mut v_a_6244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6247_: u8 = 0;
    let mut v___x_6249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6251_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6123_ = l_IO_FS_Stream_readJson(v_h_6120_, v_nBytes_6121_);
                if lean_obj_tag(v___x_6123_) == 0 {
                    v_a_6124_ = lean_ctor_get(v___x_6123_, 0);
                    v_isSharedCheck_6243_ = (!lean_is_exclusive(v___x_6123_)) as u8;
                    if v_isSharedCheck_6243_ == 0 {
                        v___x_6126_ = v___x_6123_;
                        v_isShared_6127_ = v_isSharedCheck_6243_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6124_);
                        lean_dec(v___x_6123_);
                        v___x_6126_ = lean_box(0);
                        v_isShared_6127_ = v_isSharedCheck_6243_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6244_ = lean_ctor_get(v___x_6123_, 0);
                    v_isSharedCheck_6251_ = (!lean_is_exclusive(v___x_6123_)) as u8;
                    if v_isSharedCheck_6251_ == 0 {
                        v___x_6246_ = v___x_6123_;
                        v_isShared_6247_ = v_isSharedCheck_6251_;
                        state = 20;
                        continue;
                    } else {
                        lean_inc(v_a_6244_);
                        lean_dec(v___x_6123_);
                        v___x_6246_ = lean_box(0);
                        v_isShared_6247_ = v_isSharedCheck_6251_;
                        state = 20;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6154_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__0;
                lean_inc(v_a_6124_);
                v___x_6155_ = l_Lean_Json_getObjVal_x3f(v_a_6124_, v___x_6154_);
                if lean_obj_tag(v___x_6155_) == 0 {
                    lean_del_object(v___x_6126_);
                    v_a_6156_ = lean_ctor_get(v___x_6155_, 0);
                    lean_inc(v_a_6156_);
                    lean_dec_ref_known(v___x_6155_, 1);
                    v_a_6143_ = v_a_6156_;
                    state = 5;
                    continue;
                } else {
                    v_a_6157_ = lean_ctor_get(v___x_6155_, 0);
                    lean_inc(v_a_6157_);
                    lean_dec_ref_known(v___x_6155_, 1);
                    if lean_obj_tag(v_a_6157_) == 3 {
                        v_s_6158_ = lean_ctor_get(v_a_6157_, 0);
                        lean_inc_ref(v_s_6158_);
                        lean_dec_ref_known(v_a_6157_, 1);
                        v___x_6159_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__1;
                        v___x_6160_ = lean_string_dec_eq(v_s_6158_, v___x_6159_);
                        lean_dec_ref(v_s_6158_);
                        if v___x_6160_ == 0 {
                            lean_del_object(v___x_6126_);
                            state = 6;
                            continue;
                        } else {
                            v___x_6161_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4;
                            lean_inc(v_a_6124_);
                            v___x_6162_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0(v_a_6124_, v___x_6161_);
                            if lean_obj_tag(v___x_6162_) == 0 {
                                state = 10;
                                continue;
                            } else {
                                v_a_6218_ = lean_ctor_get(v___x_6162_, 0);
                                lean_inc(v_a_6218_);
                                v___x_6219_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
                                lean_inc(v_a_6124_);
                                v___x_6220_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_a_6124_, v___x_6219_);
                                if lean_obj_tag(v___x_6220_) == 0 {
                                    lean_dec_ref_known(v___x_6220_, 1);
                                    lean_dec(v_a_6218_);
                                    state = 10;
                                    continue;
                                } else {
                                    lean_dec_ref_known(v___x_6162_, 1);
                                    lean_del_object(v___x_6126_);
                                    v_a_6221_ = lean_ctor_get(v___x_6220_, 0);
                                    v_isSharedCheck_6242_ = (!lean_is_exclusive(v___x_6220_)) as u8;
                                    if v_isSharedCheck_6242_ == 0 {
                                        v___x_6223_ = v___x_6220_;
                                        v_isShared_6224_ = v_isSharedCheck_6242_;
                                        state = 15;
                                        continue;
                                    } else {
                                        lean_inc(v_a_6221_);
                                        lean_dec(v___x_6220_);
                                        v___x_6223_ = lean_box(0);
                                        v_isShared_6224_ = v_isSharedCheck_6242_;
                                        state = 15;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        lean_dec(v_a_6157_);
                        lean_del_object(v___x_6126_);
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v___x_6133_ = lean_alloc_ctor(3, 3, (1) as u32);
                lean_ctor_set(v___x_6133_, 0, v___y_6130_);
                lean_ctor_set(v___x_6133_, 1, v___y_6131_);
                lean_ctor_set(v___x_6133_, 2, v___y_6132_);
                lean_ctor_set_uint8(
                    v___x_6133_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___y_6129_,
                );
                if v_isShared_6127_ == 0 {
                    lean_ctor_set(v___x_6126_, 0, v___x_6133_);
                    v___x_6135_ = v___x_6126_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6136_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6136_, 0, v___x_6133_);
                    v___x_6135_ = v_reuseFailAlloc_6136_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6135_;
            }
            4 => {
                v___x_6140_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6140_, 0, v___y_6138_);
                lean_ctor_set(v___x_6140_, 1, v___y_6139_);
                v___x_6141_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6141_, 0, v___x_6140_);
                return v___x_6141_;
            }
            5 => {
                v___x_6144_ = l_IO_FS_Stream_readMessage___closed__0;
                v___x_6145_ = l_Lean_Json_compress(v_a_6124_);
                v___x_6146_ = lean_string_append(v___x_6144_, v___x_6145_);
                lean_dec_ref(v___x_6145_);
                v___x_6147_ = l_IO_FS_Stream_readMessage___closed__1;
                v___x_6148_ = lean_string_append(v___x_6146_, v___x_6147_);
                v___x_6149_ = lean_string_append(v___x_6148_, v_a_6143_);
                lean_dec_ref(v_a_6143_);
                v___x_6150_ = lean_mk_io_user_error(v___x_6149_);
                v___x_6151_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_6151_, 0, v___x_6150_);
                return v___x_6151_;
            }
            6 => {
                v___x_6153_ = l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__0;
                v_a_6143_ = v___x_6153_;
                state = 5;
                continue;
            }
            7 => {
                if lean_obj_tag(v___x_6162_) == 0 {
                    lean_del_object(v___x_6126_);
                    v_a_6164_ = lean_ctor_get(v___x_6162_, 0);
                    lean_inc(v_a_6164_);
                    lean_dec_ref_known(v___x_6162_, 1);
                    v_a_6143_ = v_a_6164_;
                    state = 5;
                    continue;
                } else {
                    v_a_6165_ = lean_ctor_get(v___x_6162_, 0);
                    lean_inc(v_a_6165_);
                    lean_dec_ref_known(v___x_6162_, 1);
                    v___x_6166_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10;
                    lean_inc(v_a_6124_);
                    v___x_6167_ = l_Lean_Json_getObjVal_x3f(v_a_6124_, v___x_6166_);
                    if lean_obj_tag(v___x_6167_) == 0 {
                        lean_dec(v_a_6165_);
                        lean_del_object(v___x_6126_);
                        v_a_6168_ = lean_ctor_get(v___x_6167_, 0);
                        lean_inc(v_a_6168_);
                        lean_dec_ref_known(v___x_6167_, 1);
                        v_a_6143_ = v_a_6168_;
                        state = 5;
                        continue;
                    } else {
                        v_a_6169_ = lean_ctor_get(v___x_6167_, 0);
                        lean_inc_n(v_a_6169_, 2);
                        lean_dec_ref_known(v___x_6167_, 1);
                        v___x_6170_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11;
                        v___x_6171_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1(v_a_6169_, v___x_6170_);
                        if lean_obj_tag(v___x_6171_) == 0 {
                            lean_dec(v_a_6169_);
                            lean_dec(v_a_6165_);
                            lean_del_object(v___x_6126_);
                            v_a_6172_ = lean_ctor_get(v___x_6171_, 0);
                            lean_inc(v_a_6172_);
                            lean_dec_ref_known(v___x_6171_, 1);
                            v_a_6143_ = v_a_6172_;
                            state = 5;
                            continue;
                        } else {
                            v_a_6173_ = lean_ctor_get(v___x_6171_, 0);
                            lean_inc(v_a_6173_);
                            lean_dec_ref_known(v___x_6171_, 1);
                            v___x_6174_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8;
                            lean_inc(v_a_6169_);
                            v___x_6175_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_a_6169_, v___x_6174_);
                            if lean_obj_tag(v___x_6175_) == 0 {
                                lean_dec(v_a_6173_);
                                lean_dec(v_a_6169_);
                                lean_dec(v_a_6165_);
                                lean_del_object(v___x_6126_);
                                v_a_6176_ = lean_ctor_get(v___x_6175_, 0);
                                lean_inc(v_a_6176_);
                                lean_dec_ref_known(v___x_6175_, 1);
                                v_a_6143_ = v_a_6176_;
                                state = 5;
                                continue;
                            } else {
                                lean_dec(v_a_6124_);
                                v_a_6177_ = lean_ctor_get(v___x_6175_, 0);
                                lean_inc(v_a_6177_);
                                lean_dec_ref_known(v___x_6175_, 1);
                                v___x_6178_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9;
                                v___x_6179_ = l_Lean_Json_getObjVal_x3f(v_a_6169_, v___x_6178_);
                                if lean_obj_tag(v___x_6179_) == 0 {
                                    lean_dec_ref_known(v___x_6179_, 1);
                                    v___x_6180_ = lean_box(0);
                                    v___x_6181_ = (lean_unbox(v_a_6173_) as u8);
                                    lean_dec(v_a_6173_);
                                    v___y_6129_ = v___x_6181_;
                                    v___y_6130_ = v_a_6165_;
                                    v___y_6131_ = v_a_6177_;
                                    v___y_6132_ = v___x_6180_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_a_6182_ = lean_ctor_get(v___x_6179_, 0);
                                    v_isSharedCheck_6190_ = (!lean_is_exclusive(v___x_6179_)) as u8;
                                    if v_isSharedCheck_6190_ == 0 {
                                        v___x_6184_ = v___x_6179_;
                                        v_isShared_6185_ = v_isSharedCheck_6190_;
                                        state = 8;
                                        continue;
                                    } else {
                                        lean_inc(v_a_6182_);
                                        lean_dec(v___x_6179_);
                                        v___x_6184_ = lean_box(0);
                                        v_isShared_6185_ = v_isSharedCheck_6190_;
                                        state = 8;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            8 => {
                if v_isShared_6185_ == 0 {
                    v___x_6187_ = v___x_6184_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6189_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6189_, 0, v_a_6182_);
                    v___x_6187_ = v_reuseFailAlloc_6189_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_6188_ = (lean_unbox(v_a_6173_) as u8);
                lean_dec(v_a_6173_);
                v___y_6129_ = v___x_6188_;
                v___y_6130_ = v_a_6165_;
                v___y_6131_ = v_a_6177_;
                v___y_6132_ = v___x_6187_;
                state = 2;
                continue;
            }
            10 => {
                v___x_6192_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
                lean_inc(v_a_6124_);
                v___x_6193_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_a_6124_, v___x_6192_);
                if lean_obj_tag(v___x_6193_) == 0 {
                    lean_dec_ref_known(v___x_6193_, 1);
                    if lean_obj_tag(v___x_6162_) == 0 {
                        state = 7;
                        continue;
                    } else {
                        v_a_6194_ = lean_ctor_get(v___x_6162_, 0);
                        lean_inc(v_a_6194_);
                        v___x_6195_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7;
                        lean_inc(v_a_6124_);
                        v___x_6196_ = l_Lean_Json_getObjVal_x3f(v_a_6124_, v___x_6195_);
                        if lean_obj_tag(v___x_6196_) == 0 {
                            lean_dec_ref_known(v___x_6196_, 1);
                            lean_dec(v_a_6194_);
                            state = 7;
                            continue;
                        } else {
                            lean_dec_ref_known(v___x_6162_, 1);
                            lean_del_object(v___x_6126_);
                            lean_dec(v_a_6124_);
                            v_a_6197_ = lean_ctor_get(v___x_6196_, 0);
                            v_isSharedCheck_6205_ = (!lean_is_exclusive(v___x_6196_)) as u8;
                            if v_isSharedCheck_6205_ == 0 {
                                v___x_6199_ = v___x_6196_;
                                v_isShared_6200_ = v_isSharedCheck_6205_;
                                state = 11;
                                continue;
                            } else {
                                lean_inc(v_a_6197_);
                                lean_dec(v___x_6196_);
                                v___x_6199_ = lean_box(0);
                                v_isShared_6200_ = v_isSharedCheck_6205_;
                                state = 11;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v___x_6162_);
                    lean_del_object(v___x_6126_);
                    v_a_6206_ = lean_ctor_get(v___x_6193_, 0);
                    lean_inc(v_a_6206_);
                    lean_dec_ref_known(v___x_6193_, 1);
                    v___x_6207_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6;
                    v___x_6208_ =
                        l_Lean_Json_getObjValAs_x3f___at___00IO_FS_Stream_readMessage_spec__0(
                            v_a_6124_,
                            v___x_6207_,
                        );
                    if lean_obj_tag(v___x_6208_) == 0 {
                        lean_dec_ref_known(v___x_6208_, 1);
                        v___x_6209_ = lean_box(0);
                        v___y_6138_ = v_a_6206_;
                        v___y_6139_ = v___x_6209_;
                        state = 4;
                        continue;
                    } else {
                        v_a_6210_ = lean_ctor_get(v___x_6208_, 0);
                        v_isSharedCheck_6217_ = (!lean_is_exclusive(v___x_6208_)) as u8;
                        if v_isSharedCheck_6217_ == 0 {
                            v___x_6212_ = v___x_6208_;
                            v_isShared_6213_ = v_isSharedCheck_6217_;
                            state = 13;
                            continue;
                        } else {
                            lean_inc(v_a_6210_);
                            lean_dec(v___x_6208_);
                            v___x_6212_ = lean_box(0);
                            v_isShared_6213_ = v_isSharedCheck_6217_;
                            state = 13;
                            continue;
                        }
                    }
                }
            }
            11 => {
                v___x_6201_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_6201_, 0, v_a_6194_);
                lean_ctor_set(v___x_6201_, 1, v_a_6197_);
                if v_isShared_6200_ == 0 {
                    lean_ctor_set_tag(v___x_6199_, 0);
                    lean_ctor_set(v___x_6199_, 0, v___x_6201_);
                    v___x_6203_ = v___x_6199_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_6204_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6204_, 0, v___x_6201_);
                    v___x_6203_ = v_reuseFailAlloc_6204_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_6203_;
            }
            13 => {
                if v_isShared_6213_ == 0 {
                    v___x_6215_ = v___x_6212_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_6216_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6216_, 0, v_a_6210_);
                    v___x_6215_ = v_reuseFailAlloc_6216_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___y_6138_ = v_a_6206_;
                v___y_6139_ = v___x_6215_;
                state = 4;
                continue;
            }
            15 => {
                v___x_6231_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6;
                v___x_6232_ = l_Lean_Json_getObjValAs_x3f___at___00IO_FS_Stream_readMessage_spec__0(
                    v_a_6124_,
                    v___x_6231_,
                );
                if lean_obj_tag(v___x_6232_) == 0 {
                    lean_dec_ref_known(v___x_6232_, 1);
                    v___x_6233_ = lean_box(0);
                    v___y_6226_ = v___x_6233_;
                    state = 16;
                    continue;
                } else {
                    v_a_6234_ = lean_ctor_get(v___x_6232_, 0);
                    v_isSharedCheck_6241_ = (!lean_is_exclusive(v___x_6232_)) as u8;
                    if v_isSharedCheck_6241_ == 0 {
                        v___x_6236_ = v___x_6232_;
                        v_isShared_6237_ = v_isSharedCheck_6241_;
                        state = 18;
                        continue;
                    } else {
                        lean_inc(v_a_6234_);
                        lean_dec(v___x_6232_);
                        v___x_6236_ = lean_box(0);
                        v_isShared_6237_ = v_isSharedCheck_6241_;
                        state = 18;
                        continue;
                    }
                }
            }
            16 => {
                v___x_6227_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_6227_, 0, v_a_6218_);
                lean_ctor_set(v___x_6227_, 1, v_a_6221_);
                lean_ctor_set(v___x_6227_, 2, v___y_6226_);
                if v_isShared_6224_ == 0 {
                    lean_ctor_set_tag(v___x_6223_, 0);
                    lean_ctor_set(v___x_6223_, 0, v___x_6227_);
                    v___x_6229_ = v___x_6223_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_6230_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6230_, 0, v___x_6227_);
                    v___x_6229_ = v_reuseFailAlloc_6230_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_6229_;
            }
            18 => {
                if v_isShared_6237_ == 0 {
                    v___x_6239_ = v___x_6236_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_6240_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6240_, 0, v_a_6234_);
                    v___x_6239_ = v_reuseFailAlloc_6240_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                v___y_6226_ = v___x_6239_;
                state = 16;
                continue;
            }
            20 => {
                if v_isShared_6247_ == 0 {
                    v___x_6249_ = v___x_6246_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_6250_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6250_, 0, v_a_6244_);
                    v___x_6249_ = v_reuseFailAlloc_6250_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_6249_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_FS_Stream_readMessage___boxed(
    mut v_h_6252_: *mut LeanObject,
    mut v_nBytes_6253_: *mut LeanObject,
    mut v_a_6254_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6255_: *mut LeanObject = core::ptr::null_mut();
    v_res_6255_ = l_IO_FS_Stream_readMessage(v_h_6252_, v_nBytes_6253_);
    lean_dec(v_nBytes_6253_);
    return v_res_6255_;
}
pub unsafe fn l_IO_FS_Stream_readRequestAs___redArg(
    mut v_h_6263_: *mut LeanObject,
    mut v_nBytes_6264_: *mut LeanObject,
    mut v_expectedMethod_6265_: *mut LeanObject,
    mut v_inst_6266_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6272_: u8 = 0;
    let mut v_id_6273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_method_6274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_x3f_6275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6278_: u8 = 0;
    let mut v___x_6279_: u8 = 0;
    let mut v___x_6280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6315_: u8 = 0;
    let mut v___x_6316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_6331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_method_6332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_x3f_6333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_6347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6350_: u8 = 0;
    let mut v___x_6352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6354_: u8 = 0;
    let mut v_n_6355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6358_: u8 = 0;
    let mut v___x_6360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6362_: u8 = 0;
    let mut v_method_6363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_x3f_6364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_6371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_result_6372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_6382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6385_: u8 = 0;
    let mut v___x_6387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6389_: u8 = 0;
    let mut v_n_6390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6393_: u8 = 0;
    let mut v___x_6395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6397_: u8 = 0;
    let mut v_id_6398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_6399_: u8 = 0;
    let mut v_message_6400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_x3f_6401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_6440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6443_: u8 = 0;
    let mut v___x_6445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6447_: u8 = 0;
    let mut v_n_6448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6451_: u8 = 0;
    let mut v___x_6453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6455_: u8 = 0;
    let mut v_isSharedCheck_6456_: u8 = 0;
    let mut v_a_6457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6460_: u8 = 0;
    let mut v___x_6462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6464_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6268_ = l_IO_FS_Stream_readMessage(v_h_6263_, v_nBytes_6264_);
                if lean_obj_tag(v___x_6268_) == 0 {
                    v_a_6269_ = lean_ctor_get(v___x_6268_, 0);
                    v_isSharedCheck_6456_ = (!lean_is_exclusive(v___x_6268_)) as u8;
                    if v_isSharedCheck_6456_ == 0 {
                        v___x_6271_ = v___x_6268_;
                        v_isShared_6272_ = v_isSharedCheck_6456_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6269_);
                        lean_dec(v___x_6268_);
                        v___x_6271_ = lean_box(0);
                        v_isShared_6272_ = v_isSharedCheck_6456_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_inst_6266_);
                    lean_dec_ref(v_expectedMethod_6265_);
                    v_a_6457_ = lean_ctor_get(v___x_6268_, 0);
                    v_isSharedCheck_6464_ = (!lean_is_exclusive(v___x_6268_)) as u8;
                    if v_isSharedCheck_6464_ == 0 {
                        v___x_6459_ = v___x_6268_;
                        v_isShared_6460_ = v_isSharedCheck_6464_;
                        state = 25;
                        continue;
                    } else {
                        lean_inc(v_a_6457_);
                        lean_dec(v___x_6268_);
                        v___x_6459_ = lean_box(0);
                        v_isShared_6460_ = v_isSharedCheck_6464_;
                        state = 25;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_6269_) == 0 {
                    v_id_6273_ = lean_ctor_get(v_a_6269_, 0);
                    v_method_6274_ = lean_ctor_get(v_a_6269_, 1);
                    v_params_x3f_6275_ = lean_ctor_get(v_a_6269_, 2);
                    v_isSharedCheck_6315_ = (!lean_is_exclusive(v_a_6269_)) as u8;
                    if v_isSharedCheck_6315_ == 0 {
                        v___x_6277_ = v_a_6269_;
                        v_isShared_6278_ = v_isSharedCheck_6315_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_params_x3f_6275_);
                        lean_inc(v_method_6274_);
                        lean_inc(v_id_6273_);
                        lean_dec(v_a_6269_);
                        v___x_6277_ = lean_box(0);
                        v_isShared_6278_ = v_isSharedCheck_6315_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_inst_6266_);
                    lean_dec_ref(v_expectedMethod_6265_);
                    v___x_6316_ = l_IO_FS_Stream_readRequestAs___redArg___closed__6;
                    v___x_6317_ = l_Lean_JsonRpc_instToJsonMessage___closed__0;
                    v___x_6318_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3;
                    match lean_obj_tag(v_a_6269_) {
                        0 => {
                            v_id_6331_ = lean_ctor_get(v_a_6269_, 0);
                            lean_inc(v_id_6331_);
                            v_method_6332_ = lean_ctor_get(v_a_6269_, 1);
                            lean_inc_ref(v_method_6332_);
                            v_params_x3f_6333_ = lean_ctor_get(v_a_6269_, 2);
                            lean_inc(v_params_x3f_6333_);
                            lean_dec_ref_known(v_a_6269_, 3);
                            v___x_6334_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4;
                            if lean_obj_tag(v_id_6331_) == 0 {
                                v_s_6347_ = lean_ctor_get(v_id_6331_, 0);
                                v_isSharedCheck_6354_ = (!lean_is_exclusive(v_id_6331_)) as u8;
                                if v_isSharedCheck_6354_ == 0 {
                                    v___x_6349_ = v_id_6331_;
                                    v_isShared_6350_ = v_isSharedCheck_6354_;
                                    state = 10;
                                    continue;
                                } else {
                                    lean_inc(v_s_6347_);
                                    lean_dec(v_id_6331_);
                                    v___x_6349_ = lean_box(0);
                                    v_isShared_6350_ = v_isSharedCheck_6354_;
                                    state = 10;
                                    continue;
                                }
                            } else {
                                v_n_6355_ = lean_ctor_get(v_id_6331_, 0);
                                v_isSharedCheck_6362_ = (!lean_is_exclusive(v_id_6331_)) as u8;
                                if v_isSharedCheck_6362_ == 0 {
                                    v___x_6357_ = v_id_6331_;
                                    v_isShared_6358_ = v_isSharedCheck_6362_;
                                    state = 12;
                                    continue;
                                } else {
                                    lean_inc(v_n_6355_);
                                    lean_dec(v_id_6331_);
                                    v___x_6357_ = lean_box(0);
                                    v_isShared_6358_ = v_isSharedCheck_6362_;
                                    state = 12;
                                    continue;
                                }
                            }
                        }
                        1 => {
                            v_method_6363_ = lean_ctor_get(v_a_6269_, 0);
                            lean_inc_ref(v_method_6363_);
                            v_params_x3f_6364_ = lean_ctor_get(v_a_6269_, 1);
                            lean_inc(v_params_x3f_6364_);
                            lean_dec_ref_known(v_a_6269_, 2);
                            v___x_6365_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
                            v___x_6366_ = lean_alloc_ctor(3, 1, (0) as u32);
                            lean_ctor_set(v___x_6366_, 0, v_method_6363_);
                            v___x_6367_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_6367_, 0, v___x_6365_);
                            lean_ctor_set(v___x_6367_, 1, v___x_6366_);
                            v___x_6368_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6;
                            v___x_6369_ = l_Lean_Json_opt___redArg(
                                v___x_6317_,
                                v___x_6368_,
                                v_params_x3f_6364_,
                            );
                            v___x_6370_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v___x_6370_, 0, v___x_6367_);
                            lean_ctor_set(v___x_6370_, 1, v___x_6369_);
                            v___y_6320_ = v___x_6370_;
                            state = 7;
                            continue;
                        }
                        2 => {
                            v_id_6371_ = lean_ctor_get(v_a_6269_, 0);
                            lean_inc(v_id_6371_);
                            v_result_6372_ = lean_ctor_get(v_a_6269_, 1);
                            lean_inc(v_result_6372_);
                            lean_dec_ref_known(v_a_6269_, 2);
                            v___x_6373_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4;
                            if lean_obj_tag(v_id_6371_) == 0 {
                                v_s_6382_ = lean_ctor_get(v_id_6371_, 0);
                                v_isSharedCheck_6389_ = (!lean_is_exclusive(v_id_6371_)) as u8;
                                if v_isSharedCheck_6389_ == 0 {
                                    v___x_6384_ = v_id_6371_;
                                    v_isShared_6385_ = v_isSharedCheck_6389_;
                                    state = 15;
                                    continue;
                                } else {
                                    lean_inc(v_s_6382_);
                                    lean_dec(v_id_6371_);
                                    v___x_6384_ = lean_box(0);
                                    v_isShared_6385_ = v_isSharedCheck_6389_;
                                    state = 15;
                                    continue;
                                }
                            } else {
                                v_n_6390_ = lean_ctor_get(v_id_6371_, 0);
                                v_isSharedCheck_6397_ = (!lean_is_exclusive(v_id_6371_)) as u8;
                                if v_isSharedCheck_6397_ == 0 {
                                    v___x_6392_ = v_id_6371_;
                                    v_isShared_6393_ = v_isSharedCheck_6397_;
                                    state = 17;
                                    continue;
                                } else {
                                    lean_inc(v_n_6390_);
                                    lean_dec(v_id_6371_);
                                    v___x_6392_ = lean_box(0);
                                    v_isShared_6393_ = v_isSharedCheck_6397_;
                                    state = 17;
                                    continue;
                                }
                            }
                        }
                        _ => {
                            v_id_6398_ = lean_ctor_get(v_a_6269_, 0);
                            lean_inc(v_id_6398_);
                            v_code_6399_ = lean_ctor_get_uint8(
                                v_a_6269_,
                                (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                            );
                            v_message_6400_ = lean_ctor_get(v_a_6269_, 1);
                            lean_inc_ref(v_message_6400_);
                            v_data_x3f_6401_ = lean_ctor_get(v_a_6269_, 2);
                            lean_inc(v_data_x3f_6401_);
                            lean_dec_ref_known(v_a_6269_, 3);
                            v___x_6402_ = l_Lean_JsonRpc_instToJsonMessage___closed__1;
                            v___x_6422_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4;
                            if lean_obj_tag(v_id_6398_) == 0 {
                                v_s_6440_ = lean_ctor_get(v_id_6398_, 0);
                                v_isSharedCheck_6447_ = (!lean_is_exclusive(v_id_6398_)) as u8;
                                if v_isSharedCheck_6447_ == 0 {
                                    v___x_6442_ = v_id_6398_;
                                    v_isShared_6443_ = v_isSharedCheck_6447_;
                                    state = 21;
                                    continue;
                                } else {
                                    lean_inc(v_s_6440_);
                                    lean_dec(v_id_6398_);
                                    v___x_6442_ = lean_box(0);
                                    v_isShared_6443_ = v_isSharedCheck_6447_;
                                    state = 21;
                                    continue;
                                }
                            } else {
                                v_n_6448_ = lean_ctor_get(v_id_6398_, 0);
                                v_isSharedCheck_6455_ = (!lean_is_exclusive(v_id_6398_)) as u8;
                                if v_isSharedCheck_6455_ == 0 {
                                    v___x_6450_ = v_id_6398_;
                                    v_isShared_6451_ = v_isSharedCheck_6455_;
                                    state = 23;
                                    continue;
                                } else {
                                    lean_inc(v_n_6448_);
                                    lean_dec(v_id_6398_);
                                    v___x_6450_ = lean_box(0);
                                    v_isShared_6451_ = v_isSharedCheck_6455_;
                                    state = 23;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_6279_ = lean_string_dec_eq(v_method_6274_, v_expectedMethod_6265_);
                if v___x_6279_ == 0 {
                    lean_del_object(v___x_6277_);
                    lean_dec(v_params_x3f_6275_);
                    lean_dec(v_id_6273_);
                    lean_dec_ref(v_inst_6266_);
                    v___x_6280_ = l_IO_FS_Stream_readRequestAs___redArg___closed__0;
                    v___x_6281_ = lean_string_append(v___x_6280_, v_expectedMethod_6265_);
                    lean_dec_ref(v_expectedMethod_6265_);
                    v___x_6282_ = l_IO_FS_Stream_readRequestAs___redArg___closed__1;
                    v___x_6283_ = lean_string_append(v___x_6281_, v___x_6282_);
                    v___x_6284_ = lean_string_append(v___x_6283_, v_method_6274_);
                    lean_dec_ref(v_method_6274_);
                    v___x_6285_ = l_IO_FS_Stream_readRequestAs___redArg___closed__2;
                    v___x_6286_ = lean_string_append(v___x_6284_, v___x_6285_);
                    v___x_6287_ = lean_mk_io_user_error(v___x_6286_);
                    if v_isShared_6272_ == 0 {
                        lean_ctor_set_tag(v___x_6271_, 1);
                        lean_ctor_set(v___x_6271_, 0, v___x_6287_);
                        v___x_6289_ = v___x_6271_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6290_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6290_, 0, v___x_6287_);
                        v___x_6289_ = v_reuseFailAlloc_6290_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_method_6274_);
                    v___x_6291_ = l_Lean_JsonRpc_instToJsonMessage___closed__0;
                    v___x_6292_ = l_Option_toJson___redArg(v___x_6291_, v_params_x3f_6275_);
                    lean_inc(v___x_6292_);
                    v___x_6293_ = lean_apply_1(v_inst_6266_, v___x_6292_);
                    if lean_obj_tag(v___x_6293_) == 0 {
                        lean_del_object(v___x_6277_);
                        lean_dec(v_id_6273_);
                        v_a_6294_ = lean_ctor_get(v___x_6293_, 0);
                        lean_inc(v_a_6294_);
                        lean_dec_ref_known(v___x_6293_, 1);
                        v___x_6295_ = l_IO_FS_Stream_readRequestAs___redArg___closed__3;
                        v___x_6296_ = l_Lean_Json_compress(v___x_6292_);
                        v___x_6297_ = lean_string_append(v___x_6295_, v___x_6296_);
                        lean_dec_ref(v___x_6296_);
                        v___x_6298_ = l_IO_FS_Stream_readRequestAs___redArg___closed__4;
                        v___x_6299_ = lean_string_append(v___x_6297_, v___x_6298_);
                        v___x_6300_ = lean_string_append(v___x_6299_, v_expectedMethod_6265_);
                        lean_dec_ref(v_expectedMethod_6265_);
                        v___x_6301_ = l_IO_FS_Stream_readRequestAs___redArg___closed__5;
                        v___x_6302_ = lean_string_append(v___x_6300_, v___x_6301_);
                        v___x_6303_ = lean_string_append(v___x_6302_, v_a_6294_);
                        lean_dec(v_a_6294_);
                        v___x_6304_ = lean_mk_io_user_error(v___x_6303_);
                        if v_isShared_6272_ == 0 {
                            lean_ctor_set_tag(v___x_6271_, 1);
                            lean_ctor_set(v___x_6271_, 0, v___x_6304_);
                            v___x_6306_ = v___x_6271_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_6307_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_6307_, 0, v___x_6304_);
                            v___x_6306_ = v_reuseFailAlloc_6307_;
                            state = 4;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_6292_);
                        v_a_6308_ = lean_ctor_get(v___x_6293_, 0);
                        lean_inc(v_a_6308_);
                        lean_dec_ref_known(v___x_6293_, 1);
                        if v_isShared_6278_ == 0 {
                            lean_ctor_set(v___x_6277_, 2, v_a_6308_);
                            lean_ctor_set(v___x_6277_, 1, v_expectedMethod_6265_);
                            v___x_6310_ = v___x_6277_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_6314_ = lean_alloc_ctor(0, 3, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_6314_, 0, v_id_6273_);
                            lean_ctor_set(v_reuseFailAlloc_6314_, 1, v_expectedMethod_6265_);
                            lean_ctor_set(v_reuseFailAlloc_6314_, 2, v_a_6308_);
                            v___x_6310_ = v_reuseFailAlloc_6314_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            3 => {
                return v___x_6289_;
            }
            4 => {
                return v___x_6306_;
            }
            5 => {
                if v_isShared_6272_ == 0 {
                    lean_ctor_set(v___x_6271_, 0, v___x_6310_);
                    v___x_6312_ = v___x_6271_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6313_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6313_, 0, v___x_6310_);
                    v___x_6312_ = v_reuseFailAlloc_6313_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6312_;
            }
            7 => {
                v___x_6321_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6321_, 0, v___x_6318_);
                lean_ctor_set(v___x_6321_, 1, v___y_6320_);
                v___x_6322_ = l_Lean_Json_mkObj(v___x_6321_);
                lean_dec_ref_known(v___x_6321_, 2);
                v___x_6323_ = l_Lean_Json_compress(v___x_6322_);
                v___x_6324_ = lean_string_append(v___x_6316_, v___x_6323_);
                lean_dec_ref(v___x_6323_);
                v___x_6325_ = l_IO_FS_Stream_readRequestAs___redArg___closed__2;
                v___x_6326_ = lean_string_append(v___x_6324_, v___x_6325_);
                v___x_6327_ = lean_mk_io_user_error(v___x_6326_);
                if v_isShared_6272_ == 0 {
                    lean_ctor_set_tag(v___x_6271_, 1);
                    lean_ctor_set(v___x_6271_, 0, v___x_6327_);
                    v___x_6329_ = v___x_6271_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6330_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6330_, 0, v___x_6327_);
                    v___x_6329_ = v_reuseFailAlloc_6330_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6329_;
            }
            9 => {
                v___x_6337_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6337_, 0, v___x_6334_);
                lean_ctor_set(v___x_6337_, 1, v___y_6336_);
                v___x_6338_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
                v___x_6339_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_6339_, 0, v_method_6332_);
                v___x_6340_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6340_, 0, v___x_6338_);
                lean_ctor_set(v___x_6340_, 1, v___x_6339_);
                v___x_6341_ = lean_box(0);
                v___x_6342_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6342_, 0, v___x_6340_);
                lean_ctor_set(v___x_6342_, 1, v___x_6341_);
                v___x_6343_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6343_, 0, v___x_6337_);
                lean_ctor_set(v___x_6343_, 1, v___x_6342_);
                v___x_6344_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6;
                v___x_6345_ =
                    l_Lean_Json_opt___redArg(v___x_6317_, v___x_6344_, v_params_x3f_6333_);
                v___x_6346_ = l_List_appendTR___redArg(v___x_6343_, v___x_6345_);
                v___y_6320_ = v___x_6346_;
                state = 7;
                continue;
            }
            10 => {
                if v_isShared_6350_ == 0 {
                    lean_ctor_set_tag(v___x_6349_, 3);
                    v___x_6352_ = v___x_6349_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6353_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6353_, 0, v_s_6347_);
                    v___x_6352_ = v_reuseFailAlloc_6353_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___y_6336_ = v___x_6352_;
                state = 9;
                continue;
            }
            12 => {
                if v_isShared_6358_ == 0 {
                    lean_ctor_set_tag(v___x_6357_, 2);
                    v___x_6360_ = v___x_6357_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_6361_ = lean_alloc_ctor(2, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6361_, 0, v_n_6355_);
                    v___x_6360_ = v_reuseFailAlloc_6361_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___y_6336_ = v___x_6360_;
                state = 9;
                continue;
            }
            14 => {
                v___x_6376_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6376_, 0, v___x_6373_);
                lean_ctor_set(v___x_6376_, 1, v___y_6375_);
                v___x_6377_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7;
                v___x_6378_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6378_, 0, v___x_6377_);
                lean_ctor_set(v___x_6378_, 1, v_result_6372_);
                v___x_6379_ = lean_box(0);
                v___x_6380_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6380_, 0, v___x_6378_);
                lean_ctor_set(v___x_6380_, 1, v___x_6379_);
                v___x_6381_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6381_, 0, v___x_6376_);
                lean_ctor_set(v___x_6381_, 1, v___x_6380_);
                v___y_6320_ = v___x_6381_;
                state = 7;
                continue;
            }
            15 => {
                if v_isShared_6385_ == 0 {
                    lean_ctor_set_tag(v___x_6384_, 3);
                    v___x_6387_ = v___x_6384_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_6388_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6388_, 0, v_s_6382_);
                    v___x_6387_ = v_reuseFailAlloc_6388_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___y_6375_ = v___x_6387_;
                state = 14;
                continue;
            }
            17 => {
                if v_isShared_6393_ == 0 {
                    lean_ctor_set_tag(v___x_6392_, 2);
                    v___x_6395_ = v___x_6392_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_6396_ = lean_alloc_ctor(2, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6396_, 0, v_n_6390_);
                    v___x_6395_ = v_reuseFailAlloc_6396_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v___y_6375_ = v___x_6395_;
                state = 14;
                continue;
            }
            19 => {
                lean_inc(v___y_6407_);
                lean_inc_ref(v___y_6406_);
                v___x_6408_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6408_, 0, v___y_6406_);
                lean_ctor_set(v___x_6408_, 1, v___y_6407_);
                v___x_6409_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8;
                v___x_6410_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_6410_, 0, v_message_6400_);
                v___x_6411_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6411_, 0, v___x_6409_);
                lean_ctor_set(v___x_6411_, 1, v___x_6410_);
                v___x_6412_ = lean_box(0);
                v___x_6413_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6413_, 0, v___x_6411_);
                lean_ctor_set(v___x_6413_, 1, v___x_6412_);
                v___x_6414_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6414_, 0, v___x_6408_);
                lean_ctor_set(v___x_6414_, 1, v___x_6413_);
                v___x_6415_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9;
                v___x_6416_ = l_Lean_Json_opt___redArg(v___x_6402_, v___x_6415_, v_data_x3f_6401_);
                v___x_6417_ = l_List_appendTR___redArg(v___x_6414_, v___x_6416_);
                v___x_6418_ = l_Lean_Json_mkObj(v___x_6417_);
                lean_dec(v___x_6417_);
                lean_inc_ref(v___y_6404_);
                v___x_6419_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6419_, 0, v___y_6404_);
                lean_ctor_set(v___x_6419_, 1, v___x_6418_);
                v___x_6420_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6420_, 0, v___x_6419_);
                lean_ctor_set(v___x_6420_, 1, v___x_6412_);
                v___x_6421_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6421_, 0, v___y_6405_);
                lean_ctor_set(v___x_6421_, 1, v___x_6420_);
                v___y_6320_ = v___x_6421_;
                state = 7;
                continue;
            }
            20 => {
                v___x_6425_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6425_, 0, v___x_6422_);
                lean_ctor_set(v___x_6425_, 1, v___y_6424_);
                v___x_6426_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10;
                v___x_6427_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11;
                match v_code_6399_ {
                    0 => {
                        v___x_6428_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1_once
                            ),
                            _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1,
                        );
                        v___y_6404_ = v___x_6426_;
                        v___y_6405_ = v___x_6425_;
                        v___y_6406_ = v___x_6427_;
                        v___y_6407_ = v___x_6428_;
                        state = 19;
                        continue;
                    }
                    1 => {
                        v___x_6429_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3_once
                            ),
                            _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3,
                        );
                        v___y_6404_ = v___x_6426_;
                        v___y_6405_ = v___x_6425_;
                        v___y_6406_ = v___x_6427_;
                        v___y_6407_ = v___x_6429_;
                        state = 19;
                        continue;
                    }
                    2 => {
                        v___x_6430_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5_once
                            ),
                            _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5,
                        );
                        v___y_6404_ = v___x_6426_;
                        v___y_6405_ = v___x_6425_;
                        v___y_6406_ = v___x_6427_;
                        v___y_6407_ = v___x_6430_;
                        state = 19;
                        continue;
                    }
                    3 => {
                        v___x_6431_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7_once
                            ),
                            _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7,
                        );
                        v___y_6404_ = v___x_6426_;
                        v___y_6405_ = v___x_6425_;
                        v___y_6406_ = v___x_6427_;
                        v___y_6407_ = v___x_6431_;
                        state = 19;
                        continue;
                    }
                    4 => {
                        v___x_6432_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9_once
                            ),
                            _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9,
                        );
                        v___y_6404_ = v___x_6426_;
                        v___y_6405_ = v___x_6425_;
                        v___y_6406_ = v___x_6427_;
                        v___y_6407_ = v___x_6432_;
                        state = 19;
                        continue;
                    }
                    5 => {
                        v___x_6433_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11_once
                            ),
                            _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11,
                        );
                        v___y_6404_ = v___x_6426_;
                        v___y_6405_ = v___x_6425_;
                        v___y_6406_ = v___x_6427_;
                        v___y_6407_ = v___x_6433_;
                        state = 19;
                        continue;
                    }
                    6 => {
                        v___x_6434_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13_once
                            ),
                            _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13,
                        );
                        v___y_6404_ = v___x_6426_;
                        v___y_6405_ = v___x_6425_;
                        v___y_6406_ = v___x_6427_;
                        v___y_6407_ = v___x_6434_;
                        state = 19;
                        continue;
                    }
                    7 => {
                        v___x_6435_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15_once
                            ),
                            _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15,
                        );
                        v___y_6404_ = v___x_6426_;
                        v___y_6405_ = v___x_6425_;
                        v___y_6406_ = v___x_6427_;
                        v___y_6407_ = v___x_6435_;
                        state = 19;
                        continue;
                    }
                    8 => {
                        v___x_6436_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17_once
                            ),
                            _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17,
                        );
                        v___y_6404_ = v___x_6426_;
                        v___y_6405_ = v___x_6425_;
                        v___y_6406_ = v___x_6427_;
                        v___y_6407_ = v___x_6436_;
                        state = 19;
                        continue;
                    }
                    9 => {
                        v___x_6437_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19_once
                            ),
                            _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19,
                        );
                        v___y_6404_ = v___x_6426_;
                        v___y_6405_ = v___x_6425_;
                        v___y_6406_ = v___x_6427_;
                        v___y_6407_ = v___x_6437_;
                        state = 19;
                        continue;
                    }
                    10 => {
                        v___x_6438_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21_once
                            ),
                            _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21,
                        );
                        v___y_6404_ = v___x_6426_;
                        v___y_6405_ = v___x_6425_;
                        v___y_6406_ = v___x_6427_;
                        v___y_6407_ = v___x_6438_;
                        state = 19;
                        continue;
                    }
                    _ => {
                        v___x_6439_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23_once
                            ),
                            _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23,
                        );
                        v___y_6404_ = v___x_6426_;
                        v___y_6405_ = v___x_6425_;
                        v___y_6406_ = v___x_6427_;
                        v___y_6407_ = v___x_6439_;
                        state = 19;
                        continue;
                    }
                }
            }
            21 => {
                if v_isShared_6443_ == 0 {
                    lean_ctor_set_tag(v___x_6442_, 3);
                    v___x_6445_ = v___x_6442_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_6446_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6446_, 0, v_s_6440_);
                    v___x_6445_ = v_reuseFailAlloc_6446_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                v___y_6424_ = v___x_6445_;
                state = 20;
                continue;
            }
            23 => {
                if v_isShared_6451_ == 0 {
                    lean_ctor_set_tag(v___x_6450_, 2);
                    v___x_6453_ = v___x_6450_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_6454_ = lean_alloc_ctor(2, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6454_, 0, v_n_6448_);
                    v___x_6453_ = v_reuseFailAlloc_6454_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                v___y_6424_ = v___x_6453_;
                state = 20;
                continue;
            }
            25 => {
                if v_isShared_6460_ == 0 {
                    v___x_6462_ = v___x_6459_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_6463_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6463_, 0, v_a_6457_);
                    v___x_6462_ = v_reuseFailAlloc_6463_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_6462_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_FS_Stream_readRequestAs___redArg___boxed(
    mut v_h_6465_: *mut LeanObject,
    mut v_nBytes_6466_: *mut LeanObject,
    mut v_expectedMethod_6467_: *mut LeanObject,
    mut v_inst_6468_: *mut LeanObject,
    mut v_a_6469_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6470_: *mut LeanObject = core::ptr::null_mut();
    v_res_6470_ = l_IO_FS_Stream_readRequestAs___redArg(
        v_h_6465_,
        v_nBytes_6466_,
        v_expectedMethod_6467_,
        v_inst_6468_,
    );
    lean_dec(v_nBytes_6466_);
    return v_res_6470_;
}
pub unsafe fn l_IO_FS_Stream_readRequestAs(
    mut v_h_6471_: *mut LeanObject,
    mut v_nBytes_6472_: *mut LeanObject,
    mut v_expectedMethod_6473_: *mut LeanObject,
    mut v_00_u03b1_6474_: *mut LeanObject,
    mut v_inst_6475_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6477_: *mut LeanObject = core::ptr::null_mut();
    v___x_6477_ = l_IO_FS_Stream_readRequestAs___redArg(
        v_h_6471_,
        v_nBytes_6472_,
        v_expectedMethod_6473_,
        v_inst_6475_,
    );
    return v___x_6477_;
}
pub unsafe fn l_IO_FS_Stream_readRequestAs___boxed(
    mut v_h_6478_: *mut LeanObject,
    mut v_nBytes_6479_: *mut LeanObject,
    mut v_expectedMethod_6480_: *mut LeanObject,
    mut v_00_u03b1_6481_: *mut LeanObject,
    mut v_inst_6482_: *mut LeanObject,
    mut v_a_6483_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6484_: *mut LeanObject = core::ptr::null_mut();
    v_res_6484_ = l_IO_FS_Stream_readRequestAs(
        v_h_6478_,
        v_nBytes_6479_,
        v_expectedMethod_6480_,
        v_00_u03b1_6481_,
        v_inst_6482_,
    );
    lean_dec(v_nBytes_6479_);
    return v_res_6484_;
}
pub unsafe fn l_IO_FS_Stream_readNotificationAs___redArg(
    mut v_h_6486_: *mut LeanObject,
    mut v_nBytes_6487_: *mut LeanObject,
    mut v_expectedMethod_6488_: *mut LeanObject,
    mut v_inst_6489_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6495_: u8 = 0;
    let mut v_method_6496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_x3f_6497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6500_: u8 = 0;
    let mut v___x_6501_: u8 = 0;
    let mut v___x_6502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6537_: u8 = 0;
    let mut v___x_6538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_6553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_method_6554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_x3f_6555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_6569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6572_: u8 = 0;
    let mut v___x_6574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6576_: u8 = 0;
    let mut v_n_6577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6580_: u8 = 0;
    let mut v___x_6582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6584_: u8 = 0;
    let mut v_method_6585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_x3f_6586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_6593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_result_6594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_6604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6607_: u8 = 0;
    let mut v___x_6609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6611_: u8 = 0;
    let mut v_n_6612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6615_: u8 = 0;
    let mut v___x_6617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6619_: u8 = 0;
    let mut v_id_6620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_6621_: u8 = 0;
    let mut v_message_6622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_x3f_6623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_6662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6665_: u8 = 0;
    let mut v___x_6667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6669_: u8 = 0;
    let mut v_n_6670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6673_: u8 = 0;
    let mut v___x_6675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6677_: u8 = 0;
    let mut v_isSharedCheck_6678_: u8 = 0;
    let mut v_a_6679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6682_: u8 = 0;
    let mut v___x_6684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6686_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6491_ = l_IO_FS_Stream_readMessage(v_h_6486_, v_nBytes_6487_);
                if lean_obj_tag(v___x_6491_) == 0 {
                    v_a_6492_ = lean_ctor_get(v___x_6491_, 0);
                    v_isSharedCheck_6678_ = (!lean_is_exclusive(v___x_6491_)) as u8;
                    if v_isSharedCheck_6678_ == 0 {
                        v___x_6494_ = v___x_6491_;
                        v_isShared_6495_ = v_isSharedCheck_6678_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6492_);
                        lean_dec(v___x_6491_);
                        v___x_6494_ = lean_box(0);
                        v_isShared_6495_ = v_isSharedCheck_6678_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_inst_6489_);
                    lean_dec_ref(v_expectedMethod_6488_);
                    v_a_6679_ = lean_ctor_get(v___x_6491_, 0);
                    v_isSharedCheck_6686_ = (!lean_is_exclusive(v___x_6491_)) as u8;
                    if v_isSharedCheck_6686_ == 0 {
                        v___x_6681_ = v___x_6491_;
                        v_isShared_6682_ = v_isSharedCheck_6686_;
                        state = 25;
                        continue;
                    } else {
                        lean_inc(v_a_6679_);
                        lean_dec(v___x_6491_);
                        v___x_6681_ = lean_box(0);
                        v_isShared_6682_ = v_isSharedCheck_6686_;
                        state = 25;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_6492_) == 1 {
                    v_method_6496_ = lean_ctor_get(v_a_6492_, 0);
                    v_params_x3f_6497_ = lean_ctor_get(v_a_6492_, 1);
                    v_isSharedCheck_6537_ = (!lean_is_exclusive(v_a_6492_)) as u8;
                    if v_isSharedCheck_6537_ == 0 {
                        v___x_6499_ = v_a_6492_;
                        v_isShared_6500_ = v_isSharedCheck_6537_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_params_x3f_6497_);
                        lean_inc(v_method_6496_);
                        lean_dec(v_a_6492_);
                        v___x_6499_ = lean_box(0);
                        v_isShared_6500_ = v_isSharedCheck_6537_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_inst_6489_);
                    lean_dec_ref(v_expectedMethod_6488_);
                    v___x_6538_ = l_IO_FS_Stream_readNotificationAs___redArg___closed__0;
                    v___x_6539_ = l_Lean_JsonRpc_instToJsonMessage___closed__0;
                    v___x_6540_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3;
                    match lean_obj_tag(v_a_6492_) {
                        0 => {
                            v_id_6553_ = lean_ctor_get(v_a_6492_, 0);
                            lean_inc(v_id_6553_);
                            v_method_6554_ = lean_ctor_get(v_a_6492_, 1);
                            lean_inc_ref(v_method_6554_);
                            v_params_x3f_6555_ = lean_ctor_get(v_a_6492_, 2);
                            lean_inc(v_params_x3f_6555_);
                            lean_dec_ref_known(v_a_6492_, 3);
                            v___x_6556_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4;
                            if lean_obj_tag(v_id_6553_) == 0 {
                                v_s_6569_ = lean_ctor_get(v_id_6553_, 0);
                                v_isSharedCheck_6576_ = (!lean_is_exclusive(v_id_6553_)) as u8;
                                if v_isSharedCheck_6576_ == 0 {
                                    v___x_6571_ = v_id_6553_;
                                    v_isShared_6572_ = v_isSharedCheck_6576_;
                                    state = 10;
                                    continue;
                                } else {
                                    lean_inc(v_s_6569_);
                                    lean_dec(v_id_6553_);
                                    v___x_6571_ = lean_box(0);
                                    v_isShared_6572_ = v_isSharedCheck_6576_;
                                    state = 10;
                                    continue;
                                }
                            } else {
                                v_n_6577_ = lean_ctor_get(v_id_6553_, 0);
                                v_isSharedCheck_6584_ = (!lean_is_exclusive(v_id_6553_)) as u8;
                                if v_isSharedCheck_6584_ == 0 {
                                    v___x_6579_ = v_id_6553_;
                                    v_isShared_6580_ = v_isSharedCheck_6584_;
                                    state = 12;
                                    continue;
                                } else {
                                    lean_inc(v_n_6577_);
                                    lean_dec(v_id_6553_);
                                    v___x_6579_ = lean_box(0);
                                    v_isShared_6580_ = v_isSharedCheck_6584_;
                                    state = 12;
                                    continue;
                                }
                            }
                        }
                        1 => {
                            v_method_6585_ = lean_ctor_get(v_a_6492_, 0);
                            lean_inc_ref(v_method_6585_);
                            v_params_x3f_6586_ = lean_ctor_get(v_a_6492_, 1);
                            lean_inc(v_params_x3f_6586_);
                            lean_dec_ref_known(v_a_6492_, 2);
                            v___x_6587_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
                            v___x_6588_ = lean_alloc_ctor(3, 1, (0) as u32);
                            lean_ctor_set(v___x_6588_, 0, v_method_6585_);
                            v___x_6589_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_6589_, 0, v___x_6587_);
                            lean_ctor_set(v___x_6589_, 1, v___x_6588_);
                            v___x_6590_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6;
                            v___x_6591_ = l_Lean_Json_opt___redArg(
                                v___x_6539_,
                                v___x_6590_,
                                v_params_x3f_6586_,
                            );
                            v___x_6592_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v___x_6592_, 0, v___x_6589_);
                            lean_ctor_set(v___x_6592_, 1, v___x_6591_);
                            v___y_6542_ = v___x_6592_;
                            state = 7;
                            continue;
                        }
                        2 => {
                            v_id_6593_ = lean_ctor_get(v_a_6492_, 0);
                            lean_inc(v_id_6593_);
                            v_result_6594_ = lean_ctor_get(v_a_6492_, 1);
                            lean_inc(v_result_6594_);
                            lean_dec_ref_known(v_a_6492_, 2);
                            v___x_6595_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4;
                            if lean_obj_tag(v_id_6593_) == 0 {
                                v_s_6604_ = lean_ctor_get(v_id_6593_, 0);
                                v_isSharedCheck_6611_ = (!lean_is_exclusive(v_id_6593_)) as u8;
                                if v_isSharedCheck_6611_ == 0 {
                                    v___x_6606_ = v_id_6593_;
                                    v_isShared_6607_ = v_isSharedCheck_6611_;
                                    state = 15;
                                    continue;
                                } else {
                                    lean_inc(v_s_6604_);
                                    lean_dec(v_id_6593_);
                                    v___x_6606_ = lean_box(0);
                                    v_isShared_6607_ = v_isSharedCheck_6611_;
                                    state = 15;
                                    continue;
                                }
                            } else {
                                v_n_6612_ = lean_ctor_get(v_id_6593_, 0);
                                v_isSharedCheck_6619_ = (!lean_is_exclusive(v_id_6593_)) as u8;
                                if v_isSharedCheck_6619_ == 0 {
                                    v___x_6614_ = v_id_6593_;
                                    v_isShared_6615_ = v_isSharedCheck_6619_;
                                    state = 17;
                                    continue;
                                } else {
                                    lean_inc(v_n_6612_);
                                    lean_dec(v_id_6593_);
                                    v___x_6614_ = lean_box(0);
                                    v_isShared_6615_ = v_isSharedCheck_6619_;
                                    state = 17;
                                    continue;
                                }
                            }
                        }
                        _ => {
                            v_id_6620_ = lean_ctor_get(v_a_6492_, 0);
                            lean_inc(v_id_6620_);
                            v_code_6621_ = lean_ctor_get_uint8(
                                v_a_6492_,
                                (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                            );
                            v_message_6622_ = lean_ctor_get(v_a_6492_, 1);
                            lean_inc_ref(v_message_6622_);
                            v_data_x3f_6623_ = lean_ctor_get(v_a_6492_, 2);
                            lean_inc(v_data_x3f_6623_);
                            lean_dec_ref_known(v_a_6492_, 3);
                            v___x_6624_ = l_Lean_JsonRpc_instToJsonMessage___closed__1;
                            v___x_6644_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4;
                            if lean_obj_tag(v_id_6620_) == 0 {
                                v_s_6662_ = lean_ctor_get(v_id_6620_, 0);
                                v_isSharedCheck_6669_ = (!lean_is_exclusive(v_id_6620_)) as u8;
                                if v_isSharedCheck_6669_ == 0 {
                                    v___x_6664_ = v_id_6620_;
                                    v_isShared_6665_ = v_isSharedCheck_6669_;
                                    state = 21;
                                    continue;
                                } else {
                                    lean_inc(v_s_6662_);
                                    lean_dec(v_id_6620_);
                                    v___x_6664_ = lean_box(0);
                                    v_isShared_6665_ = v_isSharedCheck_6669_;
                                    state = 21;
                                    continue;
                                }
                            } else {
                                v_n_6670_ = lean_ctor_get(v_id_6620_, 0);
                                v_isSharedCheck_6677_ = (!lean_is_exclusive(v_id_6620_)) as u8;
                                if v_isSharedCheck_6677_ == 0 {
                                    v___x_6672_ = v_id_6620_;
                                    v_isShared_6673_ = v_isSharedCheck_6677_;
                                    state = 23;
                                    continue;
                                } else {
                                    lean_inc(v_n_6670_);
                                    lean_dec(v_id_6620_);
                                    v___x_6672_ = lean_box(0);
                                    v_isShared_6673_ = v_isSharedCheck_6677_;
                                    state = 23;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_6501_ = lean_string_dec_eq(v_method_6496_, v_expectedMethod_6488_);
                if v___x_6501_ == 0 {
                    lean_del_object(v___x_6499_);
                    lean_dec(v_params_x3f_6497_);
                    lean_dec_ref(v_inst_6489_);
                    v___x_6502_ = l_IO_FS_Stream_readRequestAs___redArg___closed__0;
                    v___x_6503_ = lean_string_append(v___x_6502_, v_expectedMethod_6488_);
                    lean_dec_ref(v_expectedMethod_6488_);
                    v___x_6504_ = l_IO_FS_Stream_readRequestAs___redArg___closed__1;
                    v___x_6505_ = lean_string_append(v___x_6503_, v___x_6504_);
                    v___x_6506_ = lean_string_append(v___x_6505_, v_method_6496_);
                    lean_dec_ref(v_method_6496_);
                    v___x_6507_ = l_IO_FS_Stream_readRequestAs___redArg___closed__2;
                    v___x_6508_ = lean_string_append(v___x_6506_, v___x_6507_);
                    v___x_6509_ = lean_mk_io_user_error(v___x_6508_);
                    if v_isShared_6495_ == 0 {
                        lean_ctor_set_tag(v___x_6494_, 1);
                        lean_ctor_set(v___x_6494_, 0, v___x_6509_);
                        v___x_6511_ = v___x_6494_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6512_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6512_, 0, v___x_6509_);
                        v___x_6511_ = v_reuseFailAlloc_6512_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_method_6496_);
                    v___x_6513_ = l_Lean_JsonRpc_instToJsonMessage___closed__0;
                    v___x_6514_ = l_Option_toJson___redArg(v___x_6513_, v_params_x3f_6497_);
                    lean_inc(v___x_6514_);
                    v___x_6515_ = lean_apply_1(v_inst_6489_, v___x_6514_);
                    if lean_obj_tag(v___x_6515_) == 0 {
                        lean_del_object(v___x_6499_);
                        v_a_6516_ = lean_ctor_get(v___x_6515_, 0);
                        lean_inc(v_a_6516_);
                        lean_dec_ref_known(v___x_6515_, 1);
                        v___x_6517_ = l_IO_FS_Stream_readRequestAs___redArg___closed__3;
                        v___x_6518_ = l_Lean_Json_compress(v___x_6514_);
                        v___x_6519_ = lean_string_append(v___x_6517_, v___x_6518_);
                        lean_dec_ref(v___x_6518_);
                        v___x_6520_ = l_IO_FS_Stream_readRequestAs___redArg___closed__4;
                        v___x_6521_ = lean_string_append(v___x_6519_, v___x_6520_);
                        v___x_6522_ = lean_string_append(v___x_6521_, v_expectedMethod_6488_);
                        lean_dec_ref(v_expectedMethod_6488_);
                        v___x_6523_ = l_IO_FS_Stream_readRequestAs___redArg___closed__5;
                        v___x_6524_ = lean_string_append(v___x_6522_, v___x_6523_);
                        v___x_6525_ = lean_string_append(v___x_6524_, v_a_6516_);
                        lean_dec(v_a_6516_);
                        v___x_6526_ = lean_mk_io_user_error(v___x_6525_);
                        if v_isShared_6495_ == 0 {
                            lean_ctor_set_tag(v___x_6494_, 1);
                            lean_ctor_set(v___x_6494_, 0, v___x_6526_);
                            v___x_6528_ = v___x_6494_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_6529_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_6529_, 0, v___x_6526_);
                            v___x_6528_ = v_reuseFailAlloc_6529_;
                            state = 4;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_6514_);
                        v_a_6530_ = lean_ctor_get(v___x_6515_, 0);
                        lean_inc(v_a_6530_);
                        lean_dec_ref_known(v___x_6515_, 1);
                        if v_isShared_6500_ == 0 {
                            lean_ctor_set_tag(v___x_6499_, 0);
                            lean_ctor_set(v___x_6499_, 1, v_a_6530_);
                            lean_ctor_set(v___x_6499_, 0, v_expectedMethod_6488_);
                            v___x_6532_ = v___x_6499_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_6536_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_6536_, 0, v_expectedMethod_6488_);
                            lean_ctor_set(v_reuseFailAlloc_6536_, 1, v_a_6530_);
                            v___x_6532_ = v_reuseFailAlloc_6536_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            3 => {
                return v___x_6511_;
            }
            4 => {
                return v___x_6528_;
            }
            5 => {
                if v_isShared_6495_ == 0 {
                    lean_ctor_set(v___x_6494_, 0, v___x_6532_);
                    v___x_6534_ = v___x_6494_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6535_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6535_, 0, v___x_6532_);
                    v___x_6534_ = v_reuseFailAlloc_6535_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6534_;
            }
            7 => {
                v___x_6543_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6543_, 0, v___x_6540_);
                lean_ctor_set(v___x_6543_, 1, v___y_6542_);
                v___x_6544_ = l_Lean_Json_mkObj(v___x_6543_);
                lean_dec_ref_known(v___x_6543_, 2);
                v___x_6545_ = l_Lean_Json_compress(v___x_6544_);
                v___x_6546_ = lean_string_append(v___x_6538_, v___x_6545_);
                lean_dec_ref(v___x_6545_);
                v___x_6547_ = l_IO_FS_Stream_readRequestAs___redArg___closed__2;
                v___x_6548_ = lean_string_append(v___x_6546_, v___x_6547_);
                v___x_6549_ = lean_mk_io_user_error(v___x_6548_);
                if v_isShared_6495_ == 0 {
                    lean_ctor_set_tag(v___x_6494_, 1);
                    lean_ctor_set(v___x_6494_, 0, v___x_6549_);
                    v___x_6551_ = v___x_6494_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6552_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6552_, 0, v___x_6549_);
                    v___x_6551_ = v_reuseFailAlloc_6552_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6551_;
            }
            9 => {
                v___x_6559_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6559_, 0, v___x_6556_);
                lean_ctor_set(v___x_6559_, 1, v___y_6558_);
                v___x_6560_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
                v___x_6561_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_6561_, 0, v_method_6554_);
                v___x_6562_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6562_, 0, v___x_6560_);
                lean_ctor_set(v___x_6562_, 1, v___x_6561_);
                v___x_6563_ = lean_box(0);
                v___x_6564_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6564_, 0, v___x_6562_);
                lean_ctor_set(v___x_6564_, 1, v___x_6563_);
                v___x_6565_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6565_, 0, v___x_6559_);
                lean_ctor_set(v___x_6565_, 1, v___x_6564_);
                v___x_6566_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6;
                v___x_6567_ =
                    l_Lean_Json_opt___redArg(v___x_6539_, v___x_6566_, v_params_x3f_6555_);
                v___x_6568_ = l_List_appendTR___redArg(v___x_6565_, v___x_6567_);
                v___y_6542_ = v___x_6568_;
                state = 7;
                continue;
            }
            10 => {
                if v_isShared_6572_ == 0 {
                    lean_ctor_set_tag(v___x_6571_, 3);
                    v___x_6574_ = v___x_6571_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6575_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6575_, 0, v_s_6569_);
                    v___x_6574_ = v_reuseFailAlloc_6575_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___y_6558_ = v___x_6574_;
                state = 9;
                continue;
            }
            12 => {
                if v_isShared_6580_ == 0 {
                    lean_ctor_set_tag(v___x_6579_, 2);
                    v___x_6582_ = v___x_6579_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_6583_ = lean_alloc_ctor(2, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6583_, 0, v_n_6577_);
                    v___x_6582_ = v_reuseFailAlloc_6583_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___y_6558_ = v___x_6582_;
                state = 9;
                continue;
            }
            14 => {
                v___x_6598_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6598_, 0, v___x_6595_);
                lean_ctor_set(v___x_6598_, 1, v___y_6597_);
                v___x_6599_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7;
                v___x_6600_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6600_, 0, v___x_6599_);
                lean_ctor_set(v___x_6600_, 1, v_result_6594_);
                v___x_6601_ = lean_box(0);
                v___x_6602_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6602_, 0, v___x_6600_);
                lean_ctor_set(v___x_6602_, 1, v___x_6601_);
                v___x_6603_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6603_, 0, v___x_6598_);
                lean_ctor_set(v___x_6603_, 1, v___x_6602_);
                v___y_6542_ = v___x_6603_;
                state = 7;
                continue;
            }
            15 => {
                if v_isShared_6607_ == 0 {
                    lean_ctor_set_tag(v___x_6606_, 3);
                    v___x_6609_ = v___x_6606_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_6610_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6610_, 0, v_s_6604_);
                    v___x_6609_ = v_reuseFailAlloc_6610_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___y_6597_ = v___x_6609_;
                state = 14;
                continue;
            }
            17 => {
                if v_isShared_6615_ == 0 {
                    lean_ctor_set_tag(v___x_6614_, 2);
                    v___x_6617_ = v___x_6614_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_6618_ = lean_alloc_ctor(2, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6618_, 0, v_n_6612_);
                    v___x_6617_ = v_reuseFailAlloc_6618_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v___y_6597_ = v___x_6617_;
                state = 14;
                continue;
            }
            19 => {
                lean_inc(v___y_6629_);
                lean_inc_ref(v___y_6626_);
                v___x_6630_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6630_, 0, v___y_6626_);
                lean_ctor_set(v___x_6630_, 1, v___y_6629_);
                v___x_6631_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8;
                v___x_6632_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_6632_, 0, v_message_6622_);
                v___x_6633_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6633_, 0, v___x_6631_);
                lean_ctor_set(v___x_6633_, 1, v___x_6632_);
                v___x_6634_ = lean_box(0);
                v___x_6635_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6635_, 0, v___x_6633_);
                lean_ctor_set(v___x_6635_, 1, v___x_6634_);
                v___x_6636_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6636_, 0, v___x_6630_);
                lean_ctor_set(v___x_6636_, 1, v___x_6635_);
                v___x_6637_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9;
                v___x_6638_ = l_Lean_Json_opt___redArg(v___x_6624_, v___x_6637_, v_data_x3f_6623_);
                v___x_6639_ = l_List_appendTR___redArg(v___x_6636_, v___x_6638_);
                v___x_6640_ = l_Lean_Json_mkObj(v___x_6639_);
                lean_dec(v___x_6639_);
                lean_inc_ref(v___y_6627_);
                v___x_6641_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6641_, 0, v___y_6627_);
                lean_ctor_set(v___x_6641_, 1, v___x_6640_);
                v___x_6642_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6642_, 0, v___x_6641_);
                lean_ctor_set(v___x_6642_, 1, v___x_6634_);
                v___x_6643_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6643_, 0, v___y_6628_);
                lean_ctor_set(v___x_6643_, 1, v___x_6642_);
                v___y_6542_ = v___x_6643_;
                state = 7;
                continue;
            }
            20 => {
                v___x_6647_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6647_, 0, v___x_6644_);
                lean_ctor_set(v___x_6647_, 1, v___y_6646_);
                v___x_6648_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10;
                v___x_6649_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11;
                match v_code_6621_ {
                    0 => {
                        v___x_6650_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1_once
                            ),
                            _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1,
                        );
                        v___y_6626_ = v___x_6649_;
                        v___y_6627_ = v___x_6648_;
                        v___y_6628_ = v___x_6647_;
                        v___y_6629_ = v___x_6650_;
                        state = 19;
                        continue;
                    }
                    1 => {
                        v___x_6651_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3_once
                            ),
                            _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3,
                        );
                        v___y_6626_ = v___x_6649_;
                        v___y_6627_ = v___x_6648_;
                        v___y_6628_ = v___x_6647_;
                        v___y_6629_ = v___x_6651_;
                        state = 19;
                        continue;
                    }
                    2 => {
                        v___x_6652_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5_once
                            ),
                            _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5,
                        );
                        v___y_6626_ = v___x_6649_;
                        v___y_6627_ = v___x_6648_;
                        v___y_6628_ = v___x_6647_;
                        v___y_6629_ = v___x_6652_;
                        state = 19;
                        continue;
                    }
                    3 => {
                        v___x_6653_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7_once
                            ),
                            _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7,
                        );
                        v___y_6626_ = v___x_6649_;
                        v___y_6627_ = v___x_6648_;
                        v___y_6628_ = v___x_6647_;
                        v___y_6629_ = v___x_6653_;
                        state = 19;
                        continue;
                    }
                    4 => {
                        v___x_6654_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9_once
                            ),
                            _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9,
                        );
                        v___y_6626_ = v___x_6649_;
                        v___y_6627_ = v___x_6648_;
                        v___y_6628_ = v___x_6647_;
                        v___y_6629_ = v___x_6654_;
                        state = 19;
                        continue;
                    }
                    5 => {
                        v___x_6655_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11_once
                            ),
                            _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11,
                        );
                        v___y_6626_ = v___x_6649_;
                        v___y_6627_ = v___x_6648_;
                        v___y_6628_ = v___x_6647_;
                        v___y_6629_ = v___x_6655_;
                        state = 19;
                        continue;
                    }
                    6 => {
                        v___x_6656_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13_once
                            ),
                            _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13,
                        );
                        v___y_6626_ = v___x_6649_;
                        v___y_6627_ = v___x_6648_;
                        v___y_6628_ = v___x_6647_;
                        v___y_6629_ = v___x_6656_;
                        state = 19;
                        continue;
                    }
                    7 => {
                        v___x_6657_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15_once
                            ),
                            _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15,
                        );
                        v___y_6626_ = v___x_6649_;
                        v___y_6627_ = v___x_6648_;
                        v___y_6628_ = v___x_6647_;
                        v___y_6629_ = v___x_6657_;
                        state = 19;
                        continue;
                    }
                    8 => {
                        v___x_6658_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17_once
                            ),
                            _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17,
                        );
                        v___y_6626_ = v___x_6649_;
                        v___y_6627_ = v___x_6648_;
                        v___y_6628_ = v___x_6647_;
                        v___y_6629_ = v___x_6658_;
                        state = 19;
                        continue;
                    }
                    9 => {
                        v___x_6659_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19_once
                            ),
                            _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19,
                        );
                        v___y_6626_ = v___x_6649_;
                        v___y_6627_ = v___x_6648_;
                        v___y_6628_ = v___x_6647_;
                        v___y_6629_ = v___x_6659_;
                        state = 19;
                        continue;
                    }
                    10 => {
                        v___x_6660_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21_once
                            ),
                            _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21,
                        );
                        v___y_6626_ = v___x_6649_;
                        v___y_6627_ = v___x_6648_;
                        v___y_6628_ = v___x_6647_;
                        v___y_6629_ = v___x_6660_;
                        state = 19;
                        continue;
                    }
                    _ => {
                        v___x_6661_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23_once
                            ),
                            _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23,
                        );
                        v___y_6626_ = v___x_6649_;
                        v___y_6627_ = v___x_6648_;
                        v___y_6628_ = v___x_6647_;
                        v___y_6629_ = v___x_6661_;
                        state = 19;
                        continue;
                    }
                }
            }
            21 => {
                if v_isShared_6665_ == 0 {
                    lean_ctor_set_tag(v___x_6664_, 3);
                    v___x_6667_ = v___x_6664_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_6668_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6668_, 0, v_s_6662_);
                    v___x_6667_ = v_reuseFailAlloc_6668_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                v___y_6646_ = v___x_6667_;
                state = 20;
                continue;
            }
            23 => {
                if v_isShared_6673_ == 0 {
                    lean_ctor_set_tag(v___x_6672_, 2);
                    v___x_6675_ = v___x_6672_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_6676_ = lean_alloc_ctor(2, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6676_, 0, v_n_6670_);
                    v___x_6675_ = v_reuseFailAlloc_6676_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                v___y_6646_ = v___x_6675_;
                state = 20;
                continue;
            }
            25 => {
                if v_isShared_6682_ == 0 {
                    v___x_6684_ = v___x_6681_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_6685_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6685_, 0, v_a_6679_);
                    v___x_6684_ = v_reuseFailAlloc_6685_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_6684_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_FS_Stream_readNotificationAs___redArg___boxed(
    mut v_h_6687_: *mut LeanObject,
    mut v_nBytes_6688_: *mut LeanObject,
    mut v_expectedMethod_6689_: *mut LeanObject,
    mut v_inst_6690_: *mut LeanObject,
    mut v_a_6691_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6692_: *mut LeanObject = core::ptr::null_mut();
    v_res_6692_ = l_IO_FS_Stream_readNotificationAs___redArg(
        v_h_6687_,
        v_nBytes_6688_,
        v_expectedMethod_6689_,
        v_inst_6690_,
    );
    lean_dec(v_nBytes_6688_);
    return v_res_6692_;
}
pub unsafe fn l_IO_FS_Stream_readNotificationAs(
    mut v_h_6693_: *mut LeanObject,
    mut v_nBytes_6694_: *mut LeanObject,
    mut v_expectedMethod_6695_: *mut LeanObject,
    mut v_00_u03b1_6696_: *mut LeanObject,
    mut v_inst_6697_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6699_: *mut LeanObject = core::ptr::null_mut();
    v___x_6699_ = l_IO_FS_Stream_readNotificationAs___redArg(
        v_h_6693_,
        v_nBytes_6694_,
        v_expectedMethod_6695_,
        v_inst_6697_,
    );
    return v___x_6699_;
}
pub unsafe fn l_IO_FS_Stream_readNotificationAs___boxed(
    mut v_h_6700_: *mut LeanObject,
    mut v_nBytes_6701_: *mut LeanObject,
    mut v_expectedMethod_6702_: *mut LeanObject,
    mut v_00_u03b1_6703_: *mut LeanObject,
    mut v_inst_6704_: *mut LeanObject,
    mut v_a_6705_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6706_: *mut LeanObject = core::ptr::null_mut();
    v_res_6706_ = l_IO_FS_Stream_readNotificationAs(
        v_h_6700_,
        v_nBytes_6701_,
        v_expectedMethod_6702_,
        v_00_u03b1_6703_,
        v_inst_6704_,
    );
    lean_dec(v_nBytes_6701_);
    return v_res_6706_;
}
pub unsafe fn l_IO_FS_Stream_readResponseAs___redArg(
    mut v_h_6711_: *mut LeanObject,
    mut v_nBytes_6712_: *mut LeanObject,
    mut v_expectedID_6713_: *mut LeanObject,
    mut v_inst_6714_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6720_: u8 = 0;
    let mut v___y_6722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_6729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_result_6730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6733_: u8 = 0;
    let mut v___x_6734_: u8 = 0;
    let mut v___x_6735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_6741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_6745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_6747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_6751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6758_: u8 = 0;
    let mut v___x_6759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6769_: u8 = 0;
    let mut v_a_6770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6773_: u8 = 0;
    let mut v___x_6775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6780_: u8 = 0;
    let mut v_isSharedCheck_6781_: u8 = 0;
    let mut v___x_6782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_6795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_method_6796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_x3f_6797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_6811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6814_: u8 = 0;
    let mut v___x_6816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6818_: u8 = 0;
    let mut v_n_6819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6822_: u8 = 0;
    let mut v___x_6824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6826_: u8 = 0;
    let mut v_method_6827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_x3f_6828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_6835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_result_6836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_6846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6849_: u8 = 0;
    let mut v___x_6851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6853_: u8 = 0;
    let mut v_n_6854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6857_: u8 = 0;
    let mut v___x_6859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6861_: u8 = 0;
    let mut v_id_6862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_6863_: u8 = 0;
    let mut v_message_6864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_x3f_6865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_6904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6907_: u8 = 0;
    let mut v___x_6909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6911_: u8 = 0;
    let mut v_n_6912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6915_: u8 = 0;
    let mut v___x_6917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6919_: u8 = 0;
    let mut v_isSharedCheck_6920_: u8 = 0;
    let mut v_a_6921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6924_: u8 = 0;
    let mut v___x_6926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6928_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6716_ = l_IO_FS_Stream_readMessage(v_h_6711_, v_nBytes_6712_);
                if lean_obj_tag(v___x_6716_) == 0 {
                    v_a_6717_ = lean_ctor_get(v___x_6716_, 0);
                    v_isSharedCheck_6920_ = (!lean_is_exclusive(v___x_6716_)) as u8;
                    if v_isSharedCheck_6920_ == 0 {
                        v___x_6719_ = v___x_6716_;
                        v_isShared_6720_ = v_isSharedCheck_6920_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6717_);
                        lean_dec(v___x_6716_);
                        v___x_6719_ = lean_box(0);
                        v_isShared_6720_ = v_isSharedCheck_6920_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_inst_6714_);
                    lean_dec(v_expectedID_6713_);
                    v_a_6921_ = lean_ctor_get(v___x_6716_, 0);
                    v_isSharedCheck_6928_ = (!lean_is_exclusive(v___x_6716_)) as u8;
                    if v_isSharedCheck_6928_ == 0 {
                        v___x_6923_ = v___x_6716_;
                        v_isShared_6924_ = v_isSharedCheck_6928_;
                        state = 28;
                        continue;
                    } else {
                        lean_inc(v_a_6921_);
                        lean_dec(v___x_6716_);
                        v___x_6923_ = lean_box(0);
                        v_isShared_6924_ = v_isSharedCheck_6928_;
                        state = 28;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_6717_) == 2 {
                    v_id_6729_ = lean_ctor_get(v_a_6717_, 0);
                    v_result_6730_ = lean_ctor_get(v_a_6717_, 1);
                    v_isSharedCheck_6781_ = (!lean_is_exclusive(v_a_6717_)) as u8;
                    if v_isSharedCheck_6781_ == 0 {
                        v___x_6732_ = v_a_6717_;
                        v_isShared_6733_ = v_isSharedCheck_6781_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_result_6730_);
                        lean_inc(v_id_6729_);
                        lean_dec(v_a_6717_);
                        v___x_6732_ = lean_box(0);
                        v_isShared_6733_ = v_isSharedCheck_6781_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6719_);
                    lean_dec_ref(v_inst_6714_);
                    lean_dec(v_expectedID_6713_);
                    v___x_6782_ = l_IO_FS_Stream_readResponseAs___redArg___closed__3;
                    v___x_6783_ = l_Lean_JsonRpc_instToJsonMessage___closed__0;
                    v___x_6784_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3;
                    match lean_obj_tag(v_a_6717_) {
                        0 => {
                            v_id_6795_ = lean_ctor_get(v_a_6717_, 0);
                            lean_inc(v_id_6795_);
                            v_method_6796_ = lean_ctor_get(v_a_6717_, 1);
                            lean_inc_ref(v_method_6796_);
                            v_params_x3f_6797_ = lean_ctor_get(v_a_6717_, 2);
                            lean_inc(v_params_x3f_6797_);
                            lean_dec_ref_known(v_a_6717_, 3);
                            v___x_6798_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4;
                            if lean_obj_tag(v_id_6795_) == 0 {
                                v_s_6811_ = lean_ctor_get(v_id_6795_, 0);
                                v_isSharedCheck_6818_ = (!lean_is_exclusive(v_id_6795_)) as u8;
                                if v_isSharedCheck_6818_ == 0 {
                                    v___x_6813_ = v_id_6795_;
                                    v_isShared_6814_ = v_isSharedCheck_6818_;
                                    state = 13;
                                    continue;
                                } else {
                                    lean_inc(v_s_6811_);
                                    lean_dec(v_id_6795_);
                                    v___x_6813_ = lean_box(0);
                                    v_isShared_6814_ = v_isSharedCheck_6818_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                v_n_6819_ = lean_ctor_get(v_id_6795_, 0);
                                v_isSharedCheck_6826_ = (!lean_is_exclusive(v_id_6795_)) as u8;
                                if v_isSharedCheck_6826_ == 0 {
                                    v___x_6821_ = v_id_6795_;
                                    v_isShared_6822_ = v_isSharedCheck_6826_;
                                    state = 15;
                                    continue;
                                } else {
                                    lean_inc(v_n_6819_);
                                    lean_dec(v_id_6795_);
                                    v___x_6821_ = lean_box(0);
                                    v_isShared_6822_ = v_isSharedCheck_6826_;
                                    state = 15;
                                    continue;
                                }
                            }
                        }
                        1 => {
                            v_method_6827_ = lean_ctor_get(v_a_6717_, 0);
                            lean_inc_ref(v_method_6827_);
                            v_params_x3f_6828_ = lean_ctor_get(v_a_6717_, 1);
                            lean_inc(v_params_x3f_6828_);
                            lean_dec_ref_known(v_a_6717_, 2);
                            v___x_6829_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
                            v___x_6830_ = lean_alloc_ctor(3, 1, (0) as u32);
                            lean_ctor_set(v___x_6830_, 0, v_method_6827_);
                            v___x_6831_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_6831_, 0, v___x_6829_);
                            lean_ctor_set(v___x_6831_, 1, v___x_6830_);
                            v___x_6832_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6;
                            v___x_6833_ = l_Lean_Json_opt___redArg(
                                v___x_6783_,
                                v___x_6832_,
                                v_params_x3f_6828_,
                            );
                            v___x_6834_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v___x_6834_, 0, v___x_6831_);
                            lean_ctor_set(v___x_6834_, 1, v___x_6833_);
                            v___y_6786_ = v___x_6834_;
                            state = 11;
                            continue;
                        }
                        2 => {
                            v_id_6835_ = lean_ctor_get(v_a_6717_, 0);
                            lean_inc(v_id_6835_);
                            v_result_6836_ = lean_ctor_get(v_a_6717_, 1);
                            lean_inc(v_result_6836_);
                            lean_dec_ref_known(v_a_6717_, 2);
                            v___x_6837_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4;
                            if lean_obj_tag(v_id_6835_) == 0 {
                                v_s_6846_ = lean_ctor_get(v_id_6835_, 0);
                                v_isSharedCheck_6853_ = (!lean_is_exclusive(v_id_6835_)) as u8;
                                if v_isSharedCheck_6853_ == 0 {
                                    v___x_6848_ = v_id_6835_;
                                    v_isShared_6849_ = v_isSharedCheck_6853_;
                                    state = 18;
                                    continue;
                                } else {
                                    lean_inc(v_s_6846_);
                                    lean_dec(v_id_6835_);
                                    v___x_6848_ = lean_box(0);
                                    v_isShared_6849_ = v_isSharedCheck_6853_;
                                    state = 18;
                                    continue;
                                }
                            } else {
                                v_n_6854_ = lean_ctor_get(v_id_6835_, 0);
                                v_isSharedCheck_6861_ = (!lean_is_exclusive(v_id_6835_)) as u8;
                                if v_isSharedCheck_6861_ == 0 {
                                    v___x_6856_ = v_id_6835_;
                                    v_isShared_6857_ = v_isSharedCheck_6861_;
                                    state = 20;
                                    continue;
                                } else {
                                    lean_inc(v_n_6854_);
                                    lean_dec(v_id_6835_);
                                    v___x_6856_ = lean_box(0);
                                    v_isShared_6857_ = v_isSharedCheck_6861_;
                                    state = 20;
                                    continue;
                                }
                            }
                        }
                        _ => {
                            v_id_6862_ = lean_ctor_get(v_a_6717_, 0);
                            lean_inc(v_id_6862_);
                            v_code_6863_ = lean_ctor_get_uint8(
                                v_a_6717_,
                                (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                            );
                            v_message_6864_ = lean_ctor_get(v_a_6717_, 1);
                            lean_inc_ref(v_message_6864_);
                            v_data_x3f_6865_ = lean_ctor_get(v_a_6717_, 2);
                            lean_inc(v_data_x3f_6865_);
                            lean_dec_ref_known(v_a_6717_, 3);
                            v___x_6866_ = l_Lean_JsonRpc_instToJsonMessage___closed__1;
                            v___x_6886_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4;
                            if lean_obj_tag(v_id_6862_) == 0 {
                                v_s_6904_ = lean_ctor_get(v_id_6862_, 0);
                                v_isSharedCheck_6911_ = (!lean_is_exclusive(v_id_6862_)) as u8;
                                if v_isSharedCheck_6911_ == 0 {
                                    v___x_6906_ = v_id_6862_;
                                    v_isShared_6907_ = v_isSharedCheck_6911_;
                                    state = 24;
                                    continue;
                                } else {
                                    lean_inc(v_s_6904_);
                                    lean_dec(v_id_6862_);
                                    v___x_6906_ = lean_box(0);
                                    v_isShared_6907_ = v_isSharedCheck_6911_;
                                    state = 24;
                                    continue;
                                }
                            } else {
                                v_n_6912_ = lean_ctor_get(v_id_6862_, 0);
                                v_isSharedCheck_6919_ = (!lean_is_exclusive(v_id_6862_)) as u8;
                                if v_isSharedCheck_6919_ == 0 {
                                    v___x_6914_ = v_id_6862_;
                                    v_isShared_6915_ = v_isSharedCheck_6919_;
                                    state = 26;
                                    continue;
                                } else {
                                    lean_inc(v_n_6912_);
                                    lean_dec(v_id_6862_);
                                    v___x_6914_ = lean_box(0);
                                    v_isShared_6915_ = v_isSharedCheck_6919_;
                                    state = 26;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_6724_ = lean_string_append(v___y_6722_, v___y_6723_);
                lean_dec_ref(v___y_6723_);
                v___x_6725_ = lean_mk_io_user_error(v___x_6724_);
                if v_isShared_6720_ == 0 {
                    lean_ctor_set_tag(v___x_6719_, 1);
                    lean_ctor_set(v___x_6719_, 0, v___x_6725_);
                    v___x_6727_ = v___x_6719_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6728_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6728_, 0, v___x_6725_);
                    v___x_6727_ = v_reuseFailAlloc_6728_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6727_;
            }
            4 => {
                v___x_6734_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_6729_, v_expectedID_6713_);
                if v___x_6734_ == 0 {
                    lean_del_object(v___x_6732_);
                    lean_dec(v_result_6730_);
                    lean_dec_ref(v_inst_6714_);
                    v___x_6735_ = l_IO_FS_Stream_readResponseAs___redArg___closed__0;
                    match lean_obj_tag(v_expectedID_6713_) {
                        0 => {
                            v_s_6747_ = lean_ctor_get(v_expectedID_6713_, 0);
                            lean_inc_ref(v_s_6747_);
                            lean_dec_ref_known(v_expectedID_6713_, 1);
                            v___x_6748_ = l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__0;
                            v___x_6749_ = lean_string_append(v___x_6748_, v_s_6747_);
                            lean_dec_ref(v_s_6747_);
                            v___x_6750_ = lean_string_append(v___x_6749_, v___x_6748_);
                            v___y_6737_ = v___x_6750_;
                            state = 5;
                            continue;
                        }
                        1 => {
                            v_n_6751_ = lean_ctor_get(v_expectedID_6713_, 0);
                            lean_inc_ref(v_n_6751_);
                            lean_dec_ref_known(v_expectedID_6713_, 1);
                            v___x_6752_ = l_Lean_JsonNumber_toString(v_n_6751_);
                            v___y_6737_ = v___x_6752_;
                            state = 5;
                            continue;
                        }
                        _ => {
                            v___x_6753_ = l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__1;
                            v___y_6737_ = v___x_6753_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_id_6729_);
                    lean_del_object(v___x_6719_);
                    lean_inc(v_result_6730_);
                    v___x_6754_ = lean_apply_1(v_inst_6714_, v_result_6730_);
                    if lean_obj_tag(v___x_6754_) == 0 {
                        lean_del_object(v___x_6732_);
                        lean_dec(v_expectedID_6713_);
                        v_a_6755_ = lean_ctor_get(v___x_6754_, 0);
                        v_isSharedCheck_6769_ = (!lean_is_exclusive(v___x_6754_)) as u8;
                        if v_isSharedCheck_6769_ == 0 {
                            v___x_6757_ = v___x_6754_;
                            v_isShared_6758_ = v_isSharedCheck_6769_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_6755_);
                            lean_dec(v___x_6754_);
                            v___x_6757_ = lean_box(0);
                            v_isShared_6758_ = v_isSharedCheck_6769_;
                            state = 6;
                            continue;
                        }
                    } else {
                        lean_dec(v_result_6730_);
                        v_a_6770_ = lean_ctor_get(v___x_6754_, 0);
                        v_isSharedCheck_6780_ = (!lean_is_exclusive(v___x_6754_)) as u8;
                        if v_isSharedCheck_6780_ == 0 {
                            v___x_6772_ = v___x_6754_;
                            v_isShared_6773_ = v_isSharedCheck_6780_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_6770_);
                            lean_dec(v___x_6754_);
                            v___x_6772_ = lean_box(0);
                            v_isShared_6773_ = v_isSharedCheck_6780_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            5 => {
                v___x_6738_ = lean_string_append(v___x_6735_, v___y_6737_);
                lean_dec_ref(v___y_6737_);
                v___x_6739_ = l_IO_FS_Stream_readResponseAs___redArg___closed__1;
                v___x_6740_ = lean_string_append(v___x_6738_, v___x_6739_);
                if lean_obj_tag(v_id_6729_) == 0 {
                    v_s_6741_ = lean_ctor_get(v_id_6729_, 0);
                    lean_inc_ref(v_s_6741_);
                    lean_dec_ref_known(v_id_6729_, 1);
                    v___x_6742_ = l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__0;
                    v___x_6743_ = lean_string_append(v___x_6742_, v_s_6741_);
                    lean_dec_ref(v_s_6741_);
                    v___x_6744_ = lean_string_append(v___x_6743_, v___x_6742_);
                    v___y_6722_ = v___x_6740_;
                    v___y_6723_ = v___x_6744_;
                    state = 2;
                    continue;
                } else {
                    v_n_6745_ = lean_ctor_get(v_id_6729_, 0);
                    lean_inc_ref(v_n_6745_);
                    lean_dec_ref_known(v_id_6729_, 1);
                    v___x_6746_ = l_Lean_JsonNumber_toString(v_n_6745_);
                    v___y_6722_ = v___x_6740_;
                    v___y_6723_ = v___x_6746_;
                    state = 2;
                    continue;
                }
            }
            6 => {
                v___x_6759_ = l_IO_FS_Stream_readResponseAs___redArg___closed__2;
                v___x_6760_ = l_Lean_Json_compress(v_result_6730_);
                v___x_6761_ = lean_string_append(v___x_6759_, v___x_6760_);
                lean_dec_ref(v___x_6760_);
                v___x_6762_ = l_IO_FS_Stream_readRequestAs___redArg___closed__5;
                v___x_6763_ = lean_string_append(v___x_6761_, v___x_6762_);
                v___x_6764_ = lean_string_append(v___x_6763_, v_a_6755_);
                lean_dec(v_a_6755_);
                v___x_6765_ = lean_mk_io_user_error(v___x_6764_);
                if v_isShared_6758_ == 0 {
                    lean_ctor_set_tag(v___x_6757_, 1);
                    lean_ctor_set(v___x_6757_, 0, v___x_6765_);
                    v___x_6767_ = v___x_6757_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6768_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6768_, 0, v___x_6765_);
                    v___x_6767_ = v_reuseFailAlloc_6768_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6767_;
            }
            8 => {
                if v_isShared_6733_ == 0 {
                    lean_ctor_set_tag(v___x_6732_, 0);
                    lean_ctor_set(v___x_6732_, 1, v_a_6770_);
                    lean_ctor_set(v___x_6732_, 0, v_expectedID_6713_);
                    v___x_6775_ = v___x_6732_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6779_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6779_, 0, v_expectedID_6713_);
                    lean_ctor_set(v_reuseFailAlloc_6779_, 1, v_a_6770_);
                    v___x_6775_ = v_reuseFailAlloc_6779_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_6773_ == 0 {
                    lean_ctor_set_tag(v___x_6772_, 0);
                    lean_ctor_set(v___x_6772_, 0, v___x_6775_);
                    v___x_6777_ = v___x_6772_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6778_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6778_, 0, v___x_6775_);
                    v___x_6777_ = v_reuseFailAlloc_6778_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6777_;
            }
            11 => {
                v___x_6787_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6787_, 0, v___x_6784_);
                lean_ctor_set(v___x_6787_, 1, v___y_6786_);
                v___x_6788_ = l_Lean_Json_mkObj(v___x_6787_);
                lean_dec_ref_known(v___x_6787_, 2);
                v___x_6789_ = l_Lean_Json_compress(v___x_6788_);
                v___x_6790_ = lean_string_append(v___x_6782_, v___x_6789_);
                lean_dec_ref(v___x_6789_);
                v___x_6791_ = l_IO_FS_Stream_readRequestAs___redArg___closed__2;
                v___x_6792_ = lean_string_append(v___x_6790_, v___x_6791_);
                v___x_6793_ = lean_mk_io_user_error(v___x_6792_);
                v___x_6794_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_6794_, 0, v___x_6793_);
                return v___x_6794_;
            }
            12 => {
                v___x_6801_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6801_, 0, v___x_6798_);
                lean_ctor_set(v___x_6801_, 1, v___y_6800_);
                v___x_6802_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
                v___x_6803_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_6803_, 0, v_method_6796_);
                v___x_6804_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6804_, 0, v___x_6802_);
                lean_ctor_set(v___x_6804_, 1, v___x_6803_);
                v___x_6805_ = lean_box(0);
                v___x_6806_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6806_, 0, v___x_6804_);
                lean_ctor_set(v___x_6806_, 1, v___x_6805_);
                v___x_6807_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6807_, 0, v___x_6801_);
                lean_ctor_set(v___x_6807_, 1, v___x_6806_);
                v___x_6808_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6;
                v___x_6809_ =
                    l_Lean_Json_opt___redArg(v___x_6783_, v___x_6808_, v_params_x3f_6797_);
                v___x_6810_ = l_List_appendTR___redArg(v___x_6807_, v___x_6809_);
                v___y_6786_ = v___x_6810_;
                state = 11;
                continue;
            }
            13 => {
                if v_isShared_6814_ == 0 {
                    lean_ctor_set_tag(v___x_6813_, 3);
                    v___x_6816_ = v___x_6813_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_6817_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6817_, 0, v_s_6811_);
                    v___x_6816_ = v_reuseFailAlloc_6817_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___y_6800_ = v___x_6816_;
                state = 12;
                continue;
            }
            15 => {
                if v_isShared_6822_ == 0 {
                    lean_ctor_set_tag(v___x_6821_, 2);
                    v___x_6824_ = v___x_6821_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_6825_ = lean_alloc_ctor(2, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6825_, 0, v_n_6819_);
                    v___x_6824_ = v_reuseFailAlloc_6825_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___y_6800_ = v___x_6824_;
                state = 12;
                continue;
            }
            17 => {
                v___x_6840_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6840_, 0, v___x_6837_);
                lean_ctor_set(v___x_6840_, 1, v___y_6839_);
                v___x_6841_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7;
                v___x_6842_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6842_, 0, v___x_6841_);
                lean_ctor_set(v___x_6842_, 1, v_result_6836_);
                v___x_6843_ = lean_box(0);
                v___x_6844_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6844_, 0, v___x_6842_);
                lean_ctor_set(v___x_6844_, 1, v___x_6843_);
                v___x_6845_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6845_, 0, v___x_6840_);
                lean_ctor_set(v___x_6845_, 1, v___x_6844_);
                v___y_6786_ = v___x_6845_;
                state = 11;
                continue;
            }
            18 => {
                if v_isShared_6849_ == 0 {
                    lean_ctor_set_tag(v___x_6848_, 3);
                    v___x_6851_ = v___x_6848_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_6852_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6852_, 0, v_s_6846_);
                    v___x_6851_ = v_reuseFailAlloc_6852_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                v___y_6839_ = v___x_6851_;
                state = 17;
                continue;
            }
            20 => {
                if v_isShared_6857_ == 0 {
                    lean_ctor_set_tag(v___x_6856_, 2);
                    v___x_6859_ = v___x_6856_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_6860_ = lean_alloc_ctor(2, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6860_, 0, v_n_6854_);
                    v___x_6859_ = v_reuseFailAlloc_6860_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v___y_6839_ = v___x_6859_;
                state = 17;
                continue;
            }
            22 => {
                lean_inc(v___y_6871_);
                lean_inc_ref(v___y_6869_);
                v___x_6872_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6872_, 0, v___y_6869_);
                lean_ctor_set(v___x_6872_, 1, v___y_6871_);
                v___x_6873_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8;
                v___x_6874_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_6874_, 0, v_message_6864_);
                v___x_6875_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6875_, 0, v___x_6873_);
                lean_ctor_set(v___x_6875_, 1, v___x_6874_);
                v___x_6876_ = lean_box(0);
                v___x_6877_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6877_, 0, v___x_6875_);
                lean_ctor_set(v___x_6877_, 1, v___x_6876_);
                v___x_6878_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6878_, 0, v___x_6872_);
                lean_ctor_set(v___x_6878_, 1, v___x_6877_);
                v___x_6879_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9;
                v___x_6880_ = l_Lean_Json_opt___redArg(v___x_6866_, v___x_6879_, v_data_x3f_6865_);
                v___x_6881_ = l_List_appendTR___redArg(v___x_6878_, v___x_6880_);
                v___x_6882_ = l_Lean_Json_mkObj(v___x_6881_);
                lean_dec(v___x_6881_);
                lean_inc_ref(v___y_6870_);
                v___x_6883_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6883_, 0, v___y_6870_);
                lean_ctor_set(v___x_6883_, 1, v___x_6882_);
                v___x_6884_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6884_, 0, v___x_6883_);
                lean_ctor_set(v___x_6884_, 1, v___x_6876_);
                v___x_6885_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6885_, 0, v___y_6868_);
                lean_ctor_set(v___x_6885_, 1, v___x_6884_);
                v___y_6786_ = v___x_6885_;
                state = 11;
                continue;
            }
            23 => {
                v___x_6889_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6889_, 0, v___x_6886_);
                lean_ctor_set(v___x_6889_, 1, v___y_6888_);
                v___x_6890_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10;
                v___x_6891_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11;
                match v_code_6863_ {
                    0 => {
                        v___x_6892_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1_once
                            ),
                            _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1,
                        );
                        v___y_6868_ = v___x_6889_;
                        v___y_6869_ = v___x_6891_;
                        v___y_6870_ = v___x_6890_;
                        v___y_6871_ = v___x_6892_;
                        state = 22;
                        continue;
                    }
                    1 => {
                        v___x_6893_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3_once
                            ),
                            _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3,
                        );
                        v___y_6868_ = v___x_6889_;
                        v___y_6869_ = v___x_6891_;
                        v___y_6870_ = v___x_6890_;
                        v___y_6871_ = v___x_6893_;
                        state = 22;
                        continue;
                    }
                    2 => {
                        v___x_6894_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5_once
                            ),
                            _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5,
                        );
                        v___y_6868_ = v___x_6889_;
                        v___y_6869_ = v___x_6891_;
                        v___y_6870_ = v___x_6890_;
                        v___y_6871_ = v___x_6894_;
                        state = 22;
                        continue;
                    }
                    3 => {
                        v___x_6895_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7_once
                            ),
                            _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7,
                        );
                        v___y_6868_ = v___x_6889_;
                        v___y_6869_ = v___x_6891_;
                        v___y_6870_ = v___x_6890_;
                        v___y_6871_ = v___x_6895_;
                        state = 22;
                        continue;
                    }
                    4 => {
                        v___x_6896_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9_once
                            ),
                            _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9,
                        );
                        v___y_6868_ = v___x_6889_;
                        v___y_6869_ = v___x_6891_;
                        v___y_6870_ = v___x_6890_;
                        v___y_6871_ = v___x_6896_;
                        state = 22;
                        continue;
                    }
                    5 => {
                        v___x_6897_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11_once
                            ),
                            _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11,
                        );
                        v___y_6868_ = v___x_6889_;
                        v___y_6869_ = v___x_6891_;
                        v___y_6870_ = v___x_6890_;
                        v___y_6871_ = v___x_6897_;
                        state = 22;
                        continue;
                    }
                    6 => {
                        v___x_6898_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13_once
                            ),
                            _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13,
                        );
                        v___y_6868_ = v___x_6889_;
                        v___y_6869_ = v___x_6891_;
                        v___y_6870_ = v___x_6890_;
                        v___y_6871_ = v___x_6898_;
                        state = 22;
                        continue;
                    }
                    7 => {
                        v___x_6899_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15_once
                            ),
                            _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15,
                        );
                        v___y_6868_ = v___x_6889_;
                        v___y_6869_ = v___x_6891_;
                        v___y_6870_ = v___x_6890_;
                        v___y_6871_ = v___x_6899_;
                        state = 22;
                        continue;
                    }
                    8 => {
                        v___x_6900_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17_once
                            ),
                            _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17,
                        );
                        v___y_6868_ = v___x_6889_;
                        v___y_6869_ = v___x_6891_;
                        v___y_6870_ = v___x_6890_;
                        v___y_6871_ = v___x_6900_;
                        state = 22;
                        continue;
                    }
                    9 => {
                        v___x_6901_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19_once
                            ),
                            _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19,
                        );
                        v___y_6868_ = v___x_6889_;
                        v___y_6869_ = v___x_6891_;
                        v___y_6870_ = v___x_6890_;
                        v___y_6871_ = v___x_6901_;
                        state = 22;
                        continue;
                    }
                    10 => {
                        v___x_6902_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21_once
                            ),
                            _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21,
                        );
                        v___y_6868_ = v___x_6889_;
                        v___y_6869_ = v___x_6891_;
                        v___y_6870_ = v___x_6890_;
                        v___y_6871_ = v___x_6902_;
                        state = 22;
                        continue;
                    }
                    _ => {
                        v___x_6903_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23_once
                            ),
                            _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23,
                        );
                        v___y_6868_ = v___x_6889_;
                        v___y_6869_ = v___x_6891_;
                        v___y_6870_ = v___x_6890_;
                        v___y_6871_ = v___x_6903_;
                        state = 22;
                        continue;
                    }
                }
            }
            24 => {
                if v_isShared_6907_ == 0 {
                    lean_ctor_set_tag(v___x_6906_, 3);
                    v___x_6909_ = v___x_6906_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_6910_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6910_, 0, v_s_6904_);
                    v___x_6909_ = v_reuseFailAlloc_6910_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                v___y_6888_ = v___x_6909_;
                state = 23;
                continue;
            }
            26 => {
                if v_isShared_6915_ == 0 {
                    lean_ctor_set_tag(v___x_6914_, 2);
                    v___x_6917_ = v___x_6914_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_6918_ = lean_alloc_ctor(2, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6918_, 0, v_n_6912_);
                    v___x_6917_ = v_reuseFailAlloc_6918_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                v___y_6888_ = v___x_6917_;
                state = 23;
                continue;
            }
            28 => {
                if v_isShared_6924_ == 0 {
                    v___x_6926_ = v___x_6923_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_6927_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6927_, 0, v_a_6921_);
                    v___x_6926_ = v_reuseFailAlloc_6927_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_6926_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_FS_Stream_readResponseAs___redArg___boxed(
    mut v_h_6929_: *mut LeanObject,
    mut v_nBytes_6930_: *mut LeanObject,
    mut v_expectedID_6931_: *mut LeanObject,
    mut v_inst_6932_: *mut LeanObject,
    mut v_a_6933_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6934_: *mut LeanObject = core::ptr::null_mut();
    v_res_6934_ = l_IO_FS_Stream_readResponseAs___redArg(
        v_h_6929_,
        v_nBytes_6930_,
        v_expectedID_6931_,
        v_inst_6932_,
    );
    lean_dec(v_nBytes_6930_);
    return v_res_6934_;
}
pub unsafe fn l_IO_FS_Stream_readResponseAs(
    mut v_h_6935_: *mut LeanObject,
    mut v_nBytes_6936_: *mut LeanObject,
    mut v_expectedID_6937_: *mut LeanObject,
    mut v_00_u03b1_6938_: *mut LeanObject,
    mut v_inst_6939_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6941_: *mut LeanObject = core::ptr::null_mut();
    v___x_6941_ = l_IO_FS_Stream_readResponseAs___redArg(
        v_h_6935_,
        v_nBytes_6936_,
        v_expectedID_6937_,
        v_inst_6939_,
    );
    return v___x_6941_;
}
pub unsafe fn l_IO_FS_Stream_readResponseAs___boxed(
    mut v_h_6942_: *mut LeanObject,
    mut v_nBytes_6943_: *mut LeanObject,
    mut v_expectedID_6944_: *mut LeanObject,
    mut v_00_u03b1_6945_: *mut LeanObject,
    mut v_inst_6946_: *mut LeanObject,
    mut v_a_6947_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6948_: *mut LeanObject = core::ptr::null_mut();
    v_res_6948_ = l_IO_FS_Stream_readResponseAs(
        v_h_6942_,
        v_nBytes_6943_,
        v_expectedID_6944_,
        v_00_u03b1_6945_,
        v_inst_6946_,
    );
    lean_dec(v_nBytes_6943_);
    return v_res_6948_;
}
pub unsafe fn l_Lean_Json_opt___at___00IO_FS_Stream_writeMessage_spec__0(
    mut v_k_6949_: *mut LeanObject,
    mut v_x_6950_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_6950_) == 0 {
        let mut v___x_6951_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_k_6949_);
        v___x_6951_ = lean_box(0);
        return v___x_6951_;
    } else {
        let mut v_val_6952_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6953_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6954_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6955_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6956_: *mut LeanObject = core::ptr::null_mut();
        v_val_6952_ = lean_ctor_get(v_x_6950_, 0);
        lean_inc(v_val_6952_);
        lean_dec_ref_known(v_x_6950_, 1);
        v___x_6953_ = l_Lean_Json_Structured_toJson(v_val_6952_);
        v___x_6954_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_6954_, 0, v_k_6949_);
        lean_ctor_set(v___x_6954_, 1, v___x_6953_);
        v___x_6955_ = lean_box(0);
        v___x_6956_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_6956_, 0, v___x_6954_);
        lean_ctor_set(v___x_6956_, 1, v___x_6955_);
        return v___x_6956_;
    }
}
pub unsafe fn l_Lean_Json_opt___at___00IO_FS_Stream_writeMessage_spec__1(
    mut v_k_6957_: *mut LeanObject,
    mut v_x_6958_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_6958_) == 0 {
        let mut v___x_6959_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_k_6957_);
        v___x_6959_ = lean_box(0);
        return v___x_6959_;
    } else {
        let mut v_val_6960_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6961_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6962_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6963_: *mut LeanObject = core::ptr::null_mut();
        v_val_6960_ = lean_ctor_get(v_x_6958_, 0);
        lean_inc(v_val_6960_);
        v___x_6961_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_6961_, 0, v_k_6957_);
        lean_ctor_set(v___x_6961_, 1, v_val_6960_);
        v___x_6962_ = lean_box(0);
        v___x_6963_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_6963_, 0, v___x_6961_);
        lean_ctor_set(v___x_6963_, 1, v___x_6962_);
        return v___x_6963_;
    }
}
pub unsafe fn l_Lean_Json_opt___at___00IO_FS_Stream_writeMessage_spec__1___boxed(
    mut v_k_6964_: *mut LeanObject,
    mut v_x_6965_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6966_: *mut LeanObject = core::ptr::null_mut();
    v_res_6966_ = l_Lean_Json_opt___at___00IO_FS_Stream_writeMessage_spec__1(v_k_6964_, v_x_6965_);
    lean_dec(v_x_6965_);
    return v_res_6966_;
}
pub unsafe fn l_IO_FS_Stream_writeMessage(
    mut v_h_6967_: *mut LeanObject,
    mut v_m_6968_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_6976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_method_6977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_x3f_6978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_6992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6995_: u8 = 0;
    let mut v___x_6997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6999_: u8 = 0;
    let mut v_n_7000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7003_: u8 = 0;
    let mut v___x_7005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7007_: u8 = 0;
    let mut v___x_7008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_method_7009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_x3f_7010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7013_: u8 = 0;
    let mut v___x_7014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7022_: u8 = 0;
    let mut v_id_7023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_result_7024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7027_: u8 = 0;
    let mut v___x_7028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_7039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7042_: u8 = 0;
    let mut v___x_7044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7046_: u8 = 0;
    let mut v_n_7047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7050_: u8 = 0;
    let mut v___x_7052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7054_: u8 = 0;
    let mut v___x_7055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7056_: u8 = 0;
    let mut v_id_7057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_7058_: u8 = 0;
    let mut v_message_7059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_x3f_7060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_7098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7101_: u8 = 0;
    let mut v___x_7103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7105_: u8 = 0;
    let mut v_n_7106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7109_: u8 = 0;
    let mut v___x_7111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7113_: u8 = 0;
    let mut v___x_7114_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6970_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3;
                match lean_obj_tag(v_m_6968_) {
                    0 => {
                        v_id_6976_ = lean_ctor_get(v_m_6968_, 0);
                        lean_inc(v_id_6976_);
                        v_method_6977_ = lean_ctor_get(v_m_6968_, 1);
                        lean_inc_ref(v_method_6977_);
                        v_params_x3f_6978_ = lean_ctor_get(v_m_6968_, 2);
                        lean_inc(v_params_x3f_6978_);
                        lean_dec_ref_known(v_m_6968_, 3);
                        v___x_6979_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4;
                        match lean_obj_tag(v_id_6976_) {
                            0 => {
                                v_s_6992_ = lean_ctor_get(v_id_6976_, 0);
                                v_isSharedCheck_6999_ = (!lean_is_exclusive(v_id_6976_)) as u8;
                                if v_isSharedCheck_6999_ == 0 {
                                    v___x_6994_ = v_id_6976_;
                                    v_isShared_6995_ = v_isSharedCheck_6999_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_inc(v_s_6992_);
                                    lean_dec(v_id_6976_);
                                    v___x_6994_ = lean_box(0);
                                    v_isShared_6995_ = v_isSharedCheck_6999_;
                                    state = 3;
                                    continue;
                                }
                            }
                            1 => {
                                v_n_7000_ = lean_ctor_get(v_id_6976_, 0);
                                v_isSharedCheck_7007_ = (!lean_is_exclusive(v_id_6976_)) as u8;
                                if v_isSharedCheck_7007_ == 0 {
                                    v___x_7002_ = v_id_6976_;
                                    v_isShared_7003_ = v_isSharedCheck_7007_;
                                    state = 5;
                                    continue;
                                } else {
                                    lean_inc(v_n_7000_);
                                    lean_dec(v_id_6976_);
                                    v___x_7002_ = lean_box(0);
                                    v_isShared_7003_ = v_isSharedCheck_7007_;
                                    state = 5;
                                    continue;
                                }
                            }
                            _ => {
                                v___x_7008_ = lean_box(0);
                                v___y_6981_ = v___x_7008_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                    1 => {
                        v_method_7009_ = lean_ctor_get(v_m_6968_, 0);
                        v_params_x3f_7010_ = lean_ctor_get(v_m_6968_, 1);
                        v_isSharedCheck_7022_ = (!lean_is_exclusive(v_m_6968_)) as u8;
                        if v_isSharedCheck_7022_ == 0 {
                            v___x_7012_ = v_m_6968_;
                            v_isShared_7013_ = v_isSharedCheck_7022_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_params_x3f_7010_);
                            lean_inc(v_method_7009_);
                            lean_dec(v_m_6968_);
                            v___x_7012_ = lean_box(0);
                            v_isShared_7013_ = v_isSharedCheck_7022_;
                            state = 7;
                            continue;
                        }
                    }
                    2 => {
                        v_id_7023_ = lean_ctor_get(v_m_6968_, 0);
                        v_result_7024_ = lean_ctor_get(v_m_6968_, 1);
                        v_isSharedCheck_7056_ = (!lean_is_exclusive(v_m_6968_)) as u8;
                        if v_isSharedCheck_7056_ == 0 {
                            v___x_7026_ = v_m_6968_;
                            v_isShared_7027_ = v_isSharedCheck_7056_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_result_7024_);
                            lean_inc(v_id_7023_);
                            lean_dec(v_m_6968_);
                            v___x_7026_ = lean_box(0);
                            v_isShared_7027_ = v_isSharedCheck_7056_;
                            state = 9;
                            continue;
                        }
                    }
                    _ => {
                        v_id_7057_ = lean_ctor_get(v_m_6968_, 0);
                        lean_inc(v_id_7057_);
                        v_code_7058_ = lean_ctor_get_uint8(
                            v_m_6968_,
                            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        );
                        v_message_7059_ = lean_ctor_get(v_m_6968_, 1);
                        lean_inc_ref(v_message_7059_);
                        v_data_x3f_7060_ = lean_ctor_get(v_m_6968_, 2);
                        lean_inc(v_data_x3f_7060_);
                        lean_dec_ref_known(v_m_6968_, 3);
                        v___x_7080_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4;
                        match lean_obj_tag(v_id_7057_) {
                            0 => {
                                v_s_7098_ = lean_ctor_get(v_id_7057_, 0);
                                v_isSharedCheck_7105_ = (!lean_is_exclusive(v_id_7057_)) as u8;
                                if v_isSharedCheck_7105_ == 0 {
                                    v___x_7100_ = v_id_7057_;
                                    v_isShared_7101_ = v_isSharedCheck_7105_;
                                    state = 18;
                                    continue;
                                } else {
                                    lean_inc(v_s_7098_);
                                    lean_dec(v_id_7057_);
                                    v___x_7100_ = lean_box(0);
                                    v_isShared_7101_ = v_isSharedCheck_7105_;
                                    state = 18;
                                    continue;
                                }
                            }
                            1 => {
                                v_n_7106_ = lean_ctor_get(v_id_7057_, 0);
                                v_isSharedCheck_7113_ = (!lean_is_exclusive(v_id_7057_)) as u8;
                                if v_isSharedCheck_7113_ == 0 {
                                    v___x_7108_ = v_id_7057_;
                                    v_isShared_7109_ = v_isSharedCheck_7113_;
                                    state = 20;
                                    continue;
                                } else {
                                    lean_inc(v_n_7106_);
                                    lean_dec(v_id_7057_);
                                    v___x_7108_ = lean_box(0);
                                    v_isShared_7109_ = v_isSharedCheck_7113_;
                                    state = 20;
                                    continue;
                                }
                            }
                            _ => {
                                v___x_7114_ = lean_box(0);
                                v___y_7082_ = v___x_7114_;
                                state = 17;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_6973_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6973_, 0, v___x_6970_);
                lean_ctor_set(v___x_6973_, 1, v___y_6972_);
                v___x_6974_ = l_Lean_Json_mkObj(v___x_6973_);
                lean_dec_ref_known(v___x_6973_, 2);
                v___x_6975_ = l_IO_FS_Stream_writeJson(v_h_6967_, v___x_6974_);
                return v___x_6975_;
            }
            2 => {
                v___x_6982_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6982_, 0, v___x_6979_);
                lean_ctor_set(v___x_6982_, 1, v___y_6981_);
                v___x_6983_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
                v___x_6984_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_6984_, 0, v_method_6977_);
                v___x_6985_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6985_, 0, v___x_6983_);
                lean_ctor_set(v___x_6985_, 1, v___x_6984_);
                v___x_6986_ = lean_box(0);
                v___x_6987_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6987_, 0, v___x_6985_);
                lean_ctor_set(v___x_6987_, 1, v___x_6986_);
                v___x_6988_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6988_, 0, v___x_6982_);
                lean_ctor_set(v___x_6988_, 1, v___x_6987_);
                v___x_6989_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6;
                v___x_6990_ = l_Lean_Json_opt___at___00IO_FS_Stream_writeMessage_spec__0(
                    v___x_6989_,
                    v_params_x3f_6978_,
                );
                v___x_6991_ = l_List_appendTR___redArg(v___x_6988_, v___x_6990_);
                v___y_6972_ = v___x_6991_;
                state = 1;
                continue;
            }
            3 => {
                if v_isShared_6995_ == 0 {
                    lean_ctor_set_tag(v___x_6994_, 3);
                    v___x_6997_ = v___x_6994_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6998_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6998_, 0, v_s_6992_);
                    v___x_6997_ = v_reuseFailAlloc_6998_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___y_6981_ = v___x_6997_;
                state = 2;
                continue;
            }
            5 => {
                if v_isShared_7003_ == 0 {
                    lean_ctor_set_tag(v___x_7002_, 2);
                    v___x_7005_ = v___x_7002_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7006_ = lean_alloc_ctor(2, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7006_, 0, v_n_7000_);
                    v___x_7005_ = v_reuseFailAlloc_7006_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___y_6981_ = v___x_7005_;
                state = 2;
                continue;
            }
            7 => {
                v___x_7014_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
                v___x_7015_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_7015_, 0, v_method_7009_);
                if v_isShared_7013_ == 0 {
                    lean_ctor_set_tag(v___x_7012_, 0);
                    lean_ctor_set(v___x_7012_, 1, v___x_7015_);
                    lean_ctor_set(v___x_7012_, 0, v___x_7014_);
                    v___x_7017_ = v___x_7012_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_7021_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7021_, 0, v___x_7014_);
                    lean_ctor_set(v_reuseFailAlloc_7021_, 1, v___x_7015_);
                    v___x_7017_ = v_reuseFailAlloc_7021_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_7018_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6;
                v___x_7019_ = l_Lean_Json_opt___at___00IO_FS_Stream_writeMessage_spec__0(
                    v___x_7018_,
                    v_params_x3f_7010_,
                );
                v___x_7020_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_7020_, 0, v___x_7017_);
                lean_ctor_set(v___x_7020_, 1, v___x_7019_);
                v___y_6972_ = v___x_7020_;
                state = 1;
                continue;
            }
            9 => {
                v___x_7028_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4;
                match lean_obj_tag(v_id_7023_) {
                    0 => {
                        v_s_7039_ = lean_ctor_get(v_id_7023_, 0);
                        v_isSharedCheck_7046_ = (!lean_is_exclusive(v_id_7023_)) as u8;
                        if v_isSharedCheck_7046_ == 0 {
                            v___x_7041_ = v_id_7023_;
                            v_isShared_7042_ = v_isSharedCheck_7046_;
                            state = 12;
                            continue;
                        } else {
                            lean_inc(v_s_7039_);
                            lean_dec(v_id_7023_);
                            v___x_7041_ = lean_box(0);
                            v_isShared_7042_ = v_isSharedCheck_7046_;
                            state = 12;
                            continue;
                        }
                    }
                    1 => {
                        v_n_7047_ = lean_ctor_get(v_id_7023_, 0);
                        v_isSharedCheck_7054_ = (!lean_is_exclusive(v_id_7023_)) as u8;
                        if v_isSharedCheck_7054_ == 0 {
                            v___x_7049_ = v_id_7023_;
                            v_isShared_7050_ = v_isSharedCheck_7054_;
                            state = 14;
                            continue;
                        } else {
                            lean_inc(v_n_7047_);
                            lean_dec(v_id_7023_);
                            v___x_7049_ = lean_box(0);
                            v_isShared_7050_ = v_isSharedCheck_7054_;
                            state = 14;
                            continue;
                        }
                    }
                    _ => {
                        v___x_7055_ = lean_box(0);
                        v___y_7030_ = v___x_7055_;
                        state = 10;
                        continue;
                    }
                }
            }
            10 => {
                if v_isShared_7027_ == 0 {
                    lean_ctor_set_tag(v___x_7026_, 0);
                    lean_ctor_set(v___x_7026_, 1, v___y_7030_);
                    lean_ctor_set(v___x_7026_, 0, v___x_7028_);
                    v___x_7032_ = v___x_7026_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_7038_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7038_, 0, v___x_7028_);
                    lean_ctor_set(v_reuseFailAlloc_7038_, 1, v___y_7030_);
                    v___x_7032_ = v_reuseFailAlloc_7038_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_7033_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7;
                v___x_7034_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_7034_, 0, v___x_7033_);
                lean_ctor_set(v___x_7034_, 1, v_result_7024_);
                v___x_7035_ = lean_box(0);
                v___x_7036_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_7036_, 0, v___x_7034_);
                lean_ctor_set(v___x_7036_, 1, v___x_7035_);
                v___x_7037_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_7037_, 0, v___x_7032_);
                lean_ctor_set(v___x_7037_, 1, v___x_7036_);
                v___y_6972_ = v___x_7037_;
                state = 1;
                continue;
            }
            12 => {
                if v_isShared_7042_ == 0 {
                    lean_ctor_set_tag(v___x_7041_, 3);
                    v___x_7044_ = v___x_7041_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_7045_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7045_, 0, v_s_7039_);
                    v___x_7044_ = v_reuseFailAlloc_7045_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___y_7030_ = v___x_7044_;
                state = 10;
                continue;
            }
            14 => {
                if v_isShared_7050_ == 0 {
                    lean_ctor_set_tag(v___x_7049_, 2);
                    v___x_7052_ = v___x_7049_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_7053_ = lean_alloc_ctor(2, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7053_, 0, v_n_7047_);
                    v___x_7052_ = v_reuseFailAlloc_7053_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___y_7030_ = v___x_7052_;
                state = 10;
                continue;
            }
            16 => {
                lean_inc(v___y_7065_);
                lean_inc_ref(v___y_7064_);
                v___x_7066_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_7066_, 0, v___y_7064_);
                lean_ctor_set(v___x_7066_, 1, v___y_7065_);
                v___x_7067_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8;
                v___x_7068_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_7068_, 0, v_message_7059_);
                v___x_7069_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_7069_, 0, v___x_7067_);
                lean_ctor_set(v___x_7069_, 1, v___x_7068_);
                v___x_7070_ = lean_box(0);
                v___x_7071_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_7071_, 0, v___x_7069_);
                lean_ctor_set(v___x_7071_, 1, v___x_7070_);
                v___x_7072_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_7072_, 0, v___x_7066_);
                lean_ctor_set(v___x_7072_, 1, v___x_7071_);
                v___x_7073_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9;
                v___x_7074_ = l_Lean_Json_opt___at___00IO_FS_Stream_writeMessage_spec__1(
                    v___x_7073_,
                    v_data_x3f_7060_,
                );
                lean_dec(v_data_x3f_7060_);
                v___x_7075_ = l_List_appendTR___redArg(v___x_7072_, v___x_7074_);
                v___x_7076_ = l_Lean_Json_mkObj(v___x_7075_);
                lean_dec(v___x_7075_);
                lean_inc_ref(v___y_7063_);
                v___x_7077_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_7077_, 0, v___y_7063_);
                lean_ctor_set(v___x_7077_, 1, v___x_7076_);
                v___x_7078_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_7078_, 0, v___x_7077_);
                lean_ctor_set(v___x_7078_, 1, v___x_7070_);
                v___x_7079_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_7079_, 0, v___y_7062_);
                lean_ctor_set(v___x_7079_, 1, v___x_7078_);
                v___y_6972_ = v___x_7079_;
                state = 1;
                continue;
            }
            17 => {
                v___x_7083_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_7083_, 0, v___x_7080_);
                lean_ctor_set(v___x_7083_, 1, v___y_7082_);
                v___x_7084_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10;
                v___x_7085_ = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11;
                match v_code_7058_ {
                    0 => {
                        v___x_7086_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1_once
                            ),
                            _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1,
                        );
                        v___y_7062_ = v___x_7083_;
                        v___y_7063_ = v___x_7084_;
                        v___y_7064_ = v___x_7085_;
                        v___y_7065_ = v___x_7086_;
                        state = 16;
                        continue;
                    }
                    1 => {
                        v___x_7087_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3_once
                            ),
                            _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3,
                        );
                        v___y_7062_ = v___x_7083_;
                        v___y_7063_ = v___x_7084_;
                        v___y_7064_ = v___x_7085_;
                        v___y_7065_ = v___x_7087_;
                        state = 16;
                        continue;
                    }
                    2 => {
                        v___x_7088_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5_once
                            ),
                            _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5,
                        );
                        v___y_7062_ = v___x_7083_;
                        v___y_7063_ = v___x_7084_;
                        v___y_7064_ = v___x_7085_;
                        v___y_7065_ = v___x_7088_;
                        state = 16;
                        continue;
                    }
                    3 => {
                        v___x_7089_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7_once
                            ),
                            _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7,
                        );
                        v___y_7062_ = v___x_7083_;
                        v___y_7063_ = v___x_7084_;
                        v___y_7064_ = v___x_7085_;
                        v___y_7065_ = v___x_7089_;
                        state = 16;
                        continue;
                    }
                    4 => {
                        v___x_7090_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9_once
                            ),
                            _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9,
                        );
                        v___y_7062_ = v___x_7083_;
                        v___y_7063_ = v___x_7084_;
                        v___y_7064_ = v___x_7085_;
                        v___y_7065_ = v___x_7090_;
                        state = 16;
                        continue;
                    }
                    5 => {
                        v___x_7091_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11_once
                            ),
                            _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11,
                        );
                        v___y_7062_ = v___x_7083_;
                        v___y_7063_ = v___x_7084_;
                        v___y_7064_ = v___x_7085_;
                        v___y_7065_ = v___x_7091_;
                        state = 16;
                        continue;
                    }
                    6 => {
                        v___x_7092_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13_once
                            ),
                            _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13,
                        );
                        v___y_7062_ = v___x_7083_;
                        v___y_7063_ = v___x_7084_;
                        v___y_7064_ = v___x_7085_;
                        v___y_7065_ = v___x_7092_;
                        state = 16;
                        continue;
                    }
                    7 => {
                        v___x_7093_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15_once
                            ),
                            _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15,
                        );
                        v___y_7062_ = v___x_7083_;
                        v___y_7063_ = v___x_7084_;
                        v___y_7064_ = v___x_7085_;
                        v___y_7065_ = v___x_7093_;
                        state = 16;
                        continue;
                    }
                    8 => {
                        v___x_7094_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17_once
                            ),
                            _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17,
                        );
                        v___y_7062_ = v___x_7083_;
                        v___y_7063_ = v___x_7084_;
                        v___y_7064_ = v___x_7085_;
                        v___y_7065_ = v___x_7094_;
                        state = 16;
                        continue;
                    }
                    9 => {
                        v___x_7095_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19_once
                            ),
                            _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19,
                        );
                        v___y_7062_ = v___x_7083_;
                        v___y_7063_ = v___x_7084_;
                        v___y_7064_ = v___x_7085_;
                        v___y_7065_ = v___x_7095_;
                        state = 16;
                        continue;
                    }
                    10 => {
                        v___x_7096_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21_once
                            ),
                            _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21,
                        );
                        v___y_7062_ = v___x_7083_;
                        v___y_7063_ = v___x_7084_;
                        v___y_7064_ = v___x_7085_;
                        v___y_7065_ = v___x_7096_;
                        state = 16;
                        continue;
                    }
                    _ => {
                        v___x_7097_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23_once
                            ),
                            _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23,
                        );
                        v___y_7062_ = v___x_7083_;
                        v___y_7063_ = v___x_7084_;
                        v___y_7064_ = v___x_7085_;
                        v___y_7065_ = v___x_7097_;
                        state = 16;
                        continue;
                    }
                }
            }
            18 => {
                if v_isShared_7101_ == 0 {
                    lean_ctor_set_tag(v___x_7100_, 3);
                    v___x_7103_ = v___x_7100_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_7104_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7104_, 0, v_s_7098_);
                    v___x_7103_ = v_reuseFailAlloc_7104_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                v___y_7082_ = v___x_7103_;
                state = 17;
                continue;
            }
            20 => {
                if v_isShared_7109_ == 0 {
                    lean_ctor_set_tag(v___x_7108_, 2);
                    v___x_7111_ = v___x_7108_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_7112_ = lean_alloc_ctor(2, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7112_, 0, v_n_7106_);
                    v___x_7111_ = v_reuseFailAlloc_7112_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v___y_7082_ = v___x_7111_;
                state = 17;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_FS_Stream_writeMessage___boxed(
    mut v_h_7115_: *mut LeanObject,
    mut v_m_7116_: *mut LeanObject,
    mut v_a_7117_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7118_: *mut LeanObject = core::ptr::null_mut();
    v_res_7118_ = l_IO_FS_Stream_writeMessage(v_h_7115_, v_m_7116_);
    return v_res_7118_;
}
pub unsafe fn l_IO_FS_Stream_writeRequest___redArg(
    mut v_inst_7119_: *mut LeanObject,
    mut v_h_7120_: *mut LeanObject,
    mut v_r_7121_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_id_7123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_method_7124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_param_7125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7128_: u8 = 0;
    let mut v___y_7130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7140_: u8 = 0;
    let mut v___x_7142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7144_: u8 = 0;
    let mut v_isSharedCheck_7145_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_7123_ = lean_ctor_get(v_r_7121_, 0);
                v_method_7124_ = lean_ctor_get(v_r_7121_, 1);
                v_param_7125_ = lean_ctor_get(v_r_7121_, 2);
                v_isSharedCheck_7145_ = (!lean_is_exclusive(v_r_7121_)) as u8;
                if v_isSharedCheck_7145_ == 0 {
                    v___x_7127_ = v_r_7121_;
                    v_isShared_7128_ = v_isSharedCheck_7145_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_param_7125_);
                    lean_inc(v_method_7124_);
                    lean_inc(v_id_7123_);
                    lean_dec(v_r_7121_);
                    v___x_7127_ = lean_box(0);
                    v_isShared_7128_ = v_isSharedCheck_7145_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7135_ = l_Lean_Json_toStructured_x3f___redArg(v_inst_7119_, v_param_7125_);
                if lean_obj_tag(v___x_7135_) == 0 {
                    lean_dec_ref_known(v___x_7135_, 1);
                    v___x_7136_ = lean_box(0);
                    v___y_7130_ = v___x_7136_;
                    state = 2;
                    continue;
                } else {
                    v_a_7137_ = lean_ctor_get(v___x_7135_, 0);
                    v_isSharedCheck_7144_ = (!lean_is_exclusive(v___x_7135_)) as u8;
                    if v_isSharedCheck_7144_ == 0 {
                        v___x_7139_ = v___x_7135_;
                        v_isShared_7140_ = v_isSharedCheck_7144_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_7137_);
                        lean_dec(v___x_7135_);
                        v___x_7139_ = lean_box(0);
                        v_isShared_7140_ = v_isSharedCheck_7144_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_7128_ == 0 {
                    lean_ctor_set(v___x_7127_, 2, v___y_7130_);
                    v___x_7132_ = v___x_7127_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7134_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7134_, 0, v_id_7123_);
                    lean_ctor_set(v_reuseFailAlloc_7134_, 1, v_method_7124_);
                    lean_ctor_set(v_reuseFailAlloc_7134_, 2, v___y_7130_);
                    v___x_7132_ = v_reuseFailAlloc_7134_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7133_ = l_IO_FS_Stream_writeMessage(v_h_7120_, v___x_7132_);
                return v___x_7133_;
            }
            4 => {
                if v_isShared_7140_ == 0 {
                    v___x_7142_ = v___x_7139_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7143_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7143_, 0, v_a_7137_);
                    v___x_7142_ = v_reuseFailAlloc_7143_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_7130_ = v___x_7142_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_FS_Stream_writeRequest___redArg___boxed(
    mut v_inst_7146_: *mut LeanObject,
    mut v_h_7147_: *mut LeanObject,
    mut v_r_7148_: *mut LeanObject,
    mut v_a_7149_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7150_: *mut LeanObject = core::ptr::null_mut();
    v_res_7150_ = l_IO_FS_Stream_writeRequest___redArg(v_inst_7146_, v_h_7147_, v_r_7148_);
    return v_res_7150_;
}
pub unsafe fn l_IO_FS_Stream_writeRequest(
    mut v_00_u03b1_7151_: *mut LeanObject,
    mut v_inst_7152_: *mut LeanObject,
    mut v_h_7153_: *mut LeanObject,
    mut v_r_7154_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7156_: *mut LeanObject = core::ptr::null_mut();
    v___x_7156_ = l_IO_FS_Stream_writeRequest___redArg(v_inst_7152_, v_h_7153_, v_r_7154_);
    return v___x_7156_;
}
pub unsafe fn l_IO_FS_Stream_writeRequest___boxed(
    mut v_00_u03b1_7157_: *mut LeanObject,
    mut v_inst_7158_: *mut LeanObject,
    mut v_h_7159_: *mut LeanObject,
    mut v_r_7160_: *mut LeanObject,
    mut v_a_7161_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7162_: *mut LeanObject = core::ptr::null_mut();
    v_res_7162_ = l_IO_FS_Stream_writeRequest(v_00_u03b1_7157_, v_inst_7158_, v_h_7159_, v_r_7160_);
    return v_res_7162_;
}
pub unsafe fn l_IO_FS_Stream_writeNotification___redArg(
    mut v_inst_7163_: *mut LeanObject,
    mut v_h_7164_: *mut LeanObject,
    mut v_n_7165_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_method_7167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_param_7168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7171_: u8 = 0;
    let mut v___y_7173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7183_: u8 = 0;
    let mut v___x_7185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7187_: u8 = 0;
    let mut v_isSharedCheck_7188_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_method_7167_ = lean_ctor_get(v_n_7165_, 0);
                v_param_7168_ = lean_ctor_get(v_n_7165_, 1);
                v_isSharedCheck_7188_ = (!lean_is_exclusive(v_n_7165_)) as u8;
                if v_isSharedCheck_7188_ == 0 {
                    v___x_7170_ = v_n_7165_;
                    v_isShared_7171_ = v_isSharedCheck_7188_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_param_7168_);
                    lean_inc(v_method_7167_);
                    lean_dec(v_n_7165_);
                    v___x_7170_ = lean_box(0);
                    v_isShared_7171_ = v_isSharedCheck_7188_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7178_ = l_Lean_Json_toStructured_x3f___redArg(v_inst_7163_, v_param_7168_);
                if lean_obj_tag(v___x_7178_) == 0 {
                    lean_dec_ref_known(v___x_7178_, 1);
                    v___x_7179_ = lean_box(0);
                    v___y_7173_ = v___x_7179_;
                    state = 2;
                    continue;
                } else {
                    v_a_7180_ = lean_ctor_get(v___x_7178_, 0);
                    v_isSharedCheck_7187_ = (!lean_is_exclusive(v___x_7178_)) as u8;
                    if v_isSharedCheck_7187_ == 0 {
                        v___x_7182_ = v___x_7178_;
                        v_isShared_7183_ = v_isSharedCheck_7187_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_7180_);
                        lean_dec(v___x_7178_);
                        v___x_7182_ = lean_box(0);
                        v_isShared_7183_ = v_isSharedCheck_7187_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_7171_ == 0 {
                    lean_ctor_set_tag(v___x_7170_, 1);
                    lean_ctor_set(v___x_7170_, 1, v___y_7173_);
                    v___x_7175_ = v___x_7170_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7177_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7177_, 0, v_method_7167_);
                    lean_ctor_set(v_reuseFailAlloc_7177_, 1, v___y_7173_);
                    v___x_7175_ = v_reuseFailAlloc_7177_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7176_ = l_IO_FS_Stream_writeMessage(v_h_7164_, v___x_7175_);
                return v___x_7176_;
            }
            4 => {
                if v_isShared_7183_ == 0 {
                    v___x_7185_ = v___x_7182_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7186_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7186_, 0, v_a_7180_);
                    v___x_7185_ = v_reuseFailAlloc_7186_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_7173_ = v___x_7185_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_FS_Stream_writeNotification___redArg___boxed(
    mut v_inst_7189_: *mut LeanObject,
    mut v_h_7190_: *mut LeanObject,
    mut v_n_7191_: *mut LeanObject,
    mut v_a_7192_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7193_: *mut LeanObject = core::ptr::null_mut();
    v_res_7193_ = l_IO_FS_Stream_writeNotification___redArg(v_inst_7189_, v_h_7190_, v_n_7191_);
    return v_res_7193_;
}
pub unsafe fn l_IO_FS_Stream_writeNotification(
    mut v_00_u03b1_7194_: *mut LeanObject,
    mut v_inst_7195_: *mut LeanObject,
    mut v_h_7196_: *mut LeanObject,
    mut v_n_7197_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7199_: *mut LeanObject = core::ptr::null_mut();
    v___x_7199_ = l_IO_FS_Stream_writeNotification___redArg(v_inst_7195_, v_h_7196_, v_n_7197_);
    return v___x_7199_;
}
pub unsafe fn l_IO_FS_Stream_writeNotification___boxed(
    mut v_00_u03b1_7200_: *mut LeanObject,
    mut v_inst_7201_: *mut LeanObject,
    mut v_h_7202_: *mut LeanObject,
    mut v_n_7203_: *mut LeanObject,
    mut v_a_7204_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7205_: *mut LeanObject = core::ptr::null_mut();
    v_res_7205_ =
        l_IO_FS_Stream_writeNotification(v_00_u03b1_7200_, v_inst_7201_, v_h_7202_, v_n_7203_);
    return v_res_7205_;
}
pub unsafe fn l_IO_FS_Stream_writeResponse___redArg(
    mut v_inst_7206_: *mut LeanObject,
    mut v_h_7207_: *mut LeanObject,
    mut v_r_7208_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_id_7210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_result_7211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7214_: u8 = 0;
    let mut v___x_7215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7220_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_7210_ = lean_ctor_get(v_r_7208_, 0);
                v_result_7211_ = lean_ctor_get(v_r_7208_, 1);
                v_isSharedCheck_7220_ = (!lean_is_exclusive(v_r_7208_)) as u8;
                if v_isSharedCheck_7220_ == 0 {
                    v___x_7213_ = v_r_7208_;
                    v_isShared_7214_ = v_isSharedCheck_7220_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_result_7211_);
                    lean_inc(v_id_7210_);
                    lean_dec(v_r_7208_);
                    v___x_7213_ = lean_box(0);
                    v_isShared_7214_ = v_isSharedCheck_7220_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7215_ = lean_apply_1(v_inst_7206_, v_result_7211_);
                if v_isShared_7214_ == 0 {
                    lean_ctor_set_tag(v___x_7213_, 2);
                    lean_ctor_set(v___x_7213_, 1, v___x_7215_);
                    v___x_7217_ = v___x_7213_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7219_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7219_, 0, v_id_7210_);
                    lean_ctor_set(v_reuseFailAlloc_7219_, 1, v___x_7215_);
                    v___x_7217_ = v_reuseFailAlloc_7219_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7218_ = l_IO_FS_Stream_writeMessage(v_h_7207_, v___x_7217_);
                return v___x_7218_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_FS_Stream_writeResponse___redArg___boxed(
    mut v_inst_7221_: *mut LeanObject,
    mut v_h_7222_: *mut LeanObject,
    mut v_r_7223_: *mut LeanObject,
    mut v_a_7224_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7225_: *mut LeanObject = core::ptr::null_mut();
    v_res_7225_ = l_IO_FS_Stream_writeResponse___redArg(v_inst_7221_, v_h_7222_, v_r_7223_);
    return v_res_7225_;
}
pub unsafe fn l_IO_FS_Stream_writeResponse(
    mut v_00_u03b1_7226_: *mut LeanObject,
    mut v_inst_7227_: *mut LeanObject,
    mut v_h_7228_: *mut LeanObject,
    mut v_r_7229_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7231_: *mut LeanObject = core::ptr::null_mut();
    v___x_7231_ = l_IO_FS_Stream_writeResponse___redArg(v_inst_7227_, v_h_7228_, v_r_7229_);
    return v___x_7231_;
}
pub unsafe fn l_IO_FS_Stream_writeResponse___boxed(
    mut v_00_u03b1_7232_: *mut LeanObject,
    mut v_inst_7233_: *mut LeanObject,
    mut v_h_7234_: *mut LeanObject,
    mut v_r_7235_: *mut LeanObject,
    mut v_a_7236_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7237_: *mut LeanObject = core::ptr::null_mut();
    v_res_7237_ =
        l_IO_FS_Stream_writeResponse(v_00_u03b1_7232_, v_inst_7233_, v_h_7234_, v_r_7235_);
    return v_res_7237_;
}
pub unsafe fn l_IO_FS_Stream_writeResponseError(
    mut v_h_7238_: *mut LeanObject,
    mut v_e_7239_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_id_7241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_7242_: u8 = 0;
    let mut v_message_7243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7246_: u8 = 0;
    let mut v___x_7247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7252_: u8 = 0;
    let mut v_unused_7253_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_7241_ = lean_ctor_get(v_e_7239_, 0);
                v_code_7242_ = lean_ctor_get_uint8(
                    v_e_7239_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_message_7243_ = lean_ctor_get(v_e_7239_, 1);
                v_isSharedCheck_7252_ = (!lean_is_exclusive(v_e_7239_)) as u8;
                if v_isSharedCheck_7252_ == 0 {
                    v_unused_7253_ = lean_ctor_get(v_e_7239_, 2);
                    lean_dec(v_unused_7253_);
                    v___x_7245_ = v_e_7239_;
                    v_isShared_7246_ = v_isSharedCheck_7252_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_message_7243_);
                    lean_inc(v_id_7241_);
                    lean_dec(v_e_7239_);
                    v___x_7245_ = lean_box(0);
                    v_isShared_7246_ = v_isSharedCheck_7252_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7247_ = lean_box(0);
                if v_isShared_7246_ == 0 {
                    lean_ctor_set_tag(v___x_7245_, 3);
                    lean_ctor_set(v___x_7245_, 2, v___x_7247_);
                    v___x_7249_ = v___x_7245_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7251_ = lean_alloc_ctor(3, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7251_, 0, v_id_7241_);
                    lean_ctor_set(v_reuseFailAlloc_7251_, 1, v_message_7243_);
                    lean_ctor_set(v_reuseFailAlloc_7251_, 2, v___x_7247_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_7251_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_code_7242_,
                    );
                    v___x_7249_ = v_reuseFailAlloc_7251_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7250_ = l_IO_FS_Stream_writeMessage(v_h_7238_, v___x_7249_);
                return v___x_7250_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_FS_Stream_writeResponseError___boxed(
    mut v_h_7254_: *mut LeanObject,
    mut v_e_7255_: *mut LeanObject,
    mut v_a_7256_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7257_: *mut LeanObject = core::ptr::null_mut();
    v_res_7257_ = l_IO_FS_Stream_writeResponseError(v_h_7254_, v_e_7255_);
    return v_res_7257_;
}
pub unsafe fn l_IO_FS_Stream_writeResponseErrorWithData___redArg(
    mut v_inst_7258_: *mut LeanObject,
    mut v_h_7259_: *mut LeanObject,
    mut v_e_7260_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_id_7262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_7263_: u8 = 0;
    let mut v_message_7264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_x3f_7265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7268_: u8 = 0;
    let mut v___y_7270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7279_: u8 = 0;
    let mut v___x_7280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7284_: u8 = 0;
    let mut v_isSharedCheck_7285_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_7262_ = lean_ctor_get(v_e_7260_, 0);
                v_code_7263_ = lean_ctor_get_uint8(
                    v_e_7260_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_message_7264_ = lean_ctor_get(v_e_7260_, 1);
                v_data_x3f_7265_ = lean_ctor_get(v_e_7260_, 2);
                v_isSharedCheck_7285_ = (!lean_is_exclusive(v_e_7260_)) as u8;
                if v_isSharedCheck_7285_ == 0 {
                    v___x_7267_ = v_e_7260_;
                    v_isShared_7268_ = v_isSharedCheck_7285_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_data_x3f_7265_);
                    lean_inc(v_message_7264_);
                    lean_inc(v_id_7262_);
                    lean_dec(v_e_7260_);
                    v___x_7267_ = lean_box(0);
                    v_isShared_7268_ = v_isSharedCheck_7285_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if lean_obj_tag(v_data_x3f_7265_) == 0 {
                    lean_dec_ref(v_inst_7258_);
                    v___x_7275_ = lean_box(0);
                    v___y_7270_ = v___x_7275_;
                    state = 2;
                    continue;
                } else {
                    v_val_7276_ = lean_ctor_get(v_data_x3f_7265_, 0);
                    v_isSharedCheck_7284_ = (!lean_is_exclusive(v_data_x3f_7265_)) as u8;
                    if v_isSharedCheck_7284_ == 0 {
                        v___x_7278_ = v_data_x3f_7265_;
                        v_isShared_7279_ = v_isSharedCheck_7284_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_val_7276_);
                        lean_dec(v_data_x3f_7265_);
                        v___x_7278_ = lean_box(0);
                        v_isShared_7279_ = v_isSharedCheck_7284_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_7268_ == 0 {
                    lean_ctor_set_tag(v___x_7267_, 3);
                    lean_ctor_set(v___x_7267_, 2, v___y_7270_);
                    v___x_7272_ = v___x_7267_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7274_ = lean_alloc_ctor(3, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7274_, 0, v_id_7262_);
                    lean_ctor_set(v_reuseFailAlloc_7274_, 1, v_message_7264_);
                    lean_ctor_set(v_reuseFailAlloc_7274_, 2, v___y_7270_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_7274_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_code_7263_,
                    );
                    v___x_7272_ = v_reuseFailAlloc_7274_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7273_ = l_IO_FS_Stream_writeMessage(v_h_7259_, v___x_7272_);
                return v___x_7273_;
            }
            4 => {
                v___x_7280_ = lean_apply_1(v_inst_7258_, v_val_7276_);
                if v_isShared_7279_ == 0 {
                    lean_ctor_set(v___x_7278_, 0, v___x_7280_);
                    v___x_7282_ = v___x_7278_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7283_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7283_, 0, v___x_7280_);
                    v___x_7282_ = v_reuseFailAlloc_7283_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_7270_ = v___x_7282_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_FS_Stream_writeResponseErrorWithData___redArg___boxed(
    mut v_inst_7286_: *mut LeanObject,
    mut v_h_7287_: *mut LeanObject,
    mut v_e_7288_: *mut LeanObject,
    mut v_a_7289_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7290_: *mut LeanObject = core::ptr::null_mut();
    v_res_7290_ =
        l_IO_FS_Stream_writeResponseErrorWithData___redArg(v_inst_7286_, v_h_7287_, v_e_7288_);
    return v_res_7290_;
}
pub unsafe fn l_IO_FS_Stream_writeResponseErrorWithData(
    mut v_00_u03b1_7291_: *mut LeanObject,
    mut v_inst_7292_: *mut LeanObject,
    mut v_h_7293_: *mut LeanObject,
    mut v_e_7294_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7296_: *mut LeanObject = core::ptr::null_mut();
    v___x_7296_ =
        l_IO_FS_Stream_writeResponseErrorWithData___redArg(v_inst_7292_, v_h_7293_, v_e_7294_);
    return v___x_7296_;
}
pub unsafe fn l_IO_FS_Stream_writeResponseErrorWithData___boxed(
    mut v_00_u03b1_7297_: *mut LeanObject,
    mut v_inst_7298_: *mut LeanObject,
    mut v_h_7299_: *mut LeanObject,
    mut v_e_7300_: *mut LeanObject,
    mut v_a_7301_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7302_: *mut LeanObject = core::ptr::null_mut();
    v_res_7302_ = l_IO_FS_Stream_writeResponseErrorWithData(
        v_00_u03b1_7297_,
        v_inst_7298_,
        v_h_7299_,
        v_e_7300_,
    );
    return v_res_7302_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_JsonRpc(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_Json_Stream(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Json_FromToJson_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_JsonRpc_instInhabitedErrorCode_default =
        _init_l_Lean_JsonRpc_instInhabitedErrorCode_default();
    l_Lean_JsonRpc_instInhabitedErrorCode = _init_l_Lean_JsonRpc_instInhabitedErrorCode();
    l_Lean_JsonRpc_RequestID_ltProp = _init_l_Lean_JsonRpc_RequestID_ltProp();
    lean_mark_persistent(l_Lean_JsonRpc_RequestID_ltProp);
    l_Lean_JsonRpc_instLTRequestID = _init_l_Lean_JsonRpc_instLTRequestID();
    lean_mark_persistent(l_Lean_JsonRpc_instLTRequestID);
    l_Lean_JsonRpc_instInhabitedMessageDirection_default =
        _init_l_Lean_JsonRpc_instInhabitedMessageDirection_default();
    l_Lean_JsonRpc_instInhabitedMessageDirection =
        _init_l_Lean_JsonRpc_instInhabitedMessageDirection();
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_JsonRpc(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Data_JsonRpc(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_Json_Stream(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Data_Json_FromToJson_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_JsonRpc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Data_JsonRpc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Data_JsonRpc(builtin);
}
