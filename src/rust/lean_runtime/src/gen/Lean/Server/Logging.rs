// Lean compiler output
// Module: Lean.Server.Logging
// Imports: Std.Time Lean.Data.Lsp.InitShutdown
use crate::r#gen::Init::Data::Array::Basic::l_List_foldl___at___00Array_appendList_spec__0___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_appendTR___redArg;
use crate::r#gen::Init::Data::Rat::Basic::l_Rat_ofInt;
use crate::r#gen::Init::Data::ToString::Name::{
    l_Lean_Name_toString, l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_num___override, l_Lean_Name_str___override,
};
use crate::r#gen::Init::System::FilePath::l_System_FilePath_join;
use crate::r#gen::Init::System::IO::l_IO_FS_Handle_putStrLn;
use crate::r#gen::Lean::Data::Json::Basic::{
    l_Lean_Json_getObjVal_x3f, l_Lean_Json_getObjValD, l_Lean_Json_getStr_x3f, l_Lean_Json_mkObj,
    l_Lean_JsonNumber_fromInt,
};
use crate::r#gen::Lean::Data::Json::FromToJson::Basic::{
    l_Lean_Json_Structured_fromJson_x3f, l_Lean_Json_Structured_toJson,
};
use crate::r#gen::Lean::Data::Json::Printer::l_Lean_Json_compress;
use crate::r#gen::Lean::Data::JsonRpc::{
    l_Lean_JsonRpc_MessageKind_ofMessage, l_Lean_JsonRpc_instBEqRequestID_beq,
    l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson,
    l_Lean_JsonRpc_instFromJsonMessageKind_fromJson, l_Lean_JsonRpc_instHashableRequestID_hash,
    l_Lean_JsonRpc_instToJsonMessageDirection_toJson, l_Lean_JsonRpc_instToJsonMessageKind_toJson,
};
use crate::r#gen::Lean::Data::Lsp::Extra::l_Lean_Lsp_instFromJsonRpcCallParams_fromJson;
use crate::r#gen::Lean::Data::Lsp::InitShutdown::{
    initialize_Lean_Data_Lsp_InitShutdown, runtime_initialize_Lean_Data_Lsp_InitShutdown,
};
use crate::r#gen::Std::Time::DateTime::PlainDateTime::l_Std_Time_PlainDateTime_ofWallTime;
use crate::r#gen::Std::Time::Duration::l_Std_Time_Duration_ofNanoseconds;
use crate::r#gen::Std::Time::Format::{
    l_Std_Time_ZonedDateTime_format, l_Std_Time_ZonedDateTime_fromISO8601String,
    l_Std_Time_ZonedDateTime_toISO8601String,
};
use crate::r#gen::Std::Time::Zoned::Database::l_Std_Time_Database_defaultGetLocalZoneRules;
use crate::r#gen::Std::Time::Zoned::ZoneRules::{
    l_Std_Time_TimeZone_LocalTimeType_getTimeZone, l_Std_Time_TimeZone_Transition_timezoneAt,
};
use crate::r#gen::Std::Time::{initialize_Std_Time, runtime_initialize_Std_Time};
use crate::lean_imports_rs::Init::Core::lean_mk_thunk;
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_array_uget_borrowed;
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_add, lean_int_dec_eq, lean_int_mul, lean_int_neg, lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_of_nat, lean_usize_sub,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity,
    lean_nat_dec_eq, lean_nat_dec_lt, lean_string_dec_eq, lean_string_hash, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::IO::lean_io_prim_handle_flush;
use crate::lean_imports_rs::Std::Time::DateTime::Timestamp::lean_get_current_time;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_n, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
static mut l_Lean_Server_Logging_LogConfig_ofLspLogConfig___lam__0___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Server_Logging_LogConfig_ofLspLogConfig___lam__0___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_Logging_LogConfig_ofLspLogConfig___lam__0___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Server_Logging_LogConfig_ofLspLogConfig___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Server_Logging_LogConfig_ofLspLogConfig___closed__0_value: LeanStringObject<27> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 27,
        m_capacity: 27,
        m_length: 26,
        m_data: [
            121, 121, 121, 121, 45, 77, 77, 45, 100, 100, 45, 72, 72, 45, 109, 109, 45, 115, 115,
            45, 83, 83, 83, 83, 88, 88, 0,
        ],
    };
static mut l_Lean_Server_Logging_LogConfig_ofLspLogConfig___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_Logging_LogConfig_ofLspLogConfig___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Server_Logging_LogConfig_ofLspLogConfig___closed__1_value: LeanStringObject<5> =
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
        m_data: [76, 83, 80, 95, 0],
    };
static mut l_Lean_Server_Logging_LogConfig_ofLspLogConfig___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_Logging_LogConfig_ofLspLogConfig___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Server_Logging_LogConfig_ofLspLogConfig___closed__2_value: LeanStringObject<5> =
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
        m_data: [46, 108, 111, 103, 0],
    };
static mut l_Lean_Server_Logging_LogConfig_ofLspLogConfig___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_Logging_LogConfig_ofLspLogConfig___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Server_Logging_LogConfig_ofLspLogConfig___closed__3_value: LeanStringObject<2> =
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
static mut l_Lean_Server_Logging_LogConfig_ofLspLogConfig___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_Logging_LogConfig_ofLspLogConfig___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Server_Logging_instInhabitedMessageMethod_default___closed__0_value:
    LeanStringObject<1> = LeanStringObject {
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
static mut l_Lean_Server_Logging_instInhabitedMessageMethod_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_Logging_instInhabitedMessageMethod_default___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Server_Logging_instInhabitedMessageMethod_default___closed__1_value:
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
        l_Lean_Server_Logging_instInhabitedMessageMethod_default___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Lean_Server_Logging_instInhabitedMessageMethod_default___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_Logging_instInhabitedMessageMethod_default___closed__1_value)
        as *mut LeanObject;
pub static mut l_Lean_Server_Logging_instInhabitedMessageMethod_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_Logging_instInhabitedMessageMethod_default___closed__1_value)
        as *mut LeanObject;
pub static mut l_Lean_Server_Logging_instInhabitedMessageMethod: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_Logging_instInhabitedMessageMethod_default___closed__1_value)
        as *mut LeanObject;
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_MessageMethod_all___closed__0_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [36, 47, 108, 101, 97, 110, 47, 114, 112, 99, 47, 99, 97, 108, 108, 0]};
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_MessageMethod_all___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Server_Logging_0__Lean_Server_Logging_MessageMethod_all___closed__0_value
) as *mut LeanObject;
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_MessageMethod_all___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_MessageMethod_all___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonZonedDateTime___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonZonedDateTime___lam__0 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonZonedDateTime___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonZonedDateTime___closed__0_value) as *mut LeanObject;
pub static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonZonedDateTime: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonZonedDateTime___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonZonedDateTime___lam__0___closed__0_value: LeanStringObject<63> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 63, m_capacity: 63, m_length: 62, m_data: [69, 120, 112, 101, 99, 116, 101, 100, 32, 115, 116, 114, 105, 110, 103, 32, 119, 104, 101, 110, 32, 99, 111, 110, 118, 101, 114, 116, 105, 110, 103, 32, 74, 83, 79, 78, 32, 116, 111, 32, 83, 116, 100, 46, 84, 105, 109, 101, 46, 90, 111, 110, 101, 100, 68, 97, 116, 101, 84, 105, 109, 101, 0]};
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonZonedDateTime___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonZonedDateTime___lam__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonZonedDateTime___lam__0___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonZonedDateTime___lam__0___closed__0_value) as *mut LeanObject] };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonZonedDateTime___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonZonedDateTime___lam__0___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonZonedDateTime___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonZonedDateTime___lam__0 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonZonedDateTime___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonZonedDateTime___closed__0_value) as *mut LeanObject;
pub static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonZonedDateTime: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonZonedDateTime___closed__0_value) as *mut LeanObject;
pub static l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__0_value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [101, 120, 112, 101, 99, 116, 101, 100, 32, 101, 114, 114, 111, 114, 32, 99, 111, 100, 101, 0]};
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__0_value) as *mut LeanObject;
pub static l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__0_value) as *mut LeanObject] };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__1_value) as *mut LeanObject;
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__8: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__9: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__10_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__10: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__11: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__12_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__12: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__13: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__14_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__14: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__15_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__15: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__16_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__16: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__17_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__17: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__18_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__18: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__19_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__19: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__20_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__20: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__21_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__21: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__22_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__22: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__23_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__23: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__24_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__24: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__25_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__25: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__26_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 11 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__26: *mut LeanObject = core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__26_value) as *mut LeanObject;
pub static l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__27_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 10 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__27: *mut LeanObject = core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__27_value) as *mut LeanObject;
pub static l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__28_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 9 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__28: *mut LeanObject = core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__28_value) as *mut LeanObject;
pub static l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__29_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 8 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__29: *mut LeanObject = core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__29_value) as *mut LeanObject;
pub static l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__30_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 7 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__30: *mut LeanObject = core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__30_value) as *mut LeanObject;
pub static l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__31_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 6 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__31: *mut LeanObject = core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__31_value) as *mut LeanObject;
pub static l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__32_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 5 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__32: *mut LeanObject = core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__32_value) as *mut LeanObject;
pub static l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__33_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 4 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__33: *mut LeanObject = core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__33_value) as *mut LeanObject;
pub static l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__34_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 3 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__34: *mut LeanObject = core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__34_value) as *mut LeanObject;
pub static l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__35_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 2 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__35: *mut LeanObject = core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__35_value) as *mut LeanObject;
pub static l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__36_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__36: *mut LeanObject = core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__36_value) as *mut LeanObject;
pub static l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__37_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__37: *mut LeanObject = core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__37_value) as *mut LeanObject;
pub static l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__3___closed__0_value: LeanStringObject<46> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 46, m_capacity: 46, m_length: 45, m_data: [97, 32, 114, 101, 113, 117, 101, 115, 116, 32, 105, 100, 32, 110, 101, 101, 100, 115, 32, 116, 111, 32, 98, 101, 32, 97, 32, 110, 117, 109, 98, 101, 114, 32, 111, 114, 32, 97, 32, 115, 116, 114, 105, 110, 103, 0]};
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__3___closed__0_value) as *mut LeanObject;
pub static l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__3___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__3___closed__0_value) as *mut LeanObject] };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__3___closed__1_value) as *mut LeanObject;
pub static l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__0_value: LeanStringObject<42> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 42, m_capacity: 42, m_length: 41, m_data: [111, 110, 108, 121, 32, 118, 101, 114, 115, 105, 111, 110, 32, 50, 46, 48, 32, 111, 102, 32, 74, 83, 79, 78, 32, 82, 80, 67, 32, 105, 115, 32, 115, 117, 112, 112, 111, 114, 116, 101, 100, 0]};
static mut l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__0_value) as *mut LeanObject;
pub static l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__0_value) as *mut LeanObject] };
static mut l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__1_value) as *mut LeanObject;
pub static l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__2_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [106, 115, 111, 110, 114, 112, 99, 0]};
static mut l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__2_value) as *mut LeanObject;
pub static l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__3_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [50, 46, 48, 0]};
static mut l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__3_value) as *mut LeanObject;
pub static l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__4_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [105, 100, 0]};
static mut l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__4_value) as *mut LeanObject;
pub static l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__5_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [101, 114, 114, 111, 114, 0]};
static mut l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__5_value) as *mut LeanObject;
pub static l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__6_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [99, 111, 100, 101, 0]};
static mut l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__6_value) as *mut LeanObject;
pub static l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__7_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [109, 101, 115, 115, 97, 103, 101, 0]};
static mut l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__7_value) as *mut LeanObject;
pub static l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__8_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [100, 97, 116, 97, 0]};
static mut l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__8_value) as *mut LeanObject;
pub static l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__9_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [109, 101, 116, 104, 111, 100, 0]};
static mut l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__9: *mut LeanObject = core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__9_value) as *mut LeanObject;
pub static l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__10_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [114, 101, 115, 117, 108, 116, 0]};
static mut l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__10_value) as *mut LeanObject;
pub static l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__11_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [112, 97, 114, 97, 109, 115, 0]};
static mut l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__11: *mut LeanObject = core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__11_value) as *mut LeanObject;
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 105, 109, 101, 0]};
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__1_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__1_value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__3_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__3_value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__5_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [83, 101, 114, 118, 101, 114, 0]};
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__4_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__5_value) as *mut LeanObject,12337524736695414095 as *mut LeanObject] };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__7_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [76, 111, 103, 103, 105, 110, 103, 0]};
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__7_value) as *mut LeanObject;
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__6_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__7_value) as *mut LeanObject,13795635718385987595 as *mut LeanObject] };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__8_value) as *mut LeanObject;
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__8_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,10771712435572913910 as *mut LeanObject] };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__9_value) as *mut LeanObject;
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__10_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__9_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__3_value) as *mut LeanObject,16696290940608711967 as *mut LeanObject] };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__10_value) as *mut LeanObject;
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__10_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__5_value) as *mut LeanObject,8428733202386381774 as *mut LeanObject] };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__11_value) as *mut LeanObject;
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__12_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__11_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__7_value) as *mut LeanObject,2923788871047101174 as *mut LeanObject] };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__12: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__12_value) as *mut LeanObject;
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__13_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [76, 111, 103, 69, 110, 116, 114, 121, 0]};
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__13_value) as *mut LeanObject;
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__14_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__12_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__13_value) as *mut LeanObject,14170570813020572205 as *mut LeanObject] };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__14: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__14_value) as *mut LeanObject;
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__15_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__15: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__16_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__16: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__17_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__0_value) as *mut LeanObject,5547123645457395768 as *mut LeanObject] };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__17: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__17_value) as *mut LeanObject;
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__18_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__18: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__19_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__19: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__20_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [58, 32, 0]};
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__20: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__20_value) as *mut LeanObject;
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__21_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__21: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__22_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [100, 105, 114, 101, 99, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__22: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__22_value) as *mut LeanObject;
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__23_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__22_value) as *mut LeanObject,12068223408101116769 as *mut LeanObject] };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__23: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__23_value) as *mut LeanObject;
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__24_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__24: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__25_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__25: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__26_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__26: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__27_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [107, 105, 110, 100, 0]};
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__27: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__27_value) as *mut LeanObject;
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__28_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__27_value) as *mut LeanObject,11445860042738416218 as *mut LeanObject] };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__28: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__28_value) as *mut LeanObject;
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__29_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__29: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__30_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__30: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__31_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__31: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__32_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [109, 115, 103, 0]};
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__32: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__32_value) as *mut LeanObject;
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__33_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__32_value) as *mut LeanObject,5921405926628438706 as *mut LeanObject] };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__33: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__33_value) as *mut LeanObject;
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__34_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__34: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__35_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__35: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__36_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__36: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry___closed__0_value) as *mut LeanObject;
pub static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__3_value) as *mut LeanObject] };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__0_value) as *mut LeanObject] };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__2_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__8: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__9: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__10_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__10: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__11: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__12_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__12: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__13: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__14_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__14: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__15_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__15: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__16_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__16: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__17_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__17: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__18_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__18: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__19_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__19: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__20_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__20: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__21_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__21: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__22_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__22: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__23_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__23: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__24_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__24: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__25_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__25: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__26_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__26: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry___closed__0_value
) as *mut LeanObject;
pub static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry___closed__0_value
) as *mut LeanObject;
pub unsafe fn _init_l_Lean_Server_Logging_LogConfig_ofLspLogConfig___lam__0___closed__0()
-> *mut LeanObject {
    let mut v___x_1275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut LeanObject = core::ptr::null_mut();
    v___x_1275_ = lean_unsigned_to_nat(0);
    v___x_1276_ = lean_nat_to_int(v___x_1275_);
    return v___x_1276_;
}
pub unsafe fn _init_l_Lean_Server_Logging_LogConfig_ofLspLogConfig___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_1277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut LeanObject = core::ptr::null_mut();
    v___x_1277_ = lean_unsigned_to_nat(1000000000);
    v___x_1278_ = lean_nat_to_int(v___x_1277_);
    return v___x_1278_;
}
pub unsafe fn l_Lean_Server_Logging_LogConfig_ofLspLogConfig___lam__0(
    mut v___y_1279_: *mut LeanObject,
    mut v_a_1280_: *mut LeanObject,
    mut v_x_1281_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_offset_1282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_1283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_1284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut LeanObject = core::ptr::null_mut();
    v_offset_1282_ = lean_ctor_get(v___y_1279_, 0);
    v_second_1283_ = lean_ctor_get(v_a_1280_, 0);
    v_nano_1284_ = lean_ctor_get(v_a_1280_, 1);
    v___x_1285_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Server_Logging_LogConfig_ofLspLogConfig___lam__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Server_Logging_LogConfig_ofLspLogConfig___lam__0___closed__0_once
        ),
        _init_l_Lean_Server_Logging_LogConfig_ofLspLogConfig___lam__0___closed__0,
    );
    v___x_1286_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Server_Logging_LogConfig_ofLspLogConfig___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Server_Logging_LogConfig_ofLspLogConfig___lam__0___closed__1_once
        ),
        _init_l_Lean_Server_Logging_LogConfig_ofLspLogConfig___lam__0___closed__1,
    );
    v___x_1287_ = lean_int_mul(v_second_1283_, v___x_1286_);
    v___x_1288_ = lean_int_add(v___x_1287_, v_nano_1284_);
    lean_dec(v___x_1287_);
    v___x_1289_ = lean_int_mul(v_offset_1282_, v___x_1286_);
    v___x_1290_ = lean_int_add(v___x_1289_, v___x_1285_);
    lean_dec(v___x_1289_);
    v___x_1291_ = lean_int_add(v___x_1288_, v___x_1290_);
    lean_dec(v___x_1290_);
    lean_dec(v___x_1288_);
    v___x_1292_ = l_Std_Time_Duration_ofNanoseconds(v___x_1291_);
    lean_dec(v___x_1291_);
    v___x_1293_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1292_);
    return v___x_1293_;
}
pub unsafe fn l_Lean_Server_Logging_LogConfig_ofLspLogConfig___lam__0___boxed(
    mut v___y_1294_: *mut LeanObject,
    mut v_a_1295_: *mut LeanObject,
    mut v_x_1296_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1297_: *mut LeanObject = core::ptr::null_mut();
    v_res_1297_ =
        l_Lean_Server_Logging_LogConfig_ofLspLogConfig___lam__0(v___y_1294_, v_a_1295_, v_x_1296_);
    lean_dec_ref(v_a_1295_);
    lean_dec_ref(v___y_1294_);
    return v_res_1297_;
}
pub unsafe fn l_Lean_Server_Logging_LogConfig_ofLspLogConfig(
    mut v_lspCfg_x3f_1302_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1308_: u8 = 0;
    let mut v___x_1309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1313_: u8 = 0;
    let mut v___y_1315_: u8 = 0;
    let mut v_allowedMethods_x3f_1316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_disallowedMethods_x3f_1317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_logDir_x3f_1337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_allowedMethods_x3f_1338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_disallowedMethods_x3f_1339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: u8 = 0;
    let mut v_val_1341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: u8 = 0;
    let mut v___x_1344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initialLocalTimeType_1349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_transitions_1350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1354_: u8 = 0;
    let mut v_a_1355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1358_: u8 = 0;
    let mut v___x_1360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1362_: u8 = 0;
    let mut v_isSharedCheck_1363_: u8 = 0;
    let mut v_a_1364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1367_: u8 = 0;
    let mut v___x_1369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1371_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1304_ = lean_get_current_time();
                if lean_obj_tag(v___x_1304_) == 0 {
                    v_a_1305_ = lean_ctor_get(v___x_1304_, 0);
                    v_isSharedCheck_1363_ = (!lean_is_exclusive(v___x_1304_)) as u8;
                    if v_isSharedCheck_1363_ == 0 {
                        v___x_1307_ = v___x_1304_;
                        v_isShared_1308_ = v_isSharedCheck_1363_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1305_);
                        lean_dec(v___x_1304_);
                        v___x_1307_ = lean_box(0);
                        v_isShared_1308_ = v_isSharedCheck_1363_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_lspCfg_x3f_1302_);
                    v_a_1364_ = lean_ctor_get(v___x_1304_, 0);
                    v_isSharedCheck_1371_ = (!lean_is_exclusive(v___x_1304_)) as u8;
                    if v_isSharedCheck_1371_ == 0 {
                        v___x_1366_ = v___x_1304_;
                        v_isShared_1367_ = v_isSharedCheck_1371_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_1364_);
                        lean_dec(v___x_1304_);
                        v___x_1366_ = lean_box(0);
                        v_isShared_1367_ = v_isSharedCheck_1371_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1309_ = l_Std_Time_Database_defaultGetLocalZoneRules();
                if lean_obj_tag(v___x_1309_) == 0 {
                    v_a_1310_ = lean_ctor_get(v___x_1309_, 0);
                    v_isSharedCheck_1354_ = (!lean_is_exclusive(v___x_1309_)) as u8;
                    if v_isSharedCheck_1354_ == 0 {
                        v___x_1312_ = v___x_1309_;
                        v_isShared_1313_ = v_isSharedCheck_1354_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_1310_);
                        lean_dec(v___x_1309_);
                        v___x_1312_ = lean_box(0);
                        v_isShared_1313_ = v_isSharedCheck_1354_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1307_);
                    lean_dec(v_a_1305_);
                    lean_dec(v_lspCfg_x3f_1302_);
                    v_a_1355_ = lean_ctor_get(v___x_1309_, 0);
                    v_isSharedCheck_1362_ = (!lean_is_exclusive(v___x_1309_)) as u8;
                    if v_isSharedCheck_1362_ == 0 {
                        v___x_1357_ = v___x_1309_;
                        v_isShared_1358_ = v_isSharedCheck_1362_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_1355_);
                        lean_dec(v___x_1309_);
                        v___x_1357_ = lean_box(0);
                        v_isShared_1358_ = v_isSharedCheck_1362_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                v_initialLocalTimeType_1349_ = lean_ctor_get(v_a_1310_, 0);
                v_transitions_1350_ = lean_ctor_get(v_a_1310_, 1);
                v___x_1351_ =
                    l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_1350_, v_a_1305_);
                if lean_obj_tag(v___x_1351_) == 0 {
                    lean_dec_ref_known(v___x_1351_, 1);
                    v___x_1352_ =
                        l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_1349_);
                    v___y_1324_ = v___x_1352_;
                    state = 5;
                    continue;
                } else {
                    v_a_1353_ = lean_ctor_get(v___x_1351_, 0);
                    lean_inc(v_a_1353_);
                    lean_dec_ref_known(v___x_1351_, 1);
                    v___y_1324_ = v_a_1353_;
                    state = 5;
                    continue;
                }
            }
            3 => {
                v___x_1319_ = lean_alloc_ctor(0, 3, (1) as u32);
                lean_ctor_set(v___x_1319_, 0, v___y_1318_);
                lean_ctor_set(v___x_1319_, 1, v_allowedMethods_x3f_1316_);
                lean_ctor_set(v___x_1319_, 2, v_disallowedMethods_x3f_1317_);
                lean_ctor_set_uint8(
                    v___x_1319_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___y_1315_,
                );
                if v_isShared_1313_ == 0 {
                    lean_ctor_set(v___x_1312_, 0, v___x_1319_);
                    v___x_1321_ = v___x_1312_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1322_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1322_, 0, v___x_1319_);
                    v___x_1321_ = v_reuseFailAlloc_1322_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1321_;
            }
            5 => {
                lean_inc(v_a_1305_);
                lean_inc_ref(v___y_1324_);
                v___f_1325_ = lean_alloc_closure(
                    l_Lean_Server_Logging_LogConfig_ofLspLogConfig___lam__0___boxed
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_1325_, 0, v___y_1324_);
                lean_closure_set(v___f_1325_, 1, v_a_1305_);
                v___x_1326_ = lean_mk_thunk(v___f_1325_);
                v___x_1327_ = lean_alloc_ctor(0, 4, (0) as u32);
                lean_ctor_set(v___x_1327_, 0, v___x_1326_);
                lean_ctor_set(v___x_1327_, 1, v_a_1305_);
                lean_ctor_set(v___x_1327_, 2, v_a_1310_);
                lean_ctor_set(v___x_1327_, 3, v___y_1324_);
                v___x_1328_ = l_Lean_Server_Logging_LogConfig_ofLspLogConfig___closed__0;
                v___x_1329_ = l_Std_Time_ZonedDateTime_format(v___x_1327_, v___x_1328_);
                v___x_1330_ = l_Lean_Server_Logging_LogConfig_ofLspLogConfig___closed__1;
                v___x_1331_ = lean_string_append(v___x_1330_, v___x_1329_);
                lean_dec_ref(v___x_1329_);
                v___x_1332_ = l_Lean_Server_Logging_LogConfig_ofLspLogConfig___closed__2;
                v___x_1333_ = lean_string_append(v___x_1331_, v___x_1332_);
                v___x_1334_ = l_Lean_Server_Logging_LogConfig_ofLspLogConfig___closed__3;
                lean_inc_ref(v___x_1333_);
                v___x_1335_ = l_System_FilePath_join(v___x_1334_, v___x_1333_);
                if lean_obj_tag(v_lspCfg_x3f_1302_) == 1 {
                    lean_del_object(v___x_1307_);
                    v_val_1336_ = lean_ctor_get(v_lspCfg_x3f_1302_, 0);
                    lean_inc(v_val_1336_);
                    lean_dec_ref_known(v_lspCfg_x3f_1302_, 1);
                    v_logDir_x3f_1337_ = lean_ctor_get(v_val_1336_, 0);
                    lean_inc(v_logDir_x3f_1337_);
                    v_allowedMethods_x3f_1338_ = lean_ctor_get(v_val_1336_, 1);
                    lean_inc(v_allowedMethods_x3f_1338_);
                    v_disallowedMethods_x3f_1339_ = lean_ctor_get(v_val_1336_, 2);
                    lean_inc(v_disallowedMethods_x3f_1339_);
                    lean_dec(v_val_1336_);
                    v___x_1340_ = 1;
                    if lean_obj_tag(v_logDir_x3f_1337_) == 0 {
                        lean_dec_ref(v___x_1333_);
                        v___y_1315_ = v___x_1340_;
                        v_allowedMethods_x3f_1316_ = v_allowedMethods_x3f_1338_;
                        v_disallowedMethods_x3f_1317_ = v_disallowedMethods_x3f_1339_;
                        v___y_1318_ = v___x_1335_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec_ref(v___x_1335_);
                        v_val_1341_ = lean_ctor_get(v_logDir_x3f_1337_, 0);
                        lean_inc(v_val_1341_);
                        lean_dec_ref_known(v_logDir_x3f_1337_, 1);
                        v___x_1342_ = l_System_FilePath_join(v_val_1341_, v___x_1333_);
                        v___y_1315_ = v___x_1340_;
                        v_allowedMethods_x3f_1316_ = v_allowedMethods_x3f_1338_;
                        v_disallowedMethods_x3f_1317_ = v_disallowedMethods_x3f_1339_;
                        v___y_1318_ = v___x_1342_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_1333_);
                    lean_del_object(v___x_1312_);
                    lean_dec(v_lspCfg_x3f_1302_);
                    v___x_1343_ = 0;
                    v___x_1344_ = lean_box(0);
                    v___x_1345_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v___x_1345_, 0, v___x_1335_);
                    lean_ctor_set(v___x_1345_, 1, v___x_1344_);
                    lean_ctor_set(v___x_1345_, 2, v___x_1344_);
                    lean_ctor_set_uint8(
                        v___x_1345_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v___x_1343_,
                    );
                    if v_isShared_1308_ == 0 {
                        lean_ctor_set(v___x_1307_, 0, v___x_1345_);
                        v___x_1347_ = v___x_1307_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1348_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1348_, 0, v___x_1345_);
                        v___x_1347_ = v_reuseFailAlloc_1348_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_1347_;
            }
            7 => {
                if v_isShared_1358_ == 0 {
                    v___x_1360_ = v___x_1357_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1361_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_a_1355_);
                    v___x_1360_ = v_reuseFailAlloc_1361_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1360_;
            }
            9 => {
                if v_isShared_1367_ == 0 {
                    v___x_1369_ = v___x_1366_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1370_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_a_1364_);
                    v___x_1369_ = v_reuseFailAlloc_1370_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1369_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_Logging_LogConfig_ofLspLogConfig___boxed(
    mut v_lspCfg_x3f_1372_: *mut LeanObject,
    mut v_a_1373_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1374_: *mut LeanObject = core::ptr::null_mut();
    v_res_1374_ = l_Lean_Server_Logging_LogConfig_ofLspLogConfig(v_lspCfg_x3f_1372_);
    return v_res_1374_;
}
pub unsafe fn l_Nat_cast___at___00Nat_cast___at___00Lean_Server_Logging_LogConfig_ofLspLogConfig_spec__0_spec__0(
    mut v_a_1375_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1376_: *mut LeanObject = core::ptr::null_mut();
    v___x_1376_ = lean_nat_to_int(v_a_1375_);
    return v___x_1376_;
}
pub unsafe fn l_Nat_cast___at___00Lean_Server_Logging_LogConfig_ofLspLogConfig_spec__0(
    mut v_a_1377_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut LeanObject = core::ptr::null_mut();
    v___x_1378_ = lean_nat_to_int(v_a_1377_);
    v___x_1379_ = l_Rat_ofInt(v___x_1378_);
    return v___x_1379_;
}
pub unsafe fn l_Lean_Server_Logging_MessageMethod_ctorIdx(
    mut v_x_1380_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_1380_) {
        0 => {
            let mut v___x_1381_: *mut LeanObject = core::ptr::null_mut();
            v___x_1381_ = lean_unsigned_to_nat(0);
            return v___x_1381_;
        }
        1 => {
            let mut v___x_1382_: *mut LeanObject = core::ptr::null_mut();
            v___x_1382_ = lean_unsigned_to_nat(1);
            return v___x_1382_;
        }
        _ => {
            let mut v___x_1383_: *mut LeanObject = core::ptr::null_mut();
            v___x_1383_ = lean_unsigned_to_nat(2);
            return v___x_1383_;
        }
    }
}
pub unsafe fn l_Lean_Server_Logging_MessageMethod_ctorIdx___boxed(
    mut v_x_1384_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1385_: *mut LeanObject = core::ptr::null_mut();
    v_res_1385_ = l_Lean_Server_Logging_MessageMethod_ctorIdx(v_x_1384_);
    lean_dec_ref(v_x_1384_);
    return v_res_1385_;
}
pub unsafe fn l_Lean_Server_Logging_MessageMethod_ctorElim___redArg(
    mut v_t_1386_: *mut LeanObject,
    mut v_k_1387_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_method_1388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut LeanObject = core::ptr::null_mut();
    v_method_1388_ = lean_ctor_get(v_t_1386_, 0);
    lean_inc_ref(v_method_1388_);
    lean_dec_ref(v_t_1386_);
    v___x_1389_ = lean_apply_1(v_k_1387_, v_method_1388_);
    return v___x_1389_;
}
pub unsafe fn l_Lean_Server_Logging_MessageMethod_ctorElim(
    mut v_motive_1390_: *mut LeanObject,
    mut v_ctorIdx_1391_: *mut LeanObject,
    mut v_t_1392_: *mut LeanObject,
    mut v_h_1393_: *mut LeanObject,
    mut v_k_1394_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1395_: *mut LeanObject = core::ptr::null_mut();
    v___x_1395_ = l_Lean_Server_Logging_MessageMethod_ctorElim___redArg(v_t_1392_, v_k_1394_);
    return v___x_1395_;
}
pub unsafe fn l_Lean_Server_Logging_MessageMethod_ctorElim___boxed(
    mut v_motive_1396_: *mut LeanObject,
    mut v_ctorIdx_1397_: *mut LeanObject,
    mut v_t_1398_: *mut LeanObject,
    mut v_h_1399_: *mut LeanObject,
    mut v_k_1400_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1401_: *mut LeanObject = core::ptr::null_mut();
    v_res_1401_ = l_Lean_Server_Logging_MessageMethod_ctorElim(
        v_motive_1396_,
        v_ctorIdx_1397_,
        v_t_1398_,
        v_h_1399_,
        v_k_1400_,
    );
    lean_dec(v_ctorIdx_1397_);
    return v_res_1401_;
}
pub unsafe fn l_Lean_Server_Logging_MessageMethod_request_elim___redArg(
    mut v_t_1402_: *mut LeanObject,
    mut v_request_1403_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1404_: *mut LeanObject = core::ptr::null_mut();
    v___x_1404_ = l_Lean_Server_Logging_MessageMethod_ctorElim___redArg(v_t_1402_, v_request_1403_);
    return v___x_1404_;
}
pub unsafe fn l_Lean_Server_Logging_MessageMethod_request_elim(
    mut v_motive_1405_: *mut LeanObject,
    mut v_t_1406_: *mut LeanObject,
    mut v_h_1407_: *mut LeanObject,
    mut v_request_1408_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1409_: *mut LeanObject = core::ptr::null_mut();
    v___x_1409_ = l_Lean_Server_Logging_MessageMethod_ctorElim___redArg(v_t_1406_, v_request_1408_);
    return v___x_1409_;
}
pub unsafe fn l_Lean_Server_Logging_MessageMethod_rpcRequest_elim___redArg(
    mut v_t_1410_: *mut LeanObject,
    mut v_rpcRequest_1411_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1412_: *mut LeanObject = core::ptr::null_mut();
    v___x_1412_ =
        l_Lean_Server_Logging_MessageMethod_ctorElim___redArg(v_t_1410_, v_rpcRequest_1411_);
    return v___x_1412_;
}
pub unsafe fn l_Lean_Server_Logging_MessageMethod_rpcRequest_elim(
    mut v_motive_1413_: *mut LeanObject,
    mut v_t_1414_: *mut LeanObject,
    mut v_h_1415_: *mut LeanObject,
    mut v_rpcRequest_1416_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1417_: *mut LeanObject = core::ptr::null_mut();
    v___x_1417_ =
        l_Lean_Server_Logging_MessageMethod_ctorElim___redArg(v_t_1414_, v_rpcRequest_1416_);
    return v___x_1417_;
}
pub unsafe fn l_Lean_Server_Logging_MessageMethod_notification_elim___redArg(
    mut v_t_1418_: *mut LeanObject,
    mut v_notification_1419_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1420_: *mut LeanObject = core::ptr::null_mut();
    v___x_1420_ =
        l_Lean_Server_Logging_MessageMethod_ctorElim___redArg(v_t_1418_, v_notification_1419_);
    return v___x_1420_;
}
pub unsafe fn l_Lean_Server_Logging_MessageMethod_notification_elim(
    mut v_motive_1421_: *mut LeanObject,
    mut v_t_1422_: *mut LeanObject,
    mut v_h_1423_: *mut LeanObject,
    mut v_notification_1424_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1425_: *mut LeanObject = core::ptr::null_mut();
    v___x_1425_ =
        l_Lean_Server_Logging_MessageMethod_ctorElim___redArg(v_t_1422_, v_notification_1424_);
    return v___x_1425_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_MessageMethod_all___closed__1()
-> *mut LeanObject {
    let mut v___x_1432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut LeanObject = core::ptr::null_mut();
    v___x_1432_ =
        l___private_Lean_Server_Logging_0__Lean_Server_Logging_MessageMethod_all___closed__0;
    v___x_1433_ = lean_unsigned_to_nat(2);
    v___x_1434_ = lean_mk_empty_array_with_capacity(v___x_1433_);
    v___x_1435_ = lean_array_push(v___x_1434_, v___x_1432_);
    return v___x_1435_;
}
pub unsafe fn l___private_Lean_Server_Logging_0__Lean_Server_Logging_MessageMethod_all(
    mut v_x_1436_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_method_1438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_method_1442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_method_1445_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1436_) == 1 {
                    v_method_1442_ = lean_ctor_get(v_x_1436_, 0);
                    lean_inc_ref(v_method_1442_);
                    lean_dec_ref_known(v_x_1436_, 1);
                    v___x_1443_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_MessageMethod_all___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_MessageMethod_all___closed__1_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_MessageMethod_all___closed__1);
                    v___x_1444_ = lean_array_push(v___x_1443_, v_method_1442_);
                    return v___x_1444_;
                } else {
                    v_method_1445_ = lean_ctor_get(v_x_1436_, 0);
                    lean_inc_ref(v_method_1445_);
                    lean_dec_ref(v_x_1436_);
                    v_method_1438_ = v_method_1445_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1439_ = lean_unsigned_to_nat(1);
                v___x_1440_ = lean_mk_empty_array_with_capacity(v___x_1439_);
                v___x_1441_ = lean_array_push(v___x_1440_, v_method_1438_);
                return v___x_1441_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_toJson___at___00Lean_Server_Logging_messageMethod_x3f_spec__0(
    mut v_x_1446_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1446_) == 0 {
        let mut v___x_1447_: *mut LeanObject = core::ptr::null_mut();
        v___x_1447_ = lean_box(0);
        return v___x_1447_;
    } else {
        let mut v_val_1448_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1449_: *mut LeanObject = core::ptr::null_mut();
        v_val_1448_ = lean_ctor_get(v_x_1446_, 0);
        lean_inc(v_val_1448_);
        lean_dec_ref_known(v_x_1446_, 1);
        v___x_1449_ = l_Lean_Json_Structured_toJson(v_val_1448_);
        return v___x_1449_;
    }
}
pub unsafe fn l_Lean_Server_Logging_messageMethod_x3f(
    mut v_x_1450_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_method_1451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_x3f_1452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: u8 = 0;
    let mut v_params_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1463_: u8 = 0;
    let mut v_method_1464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1470_: u8 = 0;
    let mut v_method_1471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                match lean_obj_tag(v_x_1450_) {
                    0 => {
                        v_method_1451_ = lean_ctor_get(v_x_1450_, 1);
                        lean_inc_ref(v_method_1451_);
                        v_params_x3f_1452_ = lean_ctor_get(v_x_1450_, 2);
                        lean_inc(v_params_x3f_1452_);
                        lean_dec_ref_known(v_x_1450_, 3);
                        v___x_1456_ = l___private_Lean_Server_Logging_0__Lean_Server_Logging_MessageMethod_all___closed__0;
                        v___x_1457_ = lean_string_dec_eq(v_method_1451_, v___x_1456_);
                        if v___x_1457_ == 0 {
                            lean_dec(v_params_x3f_1452_);
                            state = 1;
                            continue;
                        } else {
                            v_params_1458_ = l_Option_toJson___at___00Lean_Server_Logging_messageMethod_x3f_spec__0(v_params_x3f_1452_);
                            v___x_1459_ =
                                l_Lean_Lsp_instFromJsonRpcCallParams_fromJson(v_params_1458_);
                            if lean_obj_tag(v___x_1459_) == 1 {
                                lean_dec_ref(v_method_1451_);
                                v_a_1460_ = lean_ctor_get(v___x_1459_, 0);
                                v_isSharedCheck_1470_ = (!lean_is_exclusive(v___x_1459_)) as u8;
                                if v_isSharedCheck_1470_ == 0 {
                                    v___x_1462_ = v___x_1459_;
                                    v_isShared_1463_ = v_isSharedCheck_1470_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_inc(v_a_1460_);
                                    lean_dec(v___x_1459_);
                                    v___x_1462_ = lean_box(0);
                                    v_isShared_1463_ = v_isSharedCheck_1470_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                lean_dec_ref(v___x_1459_);
                                state = 1;
                                continue;
                            }
                        }
                    }
                    1 => {
                        v_method_1471_ = lean_ctor_get(v_x_1450_, 0);
                        lean_inc_ref(v_method_1471_);
                        lean_dec_ref_known(v_x_1450_, 2);
                        v___x_1472_ = lean_alloc_ctor(2, 1, (0) as u32);
                        lean_ctor_set(v___x_1472_, 0, v_method_1471_);
                        v___x_1473_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1473_, 0, v___x_1472_);
                        return v___x_1473_;
                    }
                    _ => {
                        lean_dec_ref(v_x_1450_);
                        v___x_1474_ = lean_box(0);
                        return v___x_1474_;
                    }
                }
            }
            1 => {
                v___x_1454_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1454_, 0, v_method_1451_);
                v___x_1455_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1455_, 0, v___x_1454_);
                return v___x_1455_;
            }
            2 => {
                v_method_1464_ = lean_ctor_get(v_a_1460_, 1);
                lean_inc(v_method_1464_);
                lean_dec(v_a_1460_);
                v___x_1465_ = l_Lean_Name_toString(v_method_1464_, v___x_1457_);
                if v_isShared_1463_ == 0 {
                    lean_ctor_set(v___x_1462_, 0, v___x_1465_);
                    v___x_1467_ = v___x_1462_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1469_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1469_, 0, v___x_1465_);
                    v___x_1467_ = v_reuseFailAlloc_1469_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1468_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1468_, 0, v___x_1467_);
                return v___x_1468_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_Logging_0__Lean_Server_Logging_messageId_x3f(
    mut v_x_1475_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_1475_) {
        0 => {
            let mut v_id_1476_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1477_: *mut LeanObject = core::ptr::null_mut();
            v_id_1476_ = lean_ctor_get(v_x_1475_, 0);
            lean_inc(v_id_1476_);
            v___x_1477_ = lean_alloc_ctor(1, 1, (0) as u32);
            lean_ctor_set(v___x_1477_, 0, v_id_1476_);
            return v___x_1477_;
        }
        2 => {
            let mut v_id_1478_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1479_: *mut LeanObject = core::ptr::null_mut();
            v_id_1478_ = lean_ctor_get(v_x_1475_, 0);
            lean_inc(v_id_1478_);
            v___x_1479_ = lean_alloc_ctor(1, 1, (0) as u32);
            lean_ctor_set(v___x_1479_, 0, v_id_1478_);
            return v___x_1479_;
        }
        3 => {
            let mut v_id_1480_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1481_: *mut LeanObject = core::ptr::null_mut();
            v_id_1480_ = lean_ctor_get(v_x_1475_, 0);
            lean_inc(v_id_1480_);
            v___x_1481_ = lean_alloc_ctor(1, 1, (0) as u32);
            lean_ctor_set(v___x_1481_, 0, v_id_1480_);
            return v___x_1481_;
        }
        _ => {
            let mut v___x_1482_: *mut LeanObject = core::ptr::null_mut();
            v___x_1482_ = lean_box(0);
            return v___x_1482_;
        }
    }
}
pub unsafe fn l___private_Lean_Server_Logging_0__Lean_Server_Logging_messageId_x3f___boxed(
    mut v_x_1483_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1484_: *mut LeanObject = core::ptr::null_mut();
    v_res_1484_ = l___private_Lean_Server_Logging_0__Lean_Server_Logging_messageId_x3f(v_x_1483_);
    lean_dec_ref(v_x_1483_);
    return v_res_1484_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_method_x3f_spec__0_spec__0___redArg(
    mut v_a_1485_: *mut LeanObject,
    mut v_x_1486_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: u8 = 0;
    let mut v___x_1493_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1486_) == 0 {
                    v___x_1487_ = lean_box(0);
                    return v___x_1487_;
                } else {
                    v_key_1488_ = lean_ctor_get(v_x_1486_, 0);
                    v_value_1489_ = lean_ctor_get(v_x_1486_, 1);
                    v_tail_1490_ = lean_ctor_get(v_x_1486_, 2);
                    v___x_1491_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_key_1488_, v_a_1485_);
                    if v___x_1491_ == 0 {
                        v_x_1486_ = v_tail_1490_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_value_1489_);
                        v___x_1493_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1493_, 0, v_value_1489_);
                        return v___x_1493_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_method_x3f_spec__0_spec__0___redArg___boxed(
    mut v_a_1494_: *mut LeanObject,
    mut v_x_1495_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1496_: *mut LeanObject = core::ptr::null_mut();
    v_res_1496_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_method_x3f_spec__0_spec__0___redArg(v_a_1494_, v_x_1495_);
    lean_dec(v_x_1495_);
    lean_dec(v_a_1494_);
    return v_res_1496_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_method_x3f_spec__0___redArg(
    mut v_m_1497_: *mut LeanObject,
    mut v_a_1498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_1499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: u64 = 0;
    let mut v___x_1502_: u64 = 0;
    let mut v___x_1503_: u64 = 0;
    let mut v_fold_1504_: u64 = 0;
    let mut v___x_1505_: u64 = 0;
    let mut v___x_1506_: u64 = 0;
    let mut v___x_1507_: u64 = 0;
    let mut v___x_1508_: usize = 0;
    let mut v___x_1509_: usize = 0;
    let mut v___x_1510_: usize = 0;
    let mut v___x_1511_: usize = 0;
    let mut v___x_1512_: usize = 0;
    let mut v___x_1513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut LeanObject = core::ptr::null_mut();
    v_buckets_1499_ = lean_ctor_get(v_m_1497_, 1);
    v___x_1500_ = lean_array_get_size(v_buckets_1499_);
    v___x_1501_ = l_Lean_JsonRpc_instHashableRequestID_hash(v_a_1498_);
    v___x_1502_ = 32u64;
    v___x_1503_ = lean_uint64_shift_right(v___x_1501_, v___x_1502_);
    v_fold_1504_ = lean_uint64_xor(v___x_1501_, v___x_1503_);
    v___x_1505_ = 16u64;
    v___x_1506_ = lean_uint64_shift_right(v_fold_1504_, v___x_1505_);
    v___x_1507_ = lean_uint64_xor(v_fold_1504_, v___x_1506_);
    v___x_1508_ = lean_uint64_to_usize(v___x_1507_);
    v___x_1509_ = lean_usize_of_nat(v___x_1500_);
    v___x_1510_ = 1usize;
    v___x_1511_ = lean_usize_sub(v___x_1509_, v___x_1510_);
    v___x_1512_ = lean_usize_land(v___x_1508_, v___x_1511_);
    v___x_1513_ = lean_array_uget_borrowed(v_buckets_1499_, v___x_1512_);
    v___x_1514_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_method_x3f_spec__0_spec__0___redArg(v_a_1498_, v___x_1513_);
    return v___x_1514_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_method_x3f_spec__0___redArg___boxed(
    mut v_m_1515_: *mut LeanObject,
    mut v_a_1516_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1517_: *mut LeanObject = core::ptr::null_mut();
    v_res_1517_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_method_x3f_spec__0___redArg(v_m_1515_, v_a_1516_);
    lean_dec(v_a_1516_);
    lean_dec_ref(v_m_1515_);
    return v_res_1517_;
}
pub unsafe fn l___private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_method_x3f(
    mut v_pending_1518_: *mut LeanObject,
    mut v_msg_1519_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1520_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_msg_1519_);
    v___x_1520_ = l_Lean_Server_Logging_messageMethod_x3f(v_msg_1519_);
    if lean_obj_tag(v___x_1520_) == 0 {
        let mut v___x_1521_: *mut LeanObject = core::ptr::null_mut();
        v___x_1521_ =
            l___private_Lean_Server_Logging_0__Lean_Server_Logging_messageId_x3f(v_msg_1519_);
        lean_dec_ref(v_msg_1519_);
        if lean_obj_tag(v___x_1521_) == 0 {
            return v___x_1520_;
        } else {
            let mut v_val_1522_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1523_: *mut LeanObject = core::ptr::null_mut();
            v_val_1522_ = lean_ctor_get(v___x_1521_, 0);
            lean_inc(v_val_1522_);
            lean_dec_ref_known(v___x_1521_, 1);
            v___x_1523_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_method_x3f_spec__0___redArg(v_pending_1518_, v_val_1522_);
            lean_dec(v_val_1522_);
            return v___x_1523_;
        }
    } else {
        lean_dec_ref(v_msg_1519_);
        return v___x_1520_;
    }
}
pub unsafe fn l___private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_method_x3f___boxed(
    mut v_pending_1524_: *mut LeanObject,
    mut v_msg_1525_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1526_: *mut LeanObject = core::ptr::null_mut();
    v_res_1526_ = l___private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_method_x3f(
        v_pending_1524_,
        v_msg_1525_,
    );
    lean_dec_ref(v_pending_1524_);
    return v_res_1526_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_method_x3f_spec__0(
    mut v_00_u03b2_1527_: *mut LeanObject,
    mut v_m_1528_: *mut LeanObject,
    mut v_a_1529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1530_: *mut LeanObject = core::ptr::null_mut();
    v___x_1530_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_method_x3f_spec__0___redArg(v_m_1528_, v_a_1529_);
    return v___x_1530_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_method_x3f_spec__0___boxed(
    mut v_00_u03b2_1531_: *mut LeanObject,
    mut v_m_1532_: *mut LeanObject,
    mut v_a_1533_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1534_: *mut LeanObject = core::ptr::null_mut();
    v_res_1534_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_method_x3f_spec__0(v_00_u03b2_1531_, v_m_1532_, v_a_1533_);
    lean_dec(v_a_1533_);
    lean_dec_ref(v_m_1532_);
    return v_res_1534_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_method_x3f_spec__0_spec__0(
    mut v_00_u03b2_1535_: *mut LeanObject,
    mut v_a_1536_: *mut LeanObject,
    mut v_x_1537_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1538_: *mut LeanObject = core::ptr::null_mut();
    v___x_1538_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_method_x3f_spec__0_spec__0___redArg(v_a_1536_, v_x_1537_);
    return v___x_1538_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_method_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b2_1539_: *mut LeanObject,
    mut v_a_1540_: *mut LeanObject,
    mut v_x_1541_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1542_: *mut LeanObject = core::ptr::null_mut();
    v_res_1542_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_method_x3f_spec__0_spec__0(v_00_u03b2_1539_, v_a_1540_, v_x_1541_);
    lean_dec(v_x_1541_);
    lean_dec(v_a_1540_);
    return v_res_1542_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_spec__0_spec__0___redArg(
    mut v_a_1543_: *mut LeanObject,
    mut v_x_1544_: *mut LeanObject,
) -> u8 {
    let mut v___x_1545_: u8 = 0;
    let mut v_key_1546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1544_) == 0 {
                    v___x_1545_ = 0;
                    return v___x_1545_;
                } else {
                    v_key_1546_ = lean_ctor_get(v_x_1544_, 0);
                    v_tail_1547_ = lean_ctor_get(v_x_1544_, 2);
                    v___x_1548_ = lean_string_dec_eq(v_key_1546_, v_a_1543_);
                    if v___x_1548_ == 0 {
                        v_x_1544_ = v_tail_1547_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1548_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_spec__0_spec__0___redArg___boxed(
    mut v_a_1550_: *mut LeanObject,
    mut v_x_1551_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1552_: u8 = 0;
    let mut v_r_1553_: *mut LeanObject = core::ptr::null_mut();
    v_res_1552_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_spec__0_spec__0___redArg(v_a_1550_, v_x_1551_);
    lean_dec(v_x_1551_);
    lean_dec_ref(v_a_1550_);
    v_r_1553_ = lean_box((v_res_1552_) as usize);
    return v_r_1553_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_spec__0___redArg(
    mut v_m_1554_: *mut LeanObject,
    mut v_a_1555_: *mut LeanObject,
) -> u8 {
    let mut v_buckets_1556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: u64 = 0;
    let mut v___x_1559_: u64 = 0;
    let mut v___x_1560_: u64 = 0;
    let mut v_fold_1561_: u64 = 0;
    let mut v___x_1562_: u64 = 0;
    let mut v___x_1563_: u64 = 0;
    let mut v___x_1564_: u64 = 0;
    let mut v___x_1565_: usize = 0;
    let mut v___x_1566_: usize = 0;
    let mut v___x_1567_: usize = 0;
    let mut v___x_1568_: usize = 0;
    let mut v___x_1569_: usize = 0;
    let mut v___x_1570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: u8 = 0;
    v_buckets_1556_ = lean_ctor_get(v_m_1554_, 1);
    v___x_1557_ = lean_array_get_size(v_buckets_1556_);
    v___x_1558_ = lean_string_hash(v_a_1555_);
    v___x_1559_ = 32u64;
    v___x_1560_ = lean_uint64_shift_right(v___x_1558_, v___x_1559_);
    v_fold_1561_ = lean_uint64_xor(v___x_1558_, v___x_1560_);
    v___x_1562_ = 16u64;
    v___x_1563_ = lean_uint64_shift_right(v_fold_1561_, v___x_1562_);
    v___x_1564_ = lean_uint64_xor(v_fold_1561_, v___x_1563_);
    v___x_1565_ = lean_uint64_to_usize(v___x_1564_);
    v___x_1566_ = lean_usize_of_nat(v___x_1557_);
    v___x_1567_ = 1usize;
    v___x_1568_ = lean_usize_sub(v___x_1566_, v___x_1567_);
    v___x_1569_ = lean_usize_land(v___x_1565_, v___x_1568_);
    v___x_1570_ = lean_array_uget_borrowed(v_buckets_1556_, v___x_1569_);
    v___x_1571_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_spec__0_spec__0___redArg(v_a_1555_, v___x_1570_);
    return v___x_1571_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_spec__0___redArg___boxed(
    mut v_m_1572_: *mut LeanObject,
    mut v_a_1573_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1574_: u8 = 0;
    let mut v_r_1575_: *mut LeanObject = core::ptr::null_mut();
    v_res_1574_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_spec__0___redArg(v_m_1572_, v_a_1573_);
    lean_dec_ref(v_a_1573_);
    lean_dec_ref(v_m_1572_);
    v_r_1575_ = lean_box((v_res_1574_) as usize);
    return v_r_1575_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_spec__2(
    mut v_val_1576_: *mut LeanObject,
    mut v___x_1577_: u8,
    mut v_as_1578_: *mut LeanObject,
    mut v_i_1579_: usize,
    mut v_stop_1580_: usize,
) -> u8 {
    let mut v___x_1582_: usize = 0;
    let mut v___x_1583_: usize = 0;
    let mut v___x_1585_: u8 = 0;
    let mut v___x_1586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: u8 = 0;
    let mut v___x_1588_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1585_ = lean_usize_dec_eq(v_i_1579_, v_stop_1580_);
                if v___x_1585_ == 0 {
                    v___x_1586_ = lean_array_uget_borrowed(v_as_1578_, v_i_1579_);
                    v___x_1587_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_spec__0___redArg(v_val_1576_, v___x_1586_);
                    if v___x_1587_ == 0 {
                        if v___x_1577_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            return v___x_1577_;
                        }
                    } else {
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_1588_ = 0;
                    return v___x_1588_;
                }
            }
            1 => {
                v___x_1582_ = 1usize;
                v___x_1583_ = lean_usize_add(v_i_1579_, v___x_1582_);
                v_i_1579_ = v___x_1583_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_spec__2___boxed(
    mut v_val_1589_: *mut LeanObject,
    mut v___x_1590_: *mut LeanObject,
    mut v_as_1591_: *mut LeanObject,
    mut v_i_1592_: *mut LeanObject,
    mut v_stop_1593_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1504__boxed_1594_: u8 = 0;
    let mut v_i_boxed_1595_: usize = 0;
    let mut v_stop_boxed_1596_: usize = 0;
    let mut v_res_1597_: u8 = 0;
    let mut v_r_1598_: *mut LeanObject = core::ptr::null_mut();
    v___x_1504__boxed_1594_ = (lean_unbox(v___x_1590_) as u8);
    v_i_boxed_1595_ = lean_unbox_usize(v_i_1592_);
    lean_dec(v_i_1592_);
    v_stop_boxed_1596_ = lean_unbox_usize(v_stop_1593_);
    lean_dec(v_stop_1593_);
    v_res_1597_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_spec__2(v_val_1589_, v___x_1504__boxed_1594_, v_as_1591_, v_i_boxed_1595_, v_stop_boxed_1596_);
    lean_dec_ref(v_as_1591_);
    lean_dec_ref(v_val_1589_);
    v_r_1598_ = lean_box((v_res_1597_) as usize);
    return v_r_1598_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_spec__1(
    mut v_val_1599_: *mut LeanObject,
    mut v_as_1600_: *mut LeanObject,
    mut v_i_1601_: usize,
    mut v_stop_1602_: usize,
) -> u8 {
    let mut v___x_1603_: u8 = 0;
    let mut v___x_1604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: u8 = 0;
    let mut v___x_1606_: usize = 0;
    let mut v___x_1607_: usize = 0;
    let mut v___x_1609_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1603_ = lean_usize_dec_eq(v_i_1601_, v_stop_1602_);
                if v___x_1603_ == 0 {
                    v___x_1604_ = lean_array_uget_borrowed(v_as_1600_, v_i_1601_);
                    v___x_1605_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_spec__0___redArg(v_val_1599_, v___x_1604_);
                    if v___x_1605_ == 0 {
                        v___x_1606_ = 1usize;
                        v___x_1607_ = lean_usize_add(v_i_1601_, v___x_1606_);
                        v_i_1601_ = v___x_1607_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1605_;
                    }
                } else {
                    v___x_1609_ = 0;
                    return v___x_1609_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_spec__1___boxed(
    mut v_val_1610_: *mut LeanObject,
    mut v_as_1611_: *mut LeanObject,
    mut v_i_1612_: *mut LeanObject,
    mut v_stop_1613_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1614_: usize = 0;
    let mut v_stop_boxed_1615_: usize = 0;
    let mut v_res_1616_: u8 = 0;
    let mut v_r_1617_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1614_ = lean_unbox_usize(v_i_1612_);
    lean_dec(v_i_1612_);
    v_stop_boxed_1615_ = lean_unbox_usize(v_stop_1613_);
    lean_dec(v_stop_1613_);
    v_res_1616_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_spec__1(v_val_1610_, v_as_1611_, v_i_boxed_1614_, v_stop_boxed_1615_);
    lean_dec_ref(v_as_1611_);
    lean_dec_ref(v_val_1610_);
    v_r_1617_ = lean_box((v_res_1616_) as usize);
    return v_r_1617_;
}
pub unsafe fn l___private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed(
    mut v_cfg_1618_: *mut LeanObject,
    mut v_pending_1619_: *mut LeanObject,
    mut v_msg_1620_: *mut LeanObject,
) -> u8 {
    let mut v_isEnabled_1621_: u8 = 0;
    let mut v_allowedMethods_x3f_1622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_disallowedMethods_x3f_1623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: u8 = 0;
    let mut v___x_1625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_allMethods_1627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: u8 = 0;
    let mut v___x_1633_: usize = 0;
    let mut v___x_1634_: usize = 0;
    let mut v___x_1635_: u8 = 0;
    let mut v_val_1636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: u8 = 0;
    let mut v___x_1640_: usize = 0;
    let mut v___x_1641_: usize = 0;
    let mut v___x_1642_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_isEnabled_1621_ = lean_ctor_get_uint8(
                    v_cfg_1618_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                if v_isEnabled_1621_ == 0 {
                    lean_dec_ref(v_msg_1620_);
                    return v_isEnabled_1621_;
                } else {
                    v_allowedMethods_x3f_1622_ = lean_ctor_get(v_cfg_1618_, 1);
                    v_disallowedMethods_x3f_1623_ = lean_ctor_get(v_cfg_1618_, 2);
                    v___x_1624_ = 0;
                    v___x_1625_ = l___private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_method_x3f(v_pending_1619_, v_msg_1620_);
                    if lean_obj_tag(v___x_1625_) == 1 {
                        v_val_1626_ = lean_ctor_get(v___x_1625_, 0);
                        lean_inc(v_val_1626_);
                        lean_dec_ref_known(v___x_1625_, 1);
                        v_allMethods_1627_ = l___private_Lean_Server_Logging_0__Lean_Server_Logging_MessageMethod_all(v_val_1626_);
                        if lean_obj_tag(v_allowedMethods_x3f_1622_) == 1 {
                            v_val_1636_ = lean_ctor_get(v_allowedMethods_x3f_1622_, 0);
                            v___x_1637_ = lean_unsigned_to_nat(0);
                            v___x_1638_ = lean_array_get_size(v_allMethods_1627_);
                            v___x_1639_ = lean_nat_dec_lt(v___x_1637_, v___x_1638_);
                            if v___x_1639_ == 0 {
                                state = 1;
                                continue;
                            } else {
                                if v___x_1639_ == 0 {
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_1640_ = 0usize;
                                    v___x_1641_ = lean_usize_of_nat(v___x_1638_);
                                    v___x_1642_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_spec__2(v_val_1636_, v_isEnabled_1621_, v_allMethods_1627_, v___x_1640_, v___x_1641_);
                                    if v___x_1642_ == 0 {
                                        state = 1;
                                        continue;
                                    } else {
                                        lean_dec_ref(v_allMethods_1627_);
                                        return v___x_1624_;
                                    }
                                }
                            }
                        } else {
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_1625_);
                        return v___x_1624_;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_disallowedMethods_x3f_1623_) == 1 {
                    v_val_1629_ = lean_ctor_get(v_disallowedMethods_x3f_1623_, 0);
                    v___x_1630_ = lean_unsigned_to_nat(0);
                    v___x_1631_ = lean_array_get_size(v_allMethods_1627_);
                    v___x_1632_ = lean_nat_dec_lt(v___x_1630_, v___x_1631_);
                    if v___x_1632_ == 0 {
                        lean_dec_ref(v_allMethods_1627_);
                        return v_isEnabled_1621_;
                    } else {
                        if v___x_1632_ == 0 {
                            lean_dec_ref(v_allMethods_1627_);
                            return v_isEnabled_1621_;
                        } else {
                            v___x_1633_ = 0usize;
                            v___x_1634_ = lean_usize_of_nat(v___x_1631_);
                            v___x_1635_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_spec__1(v_val_1629_, v_allMethods_1627_, v___x_1633_, v___x_1634_);
                            lean_dec_ref(v_allMethods_1627_);
                            if v___x_1635_ == 0 {
                                return v_isEnabled_1621_;
                            } else {
                                return v___x_1624_;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_allMethods_1627_);
                    return v_isEnabled_1621_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed___boxed(
    mut v_cfg_1643_: *mut LeanObject,
    mut v_pending_1644_: *mut LeanObject,
    mut v_msg_1645_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1646_: u8 = 0;
    let mut v_r_1647_: *mut LeanObject = core::ptr::null_mut();
    v_res_1646_ = l___private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed(
        v_cfg_1643_,
        v_pending_1644_,
        v_msg_1645_,
    );
    lean_dec_ref(v_pending_1644_);
    lean_dec_ref(v_cfg_1643_);
    v_r_1647_ = lean_box((v_res_1646_) as usize);
    return v_r_1647_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_spec__0(
    mut v_00_u03b2_1648_: *mut LeanObject,
    mut v_m_1649_: *mut LeanObject,
    mut v_a_1650_: *mut LeanObject,
) -> u8 {
    let mut v___x_1651_: u8 = 0;
    v___x_1651_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_spec__0___redArg(v_m_1649_, v_a_1650_);
    return v___x_1651_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_spec__0___boxed(
    mut v_00_u03b2_1652_: *mut LeanObject,
    mut v_m_1653_: *mut LeanObject,
    mut v_a_1654_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1655_: u8 = 0;
    let mut v_r_1656_: *mut LeanObject = core::ptr::null_mut();
    v_res_1655_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_spec__0(v_00_u03b2_1652_, v_m_1653_, v_a_1654_);
    lean_dec_ref(v_a_1654_);
    lean_dec_ref(v_m_1653_);
    v_r_1656_ = lean_box((v_res_1655_) as usize);
    return v_r_1656_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_spec__0_spec__0(
    mut v_00_u03b2_1657_: *mut LeanObject,
    mut v_a_1658_: *mut LeanObject,
    mut v_x_1659_: *mut LeanObject,
) -> u8 {
    let mut v___x_1660_: u8 = 0;
    v___x_1660_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_spec__0_spec__0___redArg(v_a_1658_, v_x_1659_);
    return v___x_1660_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_spec__0_spec__0___boxed(
    mut v_00_u03b2_1661_: *mut LeanObject,
    mut v_a_1662_: *mut LeanObject,
    mut v_x_1663_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1664_: u8 = 0;
    let mut v_r_1665_: *mut LeanObject = core::ptr::null_mut();
    v_res_1664_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_spec__0_spec__0(v_00_u03b2_1661_, v_a_1662_, v_x_1663_);
    lean_dec(v_x_1663_);
    lean_dec_ref(v_a_1662_);
    v_r_1665_ = lean_box((v_res_1664_) as usize);
    return v_r_1665_;
}
pub unsafe fn l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonZonedDateTime___lam__0(
    mut v_dt_1666_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut LeanObject = core::ptr::null_mut();
    v___x_1667_ = l_Std_Time_ZonedDateTime_toISO8601String(v_dt_1666_);
    v___x_1668_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_1668_, 0, v___x_1667_);
    return v___x_1668_;
}
pub unsafe fn l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonZonedDateTime___lam__0(
    mut v_x_1674_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1674_) == 3 {
        let mut v_s_1675_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1676_: *mut LeanObject = core::ptr::null_mut();
        v_s_1675_ = lean_ctor_get(v_x_1674_, 0);
        lean_inc_ref(v_s_1675_);
        lean_dec_ref_known(v_x_1674_, 1);
        v___x_1676_ = l_Std_Time_ZonedDateTime_fromISO8601String(v_s_1675_);
        return v___x_1676_;
    } else {
        let mut v___x_1677_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_1674_);
        v___x_1677_ = l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonZonedDateTime___lam__0___closed__1;
        return v___x_1677_;
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__0(
    mut v_j_1680_: *mut LeanObject,
    mut v_k_1681_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1682_: *mut LeanObject = core::ptr::null_mut();
    v___x_1682_ = l_Lean_Json_getObjValD(v_j_1680_, v_k_1681_);
    if lean_obj_tag(v___x_1682_) == 3 {
        let mut v_s_1683_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1684_: *mut LeanObject = core::ptr::null_mut();
        v_s_1683_ = lean_ctor_get(v___x_1682_, 0);
        lean_inc_ref(v_s_1683_);
        lean_dec_ref_known(v___x_1682_, 1);
        v___x_1684_ = l_Std_Time_ZonedDateTime_fromISO8601String(v_s_1683_);
        return v___x_1684_;
    } else {
        let mut v___x_1685_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_1682_);
        v___x_1685_ = l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonZonedDateTime___lam__0___closed__1;
        return v___x_1685_;
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__0___boxed(
    mut v_j_1686_: *mut LeanObject,
    mut v_k_1687_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1688_: *mut LeanObject = core::ptr::null_mut();
    v_res_1688_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__0(v_j_1686_, v_k_1687_);
    lean_dec_ref(v_k_1687_);
    return v_res_1688_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__1(
    mut v_j_1689_: *mut LeanObject,
    mut v_k_1690_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut LeanObject = core::ptr::null_mut();
    v___x_1691_ = l_Lean_Json_getObjValD(v_j_1689_, v_k_1690_);
    v___x_1692_ = l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson(v___x_1691_);
    return v___x_1692_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__1___boxed(
    mut v_j_1693_: *mut LeanObject,
    mut v_k_1694_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1695_: *mut LeanObject = core::ptr::null_mut();
    v_res_1695_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__1(v_j_1693_, v_k_1694_);
    lean_dec_ref(v_k_1694_);
    return v_res_1695_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__2(
    mut v_j_1696_: *mut LeanObject,
    mut v_k_1697_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut LeanObject = core::ptr::null_mut();
    v___x_1698_ = l_Lean_Json_getObjValD(v_j_1696_, v_k_1697_);
    v___x_1699_ = l_Lean_JsonRpc_instFromJsonMessageKind_fromJson(v___x_1698_);
    return v___x_1699_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__2___boxed(
    mut v_j_1700_: *mut LeanObject,
    mut v_k_1701_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1702_: *mut LeanObject = core::ptr::null_mut();
    v_res_1702_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__2(v_j_1700_, v_k_1701_);
    lean_dec_ref(v_k_1701_);
    return v_res_1702_;
}
pub unsafe fn _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__2()
-> *mut LeanObject {
    let mut v___x_1706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut LeanObject = core::ptr::null_mut();
    v___x_1706_ = lean_unsigned_to_nat(32700);
    v___x_1707_ = lean_nat_to_int(v___x_1706_);
    return v___x_1707_;
}
pub unsafe fn _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__3()
-> *mut LeanObject {
    let mut v___x_1708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut LeanObject = core::ptr::null_mut();
    v___x_1708_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__2), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__2_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__2);
    v___x_1709_ = lean_int_neg(v___x_1708_);
    return v___x_1709_;
}
pub unsafe fn _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__4()
-> *mut LeanObject {
    let mut v___x_1710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut LeanObject = core::ptr::null_mut();
    v___x_1710_ = lean_unsigned_to_nat(32600);
    v___x_1711_ = lean_nat_to_int(v___x_1710_);
    return v___x_1711_;
}
pub unsafe fn _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__5()
-> *mut LeanObject {
    let mut v___x_1712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut LeanObject = core::ptr::null_mut();
    v___x_1712_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__4), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__4_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__4);
    v___x_1713_ = lean_int_neg(v___x_1712_);
    return v___x_1713_;
}
pub unsafe fn _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__6()
-> *mut LeanObject {
    let mut v___x_1714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut LeanObject = core::ptr::null_mut();
    v___x_1714_ = lean_unsigned_to_nat(32601);
    v___x_1715_ = lean_nat_to_int(v___x_1714_);
    return v___x_1715_;
}
pub unsafe fn _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__7()
-> *mut LeanObject {
    let mut v___x_1716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut LeanObject = core::ptr::null_mut();
    v___x_1716_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__6), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__6_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__6);
    v___x_1717_ = lean_int_neg(v___x_1716_);
    return v___x_1717_;
}
pub unsafe fn _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__8()
-> *mut LeanObject {
    let mut v___x_1718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut LeanObject = core::ptr::null_mut();
    v___x_1718_ = lean_unsigned_to_nat(32602);
    v___x_1719_ = lean_nat_to_int(v___x_1718_);
    return v___x_1719_;
}
pub unsafe fn _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__9()
-> *mut LeanObject {
    let mut v___x_1720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut LeanObject = core::ptr::null_mut();
    v___x_1720_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__8), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__8_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__8);
    v___x_1721_ = lean_int_neg(v___x_1720_);
    return v___x_1721_;
}
pub unsafe fn _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__10()
-> *mut LeanObject {
    let mut v___x_1722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut LeanObject = core::ptr::null_mut();
    v___x_1722_ = lean_unsigned_to_nat(32603);
    v___x_1723_ = lean_nat_to_int(v___x_1722_);
    return v___x_1723_;
}
pub unsafe fn _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__11()
-> *mut LeanObject {
    let mut v___x_1724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut LeanObject = core::ptr::null_mut();
    v___x_1724_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__10), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__10_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__10);
    v___x_1725_ = lean_int_neg(v___x_1724_);
    return v___x_1725_;
}
pub unsafe fn _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__12()
-> *mut LeanObject {
    let mut v___x_1726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut LeanObject = core::ptr::null_mut();
    v___x_1726_ = lean_unsigned_to_nat(32002);
    v___x_1727_ = lean_nat_to_int(v___x_1726_);
    return v___x_1727_;
}
pub unsafe fn _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__13()
-> *mut LeanObject {
    let mut v___x_1728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut LeanObject = core::ptr::null_mut();
    v___x_1728_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__12), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__12_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__12);
    v___x_1729_ = lean_int_neg(v___x_1728_);
    return v___x_1729_;
}
pub unsafe fn _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__14()
-> *mut LeanObject {
    let mut v___x_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut LeanObject = core::ptr::null_mut();
    v___x_1730_ = lean_unsigned_to_nat(32001);
    v___x_1731_ = lean_nat_to_int(v___x_1730_);
    return v___x_1731_;
}
pub unsafe fn _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__15()
-> *mut LeanObject {
    let mut v___x_1732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut LeanObject = core::ptr::null_mut();
    v___x_1732_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__14), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__14_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__14);
    v___x_1733_ = lean_int_neg(v___x_1732_);
    return v___x_1733_;
}
pub unsafe fn _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__16()
-> *mut LeanObject {
    let mut v___x_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut LeanObject = core::ptr::null_mut();
    v___x_1734_ = lean_unsigned_to_nat(32801);
    v___x_1735_ = lean_nat_to_int(v___x_1734_);
    return v___x_1735_;
}
pub unsafe fn _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__17()
-> *mut LeanObject {
    let mut v___x_1736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut LeanObject = core::ptr::null_mut();
    v___x_1736_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__16), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__16_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__16);
    v___x_1737_ = lean_int_neg(v___x_1736_);
    return v___x_1737_;
}
pub unsafe fn _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__18()
-> *mut LeanObject {
    let mut v___x_1738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut LeanObject = core::ptr::null_mut();
    v___x_1738_ = lean_unsigned_to_nat(32800);
    v___x_1739_ = lean_nat_to_int(v___x_1738_);
    return v___x_1739_;
}
pub unsafe fn _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__19()
-> *mut LeanObject {
    let mut v___x_1740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut LeanObject = core::ptr::null_mut();
    v___x_1740_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__18), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__18_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__18);
    v___x_1741_ = lean_int_neg(v___x_1740_);
    return v___x_1741_;
}
pub unsafe fn _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__20()
-> *mut LeanObject {
    let mut v___x_1742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut LeanObject = core::ptr::null_mut();
    v___x_1742_ = lean_unsigned_to_nat(32900);
    v___x_1743_ = lean_nat_to_int(v___x_1742_);
    return v___x_1743_;
}
pub unsafe fn _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__21()
-> *mut LeanObject {
    let mut v___x_1744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut LeanObject = core::ptr::null_mut();
    v___x_1744_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__20), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__20_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__20);
    v___x_1745_ = lean_int_neg(v___x_1744_);
    return v___x_1745_;
}
pub unsafe fn _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__22()
-> *mut LeanObject {
    let mut v___x_1746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut LeanObject = core::ptr::null_mut();
    v___x_1746_ = lean_unsigned_to_nat(32901);
    v___x_1747_ = lean_nat_to_int(v___x_1746_);
    return v___x_1747_;
}
pub unsafe fn _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__23()
-> *mut LeanObject {
    let mut v___x_1748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut LeanObject = core::ptr::null_mut();
    v___x_1748_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__22), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__22_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__22);
    v___x_1749_ = lean_int_neg(v___x_1748_);
    return v___x_1749_;
}
pub unsafe fn _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__24()
-> *mut LeanObject {
    let mut v___x_1750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut LeanObject = core::ptr::null_mut();
    v___x_1750_ = lean_unsigned_to_nat(32902);
    v___x_1751_ = lean_nat_to_int(v___x_1750_);
    return v___x_1751_;
}
pub unsafe fn _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__25()
-> *mut LeanObject {
    let mut v___x_1752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut LeanObject = core::ptr::null_mut();
    v___x_1752_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__24), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__24_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__24);
    v___x_1753_ = lean_int_neg(v___x_1752_);
    return v___x_1753_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4(
    mut v_j_1790_: *mut LeanObject,
    mut v_k_1791_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_1795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mantissa_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exponent_1797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: u8 = 0;
    let mut v___x_1800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: u8 = 0;
    let mut v___x_1802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: u8 = 0;
    let mut v___x_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: u8 = 0;
    let mut v___x_1806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: u8 = 0;
    let mut v___x_1808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: u8 = 0;
    let mut v___x_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: u8 = 0;
    let mut v___x_1812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: u8 = 0;
    let mut v___x_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: u8 = 0;
    let mut v___x_1816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: u8 = 0;
    let mut v___x_1818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: u8 = 0;
    let mut v___x_1820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: u8 = 0;
    let mut v___x_1822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: u8 = 0;
    let mut v___x_1824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: u8 = 0;
    let mut v___x_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: u8 = 0;
    let mut v___x_1830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: u8 = 0;
    let mut v___x_1833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: u8 = 0;
    let mut v___x_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: u8 = 0;
    let mut v___x_1839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: u8 = 0;
    let mut v___x_1842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: u8 = 0;
    let mut v___x_1845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: u8 = 0;
    let mut v___x_1848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: u8 = 0;
    let mut v___x_1851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: u8 = 0;
    let mut v___x_1854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: u8 = 0;
    let mut v___x_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1794_ = l_Lean_Json_getObjValD(v_j_1790_, v_k_1791_);
                if lean_obj_tag(v___x_1794_) == 2 {
                    v_n_1795_ = lean_ctor_get(v___x_1794_, 0);
                    lean_inc_ref(v_n_1795_);
                    lean_dec_ref_known(v___x_1794_, 1);
                    v_mantissa_1796_ = lean_ctor_get(v_n_1795_, 0);
                    lean_inc(v_mantissa_1796_);
                    v_exponent_1797_ = lean_ctor_get(v_n_1795_, 1);
                    lean_inc(v_exponent_1797_);
                    lean_dec_ref(v_n_1795_);
                    v___x_1798_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__3), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__3_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__3);
                    v___x_1799_ = lean_int_dec_eq(v_mantissa_1796_, v___x_1798_);
                    if v___x_1799_ == 0 {
                        v___x_1800_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__5), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__5_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__5);
                        v___x_1801_ = lean_int_dec_eq(v_mantissa_1796_, v___x_1800_);
                        if v___x_1801_ == 0 {
                            v___x_1802_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__7), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__7_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__7);
                            v___x_1803_ = lean_int_dec_eq(v_mantissa_1796_, v___x_1802_);
                            if v___x_1803_ == 0 {
                                v___x_1804_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__9), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__9_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__9);
                                v___x_1805_ = lean_int_dec_eq(v_mantissa_1796_, v___x_1804_);
                                if v___x_1805_ == 0 {
                                    v___x_1806_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__11), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__11_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__11);
                                    v___x_1807_ = lean_int_dec_eq(v_mantissa_1796_, v___x_1806_);
                                    if v___x_1807_ == 0 {
                                        v___x_1808_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__13), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__13_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__13);
                                        v___x_1809_ =
                                            lean_int_dec_eq(v_mantissa_1796_, v___x_1808_);
                                        if v___x_1809_ == 0 {
                                            v___x_1810_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__15), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__15_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__15);
                                            v___x_1811_ =
                                                lean_int_dec_eq(v_mantissa_1796_, v___x_1810_);
                                            if v___x_1811_ == 0 {
                                                v___x_1812_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__17), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__17_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__17);
                                                v___x_1813_ =
                                                    lean_int_dec_eq(v_mantissa_1796_, v___x_1812_);
                                                if v___x_1813_ == 0 {
                                                    v___x_1814_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__19), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__19_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__19);
                                                    v___x_1815_ = lean_int_dec_eq(
                                                        v_mantissa_1796_,
                                                        v___x_1814_,
                                                    );
                                                    if v___x_1815_ == 0 {
                                                        v___x_1816_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__21), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__21_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__21);
                                                        v___x_1817_ = lean_int_dec_eq(
                                                            v_mantissa_1796_,
                                                            v___x_1816_,
                                                        );
                                                        if v___x_1817_ == 0 {
                                                            v___x_1818_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__23), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__23_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__23);
                                                            v___x_1819_ = lean_int_dec_eq(
                                                                v_mantissa_1796_,
                                                                v___x_1818_,
                                                            );
                                                            if v___x_1819_ == 0 {
                                                                v___x_1820_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__25), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__25_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__25);
                                                                v___x_1821_ = lean_int_dec_eq(
                                                                    v_mantissa_1796_,
                                                                    v___x_1820_,
                                                                );
                                                                lean_dec(v_mantissa_1796_);
                                                                if v___x_1821_ == 0 {
                                                                    lean_dec(v_exponent_1797_);
                                                                    state = 1;
                                                                    continue;
                                                                } else {
                                                                    v___x_1822_ =
                                                                        lean_unsigned_to_nat(0);
                                                                    v___x_1823_ = lean_nat_dec_eq(
                                                                        v_exponent_1797_,
                                                                        v___x_1822_,
                                                                    );
                                                                    lean_dec(v_exponent_1797_);
                                                                    if v___x_1823_ == 0 {
                                                                        state = 1;
                                                                        continue;
                                                                    } else {
                                                                        v___x_1824_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__26;
                                                                        return v___x_1824_;
                                                                    }
                                                                }
                                                            } else {
                                                                lean_dec(v_mantissa_1796_);
                                                                v___x_1825_ =
                                                                    lean_unsigned_to_nat(0);
                                                                v___x_1826_ = lean_nat_dec_eq(
                                                                    v_exponent_1797_,
                                                                    v___x_1825_,
                                                                );
                                                                lean_dec(v_exponent_1797_);
                                                                if v___x_1826_ == 0 {
                                                                    state = 1;
                                                                    continue;
                                                                } else {
                                                                    v___x_1827_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__27;
                                                                    return v___x_1827_;
                                                                }
                                                            }
                                                        } else {
                                                            lean_dec(v_mantissa_1796_);
                                                            v___x_1828_ = lean_unsigned_to_nat(0);
                                                            v___x_1829_ = lean_nat_dec_eq(
                                                                v_exponent_1797_,
                                                                v___x_1828_,
                                                            );
                                                            lean_dec(v_exponent_1797_);
                                                            if v___x_1829_ == 0 {
                                                                state = 1;
                                                                continue;
                                                            } else {
                                                                v___x_1830_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__28;
                                                                return v___x_1830_;
                                                            }
                                                        }
                                                    } else {
                                                        lean_dec(v_mantissa_1796_);
                                                        v___x_1831_ = lean_unsigned_to_nat(0);
                                                        v___x_1832_ = lean_nat_dec_eq(
                                                            v_exponent_1797_,
                                                            v___x_1831_,
                                                        );
                                                        lean_dec(v_exponent_1797_);
                                                        if v___x_1832_ == 0 {
                                                            state = 1;
                                                            continue;
                                                        } else {
                                                            v___x_1833_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__29;
                                                            return v___x_1833_;
                                                        }
                                                    }
                                                } else {
                                                    lean_dec(v_mantissa_1796_);
                                                    v___x_1834_ = lean_unsigned_to_nat(0);
                                                    v___x_1835_ = lean_nat_dec_eq(
                                                        v_exponent_1797_,
                                                        v___x_1834_,
                                                    );
                                                    lean_dec(v_exponent_1797_);
                                                    if v___x_1835_ == 0 {
                                                        state = 1;
                                                        continue;
                                                    } else {
                                                        v___x_1836_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__30;
                                                        return v___x_1836_;
                                                    }
                                                }
                                            } else {
                                                lean_dec(v_mantissa_1796_);
                                                v___x_1837_ = lean_unsigned_to_nat(0);
                                                v___x_1838_ =
                                                    lean_nat_dec_eq(v_exponent_1797_, v___x_1837_);
                                                lean_dec(v_exponent_1797_);
                                                if v___x_1838_ == 0 {
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    v___x_1839_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__31;
                                                    return v___x_1839_;
                                                }
                                            }
                                        } else {
                                            lean_dec(v_mantissa_1796_);
                                            v___x_1840_ = lean_unsigned_to_nat(0);
                                            v___x_1841_ =
                                                lean_nat_dec_eq(v_exponent_1797_, v___x_1840_);
                                            lean_dec(v_exponent_1797_);
                                            if v___x_1841_ == 0 {
                                                state = 1;
                                                continue;
                                            } else {
                                                v___x_1842_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__32;
                                                return v___x_1842_;
                                            }
                                        }
                                    } else {
                                        lean_dec(v_mantissa_1796_);
                                        v___x_1843_ = lean_unsigned_to_nat(0);
                                        v___x_1844_ =
                                            lean_nat_dec_eq(v_exponent_1797_, v___x_1843_);
                                        lean_dec(v_exponent_1797_);
                                        if v___x_1844_ == 0 {
                                            state = 1;
                                            continue;
                                        } else {
                                            v___x_1845_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__33;
                                            return v___x_1845_;
                                        }
                                    }
                                } else {
                                    lean_dec(v_mantissa_1796_);
                                    v___x_1846_ = lean_unsigned_to_nat(0);
                                    v___x_1847_ = lean_nat_dec_eq(v_exponent_1797_, v___x_1846_);
                                    lean_dec(v_exponent_1797_);
                                    if v___x_1847_ == 0 {
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_1848_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__34;
                                        return v___x_1848_;
                                    }
                                }
                            } else {
                                lean_dec(v_mantissa_1796_);
                                v___x_1849_ = lean_unsigned_to_nat(0);
                                v___x_1850_ = lean_nat_dec_eq(v_exponent_1797_, v___x_1849_);
                                lean_dec(v_exponent_1797_);
                                if v___x_1850_ == 0 {
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_1851_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__35;
                                    return v___x_1851_;
                                }
                            }
                        } else {
                            lean_dec(v_mantissa_1796_);
                            v___x_1852_ = lean_unsigned_to_nat(0);
                            v___x_1853_ = lean_nat_dec_eq(v_exponent_1797_, v___x_1852_);
                            lean_dec(v_exponent_1797_);
                            if v___x_1853_ == 0 {
                                state = 1;
                                continue;
                            } else {
                                v___x_1854_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__36;
                                return v___x_1854_;
                            }
                        }
                    } else {
                        lean_dec(v_mantissa_1796_);
                        v___x_1855_ = lean_unsigned_to_nat(0);
                        v___x_1856_ = lean_nat_dec_eq(v_exponent_1797_, v___x_1855_);
                        lean_dec(v_exponent_1797_);
                        if v___x_1856_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            v___x_1857_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__37;
                            return v___x_1857_;
                        }
                    }
                } else {
                    lean_dec(v___x_1794_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1793_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__1;
                return v___x_1793_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___boxed(
    mut v_j_1858_: *mut LeanObject,
    mut v_k_1859_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1860_: *mut LeanObject = core::ptr::null_mut();
    v_res_1860_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4(v_j_1858_, v_k_1859_);
    lean_dec_ref(v_k_1859_);
    return v_res_1860_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__3(
    mut v_j_1864_: *mut LeanObject,
    mut v_k_1865_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1870_: u8 = 0;
    let mut v___x_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1875_: u8 = 0;
    let mut v_n_1876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1879_: u8 = 0;
    let mut v___x_1881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1884_: u8 = 0;
    let mut v___x_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1866_ = l_Lean_Json_getObjValD(v_j_1864_, v_k_1865_);
                match lean_obj_tag(v___x_1866_) {
                    3 => {
                        v_s_1867_ = lean_ctor_get(v___x_1866_, 0);
                        v_isSharedCheck_1875_ = (!lean_is_exclusive(v___x_1866_)) as u8;
                        if v_isSharedCheck_1875_ == 0 {
                            v___x_1869_ = v___x_1866_;
                            v_isShared_1870_ = v_isSharedCheck_1875_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_s_1867_);
                            lean_dec(v___x_1866_);
                            v___x_1869_ = lean_box(0);
                            v_isShared_1870_ = v_isSharedCheck_1875_;
                            state = 1;
                            continue;
                        }
                    }
                    2 => {
                        v_n_1876_ = lean_ctor_get(v___x_1866_, 0);
                        v_isSharedCheck_1884_ = (!lean_is_exclusive(v___x_1866_)) as u8;
                        if v_isSharedCheck_1884_ == 0 {
                            v___x_1878_ = v___x_1866_;
                            v_isShared_1879_ = v_isSharedCheck_1884_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_n_1876_);
                            lean_dec(v___x_1866_);
                            v___x_1878_ = lean_box(0);
                            v_isShared_1879_ = v_isSharedCheck_1884_;
                            state = 3;
                            continue;
                        }
                    }
                    _ => {
                        lean_dec(v___x_1866_);
                        v___x_1885_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__3___closed__1;
                        return v___x_1885_;
                    }
                }
            }
            1 => {
                if v_isShared_1870_ == 0 {
                    lean_ctor_set_tag(v___x_1869_, 0);
                    v___x_1872_ = v___x_1869_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1874_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_s_1867_);
                    v___x_1872_ = v_reuseFailAlloc_1874_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1873_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1873_, 0, v___x_1872_);
                return v___x_1873_;
            }
            3 => {
                if v_isShared_1879_ == 0 {
                    lean_ctor_set_tag(v___x_1878_, 1);
                    v___x_1881_ = v___x_1878_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1883_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_n_1876_);
                    v___x_1881_ = v_reuseFailAlloc_1883_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1882_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1882_, 0, v___x_1881_);
                return v___x_1882_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__3___boxed(
    mut v_j_1886_: *mut LeanObject,
    mut v_k_1887_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1888_: *mut LeanObject = core::ptr::null_mut();
    v_res_1888_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__3(v_j_1886_, v_k_1887_);
    lean_dec_ref(v_k_1887_);
    return v_res_1888_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__5(
    mut v_j_1889_: *mut LeanObject,
    mut v_k_1890_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut LeanObject = core::ptr::null_mut();
    v___x_1891_ = l_Lean_Json_getObjValD(v_j_1889_, v_k_1890_);
    v___x_1892_ = l_Lean_Json_getStr_x3f(v___x_1891_);
    return v___x_1892_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__5___boxed(
    mut v_j_1893_: *mut LeanObject,
    mut v_k_1894_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1895_: *mut LeanObject = core::ptr::null_mut();
    v_res_1895_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__5(v_j_1893_, v_k_1894_);
    lean_dec_ref(v_k_1894_);
    return v_res_1895_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__6(
    mut v_j_1896_: *mut LeanObject,
    mut v_k_1897_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut LeanObject = core::ptr::null_mut();
    v___x_1898_ = l_Lean_Json_getObjValD(v_j_1896_, v_k_1897_);
    v___x_1899_ = l_Lean_Json_Structured_fromJson_x3f(v___x_1898_);
    return v___x_1899_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__6___boxed(
    mut v_j_1900_: *mut LeanObject,
    mut v_k_1901_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1902_: *mut LeanObject = core::ptr::null_mut();
    v_res_1902_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__6(v_j_1900_, v_k_1901_);
    lean_dec_ref(v_k_1901_);
    return v_res_1902_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3(
    mut v_j_1916_: *mut LeanObject,
    mut v_k_1917_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1923_: u8 = 0;
    let mut v___y_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1938_: u8 = 0;
    let mut v___x_1940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1942_: u8 = 0;
    let mut v_a_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_1944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: u8 = 0;
    let mut v___x_1947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1953_: u8 = 0;
    let mut v___x_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1957_: u8 = 0;
    let mut v_a_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1964_: u8 = 0;
    let mut v___x_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1968_: u8 = 0;
    let mut v_a_1969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1975_: u8 = 0;
    let mut v___x_1977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1979_: u8 = 0;
    let mut v_a_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1986_: u8 = 0;
    let mut v___x_1988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1990_: u8 = 0;
    let mut v_a_1991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: u8 = 0;
    let mut v_a_1996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1999_: u8 = 0;
    let mut v___x_2001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: u8 = 0;
    let mut v_reuseFailAlloc_2003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2004_: u8 = 0;
    let mut v___x_2006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2014_: u8 = 0;
    let mut v___x_2015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2019_: u8 = 0;
    let mut v_a_2020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2027_: u8 = 0;
    let mut v___x_2029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2031_: u8 = 0;
    let mut v_a_2032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2038_: u8 = 0;
    let mut v___y_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2051_: u8 = 0;
    let mut v___x_2053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2055_: u8 = 0;
    let mut v_isSharedCheck_2056_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1932_ = l_Lean_Json_getObjValD(v_j_1916_, v_k_1917_);
                v___x_1933_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__2;
                lean_inc(v___x_1932_);
                v___x_1934_ = l_Lean_Json_getObjVal_x3f(v___x_1932_, v___x_1933_);
                if lean_obj_tag(v___x_1934_) == 0 {
                    lean_dec(v___x_1932_);
                    v_a_1935_ = lean_ctor_get(v___x_1934_, 0);
                    v_isSharedCheck_1942_ = (!lean_is_exclusive(v___x_1934_)) as u8;
                    if v_isSharedCheck_1942_ == 0 {
                        v___x_1937_ = v___x_1934_;
                        v_isShared_1938_ = v_isSharedCheck_1942_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_1935_);
                        lean_dec(v___x_1934_);
                        v___x_1937_ = lean_box(0);
                        v_isShared_1938_ = v_isSharedCheck_1942_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_1943_ = lean_ctor_get(v___x_1934_, 0);
                    lean_inc(v_a_1943_);
                    lean_dec_ref_known(v___x_1934_, 1);
                    if lean_obj_tag(v_a_1943_) == 3 {
                        v_s_1944_ = lean_ctor_get(v_a_1943_, 0);
                        lean_inc_ref(v_s_1944_);
                        lean_dec_ref_known(v_a_1943_, 1);
                        v___x_1945_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__3;
                        v___x_1946_ = lean_string_dec_eq(v_s_1944_, v___x_1945_);
                        lean_dec_ref(v_s_1944_);
                        if v___x_1946_ == 0 {
                            lean_dec(v___x_1932_);
                            state = 1;
                            continue;
                        } else {
                            v___x_1947_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__4;
                            lean_inc(v___x_1932_);
                            v___x_1948_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__3(v___x_1932_, v___x_1947_);
                            if lean_obj_tag(v___x_1948_) == 0 {
                                state = 17;
                                continue;
                            } else {
                                v_a_2032_ = lean_ctor_get(v___x_1948_, 0);
                                lean_inc(v_a_2032_);
                                v___x_2033_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__9;
                                lean_inc(v___x_1932_);
                                v___x_2034_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__5(v___x_1932_, v___x_2033_);
                                if lean_obj_tag(v___x_2034_) == 0 {
                                    lean_dec_ref_known(v___x_2034_, 1);
                                    lean_dec(v_a_2032_);
                                    state = 17;
                                    continue;
                                } else {
                                    lean_dec_ref_known(v___x_1948_, 1);
                                    v_a_2035_ = lean_ctor_get(v___x_2034_, 0);
                                    v_isSharedCheck_2056_ = (!lean_is_exclusive(v___x_2034_)) as u8;
                                    if v_isSharedCheck_2056_ == 0 {
                                        v___x_2037_ = v___x_2034_;
                                        v_isShared_2038_ = v_isSharedCheck_2056_;
                                        state = 22;
                                        continue;
                                    } else {
                                        lean_inc(v_a_2035_);
                                        lean_dec(v___x_2034_);
                                        v___x_2037_ = lean_box(0);
                                        v_isShared_2038_ = v_isSharedCheck_2056_;
                                        state = 22;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        lean_dec(v_a_1943_);
                        lean_dec(v___x_1932_);
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1919_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__1;
                return v___x_1919_;
            }
            2 => {
                v___x_1925_ = lean_alloc_ctor(3, 3, (1) as u32);
                lean_ctor_set(v___x_1925_, 0, v___y_1921_);
                lean_ctor_set(v___x_1925_, 1, v___y_1922_);
                lean_ctor_set(v___x_1925_, 2, v___y_1924_);
                lean_ctor_set_uint8(
                    v___x_1925_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___y_1923_,
                );
                v___x_1926_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1926_, 0, v___x_1925_);
                return v___x_1926_;
            }
            3 => {
                v___x_1930_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1930_, 0, v___y_1928_);
                lean_ctor_set(v___x_1930_, 1, v___y_1929_);
                v___x_1931_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1931_, 0, v___x_1930_);
                return v___x_1931_;
            }
            4 => {
                if v_isShared_1938_ == 0 {
                    v___x_1940_ = v___x_1937_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1941_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1941_, 0, v_a_1935_);
                    v___x_1940_ = v_reuseFailAlloc_1941_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1940_;
            }
            6 => {
                if lean_obj_tag(v___x_1948_) == 0 {
                    lean_dec(v___x_1932_);
                    v_a_1950_ = lean_ctor_get(v___x_1948_, 0);
                    v_isSharedCheck_1957_ = (!lean_is_exclusive(v___x_1948_)) as u8;
                    if v_isSharedCheck_1957_ == 0 {
                        v___x_1952_ = v___x_1948_;
                        v_isShared_1953_ = v_isSharedCheck_1957_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_1950_);
                        lean_dec(v___x_1948_);
                        v___x_1952_ = lean_box(0);
                        v_isShared_1953_ = v_isSharedCheck_1957_;
                        state = 7;
                        continue;
                    }
                } else {
                    v_a_1958_ = lean_ctor_get(v___x_1948_, 0);
                    lean_inc(v_a_1958_);
                    lean_dec_ref_known(v___x_1948_, 1);
                    v___x_1959_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__5;
                    v___x_1960_ = l_Lean_Json_getObjVal_x3f(v___x_1932_, v___x_1959_);
                    if lean_obj_tag(v___x_1960_) == 0 {
                        lean_dec(v_a_1958_);
                        v_a_1961_ = lean_ctor_get(v___x_1960_, 0);
                        v_isSharedCheck_1968_ = (!lean_is_exclusive(v___x_1960_)) as u8;
                        if v_isSharedCheck_1968_ == 0 {
                            v___x_1963_ = v___x_1960_;
                            v_isShared_1964_ = v_isSharedCheck_1968_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_1961_);
                            lean_dec(v___x_1960_);
                            v___x_1963_ = lean_box(0);
                            v_isShared_1964_ = v_isSharedCheck_1968_;
                            state = 9;
                            continue;
                        }
                    } else {
                        v_a_1969_ = lean_ctor_get(v___x_1960_, 0);
                        lean_inc_n(v_a_1969_, 2);
                        lean_dec_ref_known(v___x_1960_, 1);
                        v___x_1970_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__6;
                        v___x_1971_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4(v_a_1969_, v___x_1970_);
                        if lean_obj_tag(v___x_1971_) == 0 {
                            lean_dec(v_a_1969_);
                            lean_dec(v_a_1958_);
                            v_a_1972_ = lean_ctor_get(v___x_1971_, 0);
                            v_isSharedCheck_1979_ = (!lean_is_exclusive(v___x_1971_)) as u8;
                            if v_isSharedCheck_1979_ == 0 {
                                v___x_1974_ = v___x_1971_;
                                v_isShared_1975_ = v_isSharedCheck_1979_;
                                state = 11;
                                continue;
                            } else {
                                lean_inc(v_a_1972_);
                                lean_dec(v___x_1971_);
                                v___x_1974_ = lean_box(0);
                                v_isShared_1975_ = v_isSharedCheck_1979_;
                                state = 11;
                                continue;
                            }
                        } else {
                            v_a_1980_ = lean_ctor_get(v___x_1971_, 0);
                            lean_inc(v_a_1980_);
                            lean_dec_ref_known(v___x_1971_, 1);
                            v___x_1981_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__7;
                            lean_inc(v_a_1969_);
                            v___x_1982_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__5(v_a_1969_, v___x_1981_);
                            if lean_obj_tag(v___x_1982_) == 0 {
                                lean_dec(v_a_1980_);
                                lean_dec(v_a_1969_);
                                lean_dec(v_a_1958_);
                                v_a_1983_ = lean_ctor_get(v___x_1982_, 0);
                                v_isSharedCheck_1990_ = (!lean_is_exclusive(v___x_1982_)) as u8;
                                if v_isSharedCheck_1990_ == 0 {
                                    v___x_1985_ = v___x_1982_;
                                    v_isShared_1986_ = v_isSharedCheck_1990_;
                                    state = 13;
                                    continue;
                                } else {
                                    lean_inc(v_a_1983_);
                                    lean_dec(v___x_1982_);
                                    v___x_1985_ = lean_box(0);
                                    v_isShared_1986_ = v_isSharedCheck_1990_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                v_a_1991_ = lean_ctor_get(v___x_1982_, 0);
                                lean_inc(v_a_1991_);
                                lean_dec_ref_known(v___x_1982_, 1);
                                v___x_1992_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__8;
                                v___x_1993_ = l_Lean_Json_getObjVal_x3f(v_a_1969_, v___x_1992_);
                                if lean_obj_tag(v___x_1993_) == 0 {
                                    lean_dec_ref_known(v___x_1993_, 1);
                                    v___x_1994_ = lean_box(0);
                                    v___x_1995_ = (lean_unbox(v_a_1980_) as u8);
                                    lean_dec(v_a_1980_);
                                    v___y_1921_ = v_a_1958_;
                                    v___y_1922_ = v_a_1991_;
                                    v___y_1923_ = v___x_1995_;
                                    v___y_1924_ = v___x_1994_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_a_1996_ = lean_ctor_get(v___x_1993_, 0);
                                    v_isSharedCheck_2004_ = (!lean_is_exclusive(v___x_1993_)) as u8;
                                    if v_isSharedCheck_2004_ == 0 {
                                        v___x_1998_ = v___x_1993_;
                                        v_isShared_1999_ = v_isSharedCheck_2004_;
                                        state = 15;
                                        continue;
                                    } else {
                                        lean_inc(v_a_1996_);
                                        lean_dec(v___x_1993_);
                                        v___x_1998_ = lean_box(0);
                                        v_isShared_1999_ = v_isSharedCheck_2004_;
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
                if v_isShared_1953_ == 0 {
                    v___x_1955_ = v___x_1952_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1956_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_a_1950_);
                    v___x_1955_ = v_reuseFailAlloc_1956_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1955_;
            }
            9 => {
                if v_isShared_1964_ == 0 {
                    v___x_1966_ = v___x_1963_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1967_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1967_, 0, v_a_1961_);
                    v___x_1966_ = v_reuseFailAlloc_1967_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1966_;
            }
            11 => {
                if v_isShared_1975_ == 0 {
                    v___x_1977_ = v___x_1974_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1978_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_a_1972_);
                    v___x_1977_ = v_reuseFailAlloc_1978_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1977_;
            }
            13 => {
                if v_isShared_1986_ == 0 {
                    v___x_1988_ = v___x_1985_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1989_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_a_1983_);
                    v___x_1988_ = v_reuseFailAlloc_1989_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_1988_;
            }
            15 => {
                if v_isShared_1999_ == 0 {
                    v___x_2001_ = v___x_1998_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2003_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2003_, 0, v_a_1996_);
                    v___x_2001_ = v_reuseFailAlloc_2003_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___x_2002_ = (lean_unbox(v_a_1980_) as u8);
                lean_dec(v_a_1980_);
                v___y_1921_ = v_a_1958_;
                v___y_1922_ = v_a_1991_;
                v___y_1923_ = v___x_2002_;
                v___y_1924_ = v___x_2001_;
                state = 2;
                continue;
            }
            17 => {
                v___x_2006_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__9;
                lean_inc(v___x_1932_);
                v___x_2007_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__5(v___x_1932_, v___x_2006_);
                if lean_obj_tag(v___x_2007_) == 0 {
                    lean_dec_ref_known(v___x_2007_, 1);
                    if lean_obj_tag(v___x_1948_) == 0 {
                        state = 6;
                        continue;
                    } else {
                        v_a_2008_ = lean_ctor_get(v___x_1948_, 0);
                        lean_inc(v_a_2008_);
                        v___x_2009_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__10;
                        lean_inc(v___x_1932_);
                        v___x_2010_ = l_Lean_Json_getObjVal_x3f(v___x_1932_, v___x_2009_);
                        if lean_obj_tag(v___x_2010_) == 0 {
                            lean_dec_ref_known(v___x_2010_, 1);
                            lean_dec(v_a_2008_);
                            state = 6;
                            continue;
                        } else {
                            lean_dec_ref_known(v___x_1948_, 1);
                            lean_dec(v___x_1932_);
                            v_a_2011_ = lean_ctor_get(v___x_2010_, 0);
                            v_isSharedCheck_2019_ = (!lean_is_exclusive(v___x_2010_)) as u8;
                            if v_isSharedCheck_2019_ == 0 {
                                v___x_2013_ = v___x_2010_;
                                v_isShared_2014_ = v_isSharedCheck_2019_;
                                state = 18;
                                continue;
                            } else {
                                lean_inc(v_a_2011_);
                                lean_dec(v___x_2010_);
                                v___x_2013_ = lean_box(0);
                                v_isShared_2014_ = v_isSharedCheck_2019_;
                                state = 18;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v___x_1948_);
                    v_a_2020_ = lean_ctor_get(v___x_2007_, 0);
                    lean_inc(v_a_2020_);
                    lean_dec_ref_known(v___x_2007_, 1);
                    v___x_2021_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__11;
                    v___x_2022_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__6(v___x_1932_, v___x_2021_);
                    if lean_obj_tag(v___x_2022_) == 0 {
                        lean_dec_ref_known(v___x_2022_, 1);
                        v___x_2023_ = lean_box(0);
                        v___y_1928_ = v_a_2020_;
                        v___y_1929_ = v___x_2023_;
                        state = 3;
                        continue;
                    } else {
                        v_a_2024_ = lean_ctor_get(v___x_2022_, 0);
                        v_isSharedCheck_2031_ = (!lean_is_exclusive(v___x_2022_)) as u8;
                        if v_isSharedCheck_2031_ == 0 {
                            v___x_2026_ = v___x_2022_;
                            v_isShared_2027_ = v_isSharedCheck_2031_;
                            state = 20;
                            continue;
                        } else {
                            lean_inc(v_a_2024_);
                            lean_dec(v___x_2022_);
                            v___x_2026_ = lean_box(0);
                            v_isShared_2027_ = v_isSharedCheck_2031_;
                            state = 20;
                            continue;
                        }
                    }
                }
            }
            18 => {
                v___x_2015_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2015_, 0, v_a_2008_);
                lean_ctor_set(v___x_2015_, 1, v_a_2011_);
                if v_isShared_2014_ == 0 {
                    lean_ctor_set(v___x_2013_, 0, v___x_2015_);
                    v___x_2017_ = v___x_2013_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2018_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2018_, 0, v___x_2015_);
                    v___x_2017_ = v_reuseFailAlloc_2018_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_2017_;
            }
            20 => {
                if v_isShared_2027_ == 0 {
                    v___x_2029_ = v___x_2026_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_2030_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2030_, 0, v_a_2024_);
                    v___x_2029_ = v_reuseFailAlloc_2030_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v___y_1928_ = v_a_2020_;
                v___y_1929_ = v___x_2029_;
                state = 3;
                continue;
            }
            22 => {
                v___x_2045_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__11;
                v___x_2046_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__6(v___x_1932_, v___x_2045_);
                if lean_obj_tag(v___x_2046_) == 0 {
                    lean_dec_ref_known(v___x_2046_, 1);
                    v___x_2047_ = lean_box(0);
                    v___y_2040_ = v___x_2047_;
                    state = 23;
                    continue;
                } else {
                    v_a_2048_ = lean_ctor_get(v___x_2046_, 0);
                    v_isSharedCheck_2055_ = (!lean_is_exclusive(v___x_2046_)) as u8;
                    if v_isSharedCheck_2055_ == 0 {
                        v___x_2050_ = v___x_2046_;
                        v_isShared_2051_ = v_isSharedCheck_2055_;
                        state = 25;
                        continue;
                    } else {
                        lean_inc(v_a_2048_);
                        lean_dec(v___x_2046_);
                        v___x_2050_ = lean_box(0);
                        v_isShared_2051_ = v_isSharedCheck_2055_;
                        state = 25;
                        continue;
                    }
                }
            }
            23 => {
                v___x_2041_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_2041_, 0, v_a_2032_);
                lean_ctor_set(v___x_2041_, 1, v_a_2035_);
                lean_ctor_set(v___x_2041_, 2, v___y_2040_);
                if v_isShared_2038_ == 0 {
                    lean_ctor_set(v___x_2037_, 0, v___x_2041_);
                    v___x_2043_ = v___x_2037_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_2044_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2044_, 0, v___x_2041_);
                    v___x_2043_ = v_reuseFailAlloc_2044_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_2043_;
            }
            25 => {
                if v_isShared_2051_ == 0 {
                    v___x_2053_ = v___x_2050_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_2054_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_a_2048_);
                    v___x_2053_ = v_reuseFailAlloc_2054_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                v___y_2040_ = v___x_2053_;
                state = 23;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___boxed(
    mut v_j_2057_: *mut LeanObject,
    mut v_k_2058_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2059_: *mut LeanObject = core::ptr::null_mut();
    v_res_2059_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3(v_j_2057_, v_k_2058_);
    lean_dec_ref(v_k_2058_);
    return v_res_2059_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__15()
-> *mut LeanObject {
    let mut v___x_2093_: u8 = 0;
    let mut v___x_2094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: *mut LeanObject = core::ptr::null_mut();
    v___x_2093_ = 1;
    v___x_2094_ = l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__14;
    v___x_2095_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2094_, v___x_2093_);
    return v___x_2095_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__16()
-> *mut LeanObject {
    let mut v___x_2096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut LeanObject = core::ptr::null_mut();
    v___x_2096_ = l_Lean_Server_Logging_LogConfig_ofLspLogConfig___closed__3;
    v___x_2097_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__15), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__15_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__15);
    v___x_2098_ = lean_string_append(v___x_2097_, v___x_2096_);
    return v___x_2098_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__18()
-> *mut LeanObject {
    let mut v___x_2101_: u8 = 0;
    let mut v___x_2102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut LeanObject = core::ptr::null_mut();
    v___x_2101_ = 1;
    v___x_2102_ = l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__17;
    v___x_2103_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2102_, v___x_2101_);
    return v___x_2103_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__19()
-> *mut LeanObject {
    let mut v___x_2104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut LeanObject = core::ptr::null_mut();
    v___x_2104_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__18), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__18_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__18);
    v___x_2105_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__16), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__16_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__16);
    v___x_2106_ = lean_string_append(v___x_2105_, v___x_2104_);
    return v___x_2106_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__21()
-> *mut LeanObject {
    let mut v___x_2108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut LeanObject = core::ptr::null_mut();
    v___x_2108_ = l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__20;
    v___x_2109_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__19), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__19_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__19);
    v___x_2110_ = lean_string_append(v___x_2109_, v___x_2108_);
    return v___x_2110_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__24()
-> *mut LeanObject {
    let mut v___x_2114_: u8 = 0;
    let mut v___x_2115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut LeanObject = core::ptr::null_mut();
    v___x_2114_ = 1;
    v___x_2115_ = l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__23;
    v___x_2116_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2115_, v___x_2114_);
    return v___x_2116_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__25()
-> *mut LeanObject {
    let mut v___x_2117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut LeanObject = core::ptr::null_mut();
    v___x_2117_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__24), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__24_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__24);
    v___x_2118_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__16), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__16_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__16);
    v___x_2119_ = lean_string_append(v___x_2118_, v___x_2117_);
    return v___x_2119_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__26()
-> *mut LeanObject {
    let mut v___x_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut LeanObject = core::ptr::null_mut();
    v___x_2120_ = l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__20;
    v___x_2121_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__25), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__25_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__25);
    v___x_2122_ = lean_string_append(v___x_2121_, v___x_2120_);
    return v___x_2122_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__29()
-> *mut LeanObject {
    let mut v___x_2126_: u8 = 0;
    let mut v___x_2127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut LeanObject = core::ptr::null_mut();
    v___x_2126_ = 1;
    v___x_2127_ = l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__28;
    v___x_2128_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2127_, v___x_2126_);
    return v___x_2128_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__30()
-> *mut LeanObject {
    let mut v___x_2129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut LeanObject = core::ptr::null_mut();
    v___x_2129_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__29), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__29_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__29);
    v___x_2130_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__16), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__16_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__16);
    v___x_2131_ = lean_string_append(v___x_2130_, v___x_2129_);
    return v___x_2131_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__31()
-> *mut LeanObject {
    let mut v___x_2132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut LeanObject = core::ptr::null_mut();
    v___x_2132_ = l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__20;
    v___x_2133_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__30), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__30_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__30);
    v___x_2134_ = lean_string_append(v___x_2133_, v___x_2132_);
    return v___x_2134_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__34()
-> *mut LeanObject {
    let mut v___x_2138_: u8 = 0;
    let mut v___x_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut LeanObject = core::ptr::null_mut();
    v___x_2138_ = 1;
    v___x_2139_ = l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__33;
    v___x_2140_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2139_, v___x_2138_);
    return v___x_2140_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__35()
-> *mut LeanObject {
    let mut v___x_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut LeanObject = core::ptr::null_mut();
    v___x_2141_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__34), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__34_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__34);
    v___x_2142_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__16), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__16_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__16);
    v___x_2143_ = lean_string_append(v___x_2142_, v___x_2141_);
    return v___x_2143_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__36()
-> *mut LeanObject {
    let mut v___x_2144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut LeanObject = core::ptr::null_mut();
    v___x_2144_ = l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__20;
    v___x_2145_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__35), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__35_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__35);
    v___x_2146_ = lean_string_append(v___x_2145_, v___x_2144_);
    return v___x_2146_;
}
pub unsafe fn l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson(
    mut v_json_2147_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2153_: u8 = 0;
    let mut v___x_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2159_: u8 = 0;
    let mut v_a_2160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2163_: u8 = 0;
    let mut v___x_2165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2167_: u8 = 0;
    let mut v_a_2168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2174_: u8 = 0;
    let mut v___x_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2180_: u8 = 0;
    let mut v_a_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2184_: u8 = 0;
    let mut v___x_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2188_: u8 = 0;
    let mut v_a_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2195_: u8 = 0;
    let mut v___x_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2201_: u8 = 0;
    let mut v_a_2202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2205_: u8 = 0;
    let mut v___x_2207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2209_: u8 = 0;
    let mut v_a_2210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2216_: u8 = 0;
    let mut v___x_2217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2222_: u8 = 0;
    let mut v_a_2223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2226_: u8 = 0;
    let mut v___x_2228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2230_: u8 = 0;
    let mut v_a_2231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2234_: u8 = 0;
    let mut v___x_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: u8 = 0;
    let mut v___x_2237_: u8 = 0;
    let mut v___x_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2241_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2148_ = l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__0;
                lean_inc(v_json_2147_);
                v___x_2149_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__0(v_json_2147_, v___x_2148_);
                if lean_obj_tag(v___x_2149_) == 0 {
                    lean_dec(v_json_2147_);
                    v_a_2150_ = lean_ctor_get(v___x_2149_, 0);
                    v_isSharedCheck_2159_ = (!lean_is_exclusive(v___x_2149_)) as u8;
                    if v_isSharedCheck_2159_ == 0 {
                        v___x_2152_ = v___x_2149_;
                        v_isShared_2153_ = v_isSharedCheck_2159_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2150_);
                        lean_dec(v___x_2149_);
                        v___x_2152_ = lean_box(0);
                        v_isShared_2153_ = v_isSharedCheck_2159_;
                        state = 1;
                        continue;
                    }
                } else {
                    if lean_obj_tag(v___x_2149_) == 0 {
                        lean_dec(v_json_2147_);
                        v_a_2160_ = lean_ctor_get(v___x_2149_, 0);
                        v_isSharedCheck_2167_ = (!lean_is_exclusive(v___x_2149_)) as u8;
                        if v_isSharedCheck_2167_ == 0 {
                            v___x_2162_ = v___x_2149_;
                            v_isShared_2163_ = v_isSharedCheck_2167_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2160_);
                            lean_dec(v___x_2149_);
                            v___x_2162_ = lean_box(0);
                            v_isShared_2163_ = v_isSharedCheck_2167_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_2168_ = lean_ctor_get(v___x_2149_, 0);
                        lean_inc(v_a_2168_);
                        lean_dec_ref_known(v___x_2149_, 1);
                        v___x_2169_ = l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__22;
                        lean_inc(v_json_2147_);
                        v___x_2170_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__1(v_json_2147_, v___x_2169_);
                        if lean_obj_tag(v___x_2170_) == 0 {
                            lean_dec(v_a_2168_);
                            lean_dec(v_json_2147_);
                            v_a_2171_ = lean_ctor_get(v___x_2170_, 0);
                            v_isSharedCheck_2180_ = (!lean_is_exclusive(v___x_2170_)) as u8;
                            if v_isSharedCheck_2180_ == 0 {
                                v___x_2173_ = v___x_2170_;
                                v_isShared_2174_ = v_isSharedCheck_2180_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_2171_);
                                lean_dec(v___x_2170_);
                                v___x_2173_ = lean_box(0);
                                v_isShared_2174_ = v_isSharedCheck_2180_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if lean_obj_tag(v___x_2170_) == 0 {
                                lean_dec(v_a_2168_);
                                lean_dec(v_json_2147_);
                                v_a_2181_ = lean_ctor_get(v___x_2170_, 0);
                                v_isSharedCheck_2188_ = (!lean_is_exclusive(v___x_2170_)) as u8;
                                if v_isSharedCheck_2188_ == 0 {
                                    v___x_2183_ = v___x_2170_;
                                    v_isShared_2184_ = v_isSharedCheck_2188_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_2181_);
                                    lean_dec(v___x_2170_);
                                    v___x_2183_ = lean_box(0);
                                    v_isShared_2184_ = v_isSharedCheck_2188_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_2189_ = lean_ctor_get(v___x_2170_, 0);
                                lean_inc(v_a_2189_);
                                lean_dec_ref_known(v___x_2170_, 1);
                                v___x_2190_ = l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__27;
                                lean_inc(v_json_2147_);
                                v___x_2191_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__2(v_json_2147_, v___x_2190_);
                                if lean_obj_tag(v___x_2191_) == 0 {
                                    lean_dec(v_a_2189_);
                                    lean_dec(v_a_2168_);
                                    lean_dec(v_json_2147_);
                                    v_a_2192_ = lean_ctor_get(v___x_2191_, 0);
                                    v_isSharedCheck_2201_ = (!lean_is_exclusive(v___x_2191_)) as u8;
                                    if v_isSharedCheck_2201_ == 0 {
                                        v___x_2194_ = v___x_2191_;
                                        v_isShared_2195_ = v_isSharedCheck_2201_;
                                        state = 9;
                                        continue;
                                    } else {
                                        lean_inc(v_a_2192_);
                                        lean_dec(v___x_2191_);
                                        v___x_2194_ = lean_box(0);
                                        v_isShared_2195_ = v_isSharedCheck_2201_;
                                        state = 9;
                                        continue;
                                    }
                                } else {
                                    if lean_obj_tag(v___x_2191_) == 0 {
                                        lean_dec(v_a_2189_);
                                        lean_dec(v_a_2168_);
                                        lean_dec(v_json_2147_);
                                        v_a_2202_ = lean_ctor_get(v___x_2191_, 0);
                                        v_isSharedCheck_2209_ =
                                            (!lean_is_exclusive(v___x_2191_)) as u8;
                                        if v_isSharedCheck_2209_ == 0 {
                                            v___x_2204_ = v___x_2191_;
                                            v_isShared_2205_ = v_isSharedCheck_2209_;
                                            state = 11;
                                            continue;
                                        } else {
                                            lean_inc(v_a_2202_);
                                            lean_dec(v___x_2191_);
                                            v___x_2204_ = lean_box(0);
                                            v_isShared_2205_ = v_isSharedCheck_2209_;
                                            state = 11;
                                            continue;
                                        }
                                    } else {
                                        v_a_2210_ = lean_ctor_get(v___x_2191_, 0);
                                        lean_inc(v_a_2210_);
                                        lean_dec_ref_known(v___x_2191_, 1);
                                        v___x_2211_ = l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__32;
                                        v___x_2212_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3(v_json_2147_, v___x_2211_);
                                        if lean_obj_tag(v___x_2212_) == 0 {
                                            lean_dec(v_a_2210_);
                                            lean_dec(v_a_2189_);
                                            lean_dec(v_a_2168_);
                                            v_a_2213_ = lean_ctor_get(v___x_2212_, 0);
                                            v_isSharedCheck_2222_ =
                                                (!lean_is_exclusive(v___x_2212_)) as u8;
                                            if v_isSharedCheck_2222_ == 0 {
                                                v___x_2215_ = v___x_2212_;
                                                v_isShared_2216_ = v_isSharedCheck_2222_;
                                                state = 13;
                                                continue;
                                            } else {
                                                lean_inc(v_a_2213_);
                                                lean_dec(v___x_2212_);
                                                v___x_2215_ = lean_box(0);
                                                v_isShared_2216_ = v_isSharedCheck_2222_;
                                                state = 13;
                                                continue;
                                            }
                                        } else {
                                            if lean_obj_tag(v___x_2212_) == 0 {
                                                lean_dec(v_a_2210_);
                                                lean_dec(v_a_2189_);
                                                lean_dec(v_a_2168_);
                                                v_a_2223_ = lean_ctor_get(v___x_2212_, 0);
                                                v_isSharedCheck_2230_ =
                                                    (!lean_is_exclusive(v___x_2212_)) as u8;
                                                if v_isSharedCheck_2230_ == 0 {
                                                    v___x_2225_ = v___x_2212_;
                                                    v_isShared_2226_ = v_isSharedCheck_2230_;
                                                    state = 15;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_2223_);
                                                    lean_dec(v___x_2212_);
                                                    v___x_2225_ = lean_box(0);
                                                    v_isShared_2226_ = v_isSharedCheck_2230_;
                                                    state = 15;
                                                    continue;
                                                }
                                            } else {
                                                v_a_2231_ = lean_ctor_get(v___x_2212_, 0);
                                                v_isSharedCheck_2241_ =
                                                    (!lean_is_exclusive(v___x_2212_)) as u8;
                                                if v_isSharedCheck_2241_ == 0 {
                                                    v___x_2233_ = v___x_2212_;
                                                    v_isShared_2234_ = v_isSharedCheck_2241_;
                                                    state = 17;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_2231_);
                                                    lean_dec(v___x_2212_);
                                                    v___x_2233_ = lean_box(0);
                                                    v_isShared_2234_ = v_isSharedCheck_2241_;
                                                    state = 17;
                                                    continue;
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_2154_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__21), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__21_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__21);
                v___x_2155_ = lean_string_append(v___x_2154_, v_a_2150_);
                lean_dec(v_a_2150_);
                if v_isShared_2153_ == 0 {
                    lean_ctor_set(v___x_2152_, 0, v___x_2155_);
                    v___x_2157_ = v___x_2152_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2158_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2158_, 0, v___x_2155_);
                    v___x_2157_ = v_reuseFailAlloc_2158_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2157_;
            }
            3 => {
                if v_isShared_2163_ == 0 {
                    lean_ctor_set_tag(v___x_2162_, 0);
                    v___x_2165_ = v___x_2162_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2166_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2166_, 0, v_a_2160_);
                    v___x_2165_ = v_reuseFailAlloc_2166_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2165_;
            }
            5 => {
                v___x_2175_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__26), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__26_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__26);
                v___x_2176_ = lean_string_append(v___x_2175_, v_a_2171_);
                lean_dec(v_a_2171_);
                if v_isShared_2174_ == 0 {
                    lean_ctor_set(v___x_2173_, 0, v___x_2176_);
                    v___x_2178_ = v___x_2173_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2179_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2179_, 0, v___x_2176_);
                    v___x_2178_ = v_reuseFailAlloc_2179_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2178_;
            }
            7 => {
                if v_isShared_2184_ == 0 {
                    lean_ctor_set_tag(v___x_2183_, 0);
                    v___x_2186_ = v___x_2183_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2187_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_a_2181_);
                    v___x_2186_ = v_reuseFailAlloc_2187_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2186_;
            }
            9 => {
                v___x_2196_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__31), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__31_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__31);
                v___x_2197_ = lean_string_append(v___x_2196_, v_a_2192_);
                lean_dec(v_a_2192_);
                if v_isShared_2195_ == 0 {
                    lean_ctor_set(v___x_2194_, 0, v___x_2197_);
                    v___x_2199_ = v___x_2194_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2200_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2200_, 0, v___x_2197_);
                    v___x_2199_ = v_reuseFailAlloc_2200_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2199_;
            }
            11 => {
                if v_isShared_2205_ == 0 {
                    lean_ctor_set_tag(v___x_2204_, 0);
                    v___x_2207_ = v___x_2204_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2208_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2208_, 0, v_a_2202_);
                    v___x_2207_ = v_reuseFailAlloc_2208_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2207_;
            }
            13 => {
                v___x_2217_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__36), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__36_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__36);
                v___x_2218_ = lean_string_append(v___x_2217_, v_a_2213_);
                lean_dec(v_a_2213_);
                if v_isShared_2216_ == 0 {
                    lean_ctor_set(v___x_2215_, 0, v___x_2218_);
                    v___x_2220_ = v___x_2215_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2221_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2221_, 0, v___x_2218_);
                    v___x_2220_ = v_reuseFailAlloc_2221_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2220_;
            }
            15 => {
                if v_isShared_2226_ == 0 {
                    lean_ctor_set_tag(v___x_2225_, 0);
                    v___x_2228_ = v___x_2225_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2229_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_a_2223_);
                    v___x_2228_ = v_reuseFailAlloc_2229_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2228_;
            }
            17 => {
                v___x_2235_ = lean_alloc_ctor(0, 2, (2) as u32);
                lean_ctor_set(v___x_2235_, 0, v_a_2168_);
                lean_ctor_set(v___x_2235_, 1, v_a_2231_);
                v___x_2236_ = (lean_unbox(v_a_2189_) as u8);
                lean_dec(v_a_2189_);
                lean_ctor_set_uint8(
                    v___x_2235_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___x_2236_,
                );
                v___x_2237_ = (lean_unbox(v_a_2210_) as u8);
                lean_dec(v_a_2210_);
                lean_ctor_set_uint8(
                    v___x_2235_,
                    (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                    v___x_2237_,
                );
                if v_isShared_2234_ == 0 {
                    lean_ctor_set(v___x_2233_, 0, v___x_2235_);
                    v___x_2239_ = v___x_2233_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2240_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2240_, 0, v___x_2235_);
                    v___x_2239_ = v_reuseFailAlloc_2240_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_2239_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_opt___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson_spec__1(
    mut v_k_2244_: *mut LeanObject,
    mut v_x_2245_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2245_) == 0 {
        let mut v___x_2246_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_k_2244_);
        v___x_2246_ = lean_box(0);
        return v___x_2246_;
    } else {
        let mut v_val_2247_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2248_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2249_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2250_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2251_: *mut LeanObject = core::ptr::null_mut();
        v_val_2247_ = lean_ctor_get(v_x_2245_, 0);
        lean_inc(v_val_2247_);
        lean_dec_ref_known(v_x_2245_, 1);
        v___x_2248_ = l_Lean_Json_Structured_toJson(v_val_2247_);
        v___x_2249_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2249_, 0, v_k_2244_);
        lean_ctor_set(v___x_2249_, 1, v___x_2248_);
        v___x_2250_ = lean_box(0);
        v___x_2251_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_2251_, 0, v___x_2249_);
        lean_ctor_set(v___x_2251_, 1, v___x_2250_);
        return v___x_2251_;
    }
}
pub unsafe fn l_Lean_Json_opt___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson_spec__2(
    mut v_k_2252_: *mut LeanObject,
    mut v_x_2253_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2253_) == 0 {
        let mut v___x_2254_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_k_2252_);
        v___x_2254_ = lean_box(0);
        return v___x_2254_;
    } else {
        let mut v_val_2255_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2256_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2257_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2258_: *mut LeanObject = core::ptr::null_mut();
        v_val_2255_ = lean_ctor_get(v_x_2253_, 0);
        lean_inc(v_val_2255_);
        v___x_2256_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2256_, 0, v_k_2252_);
        lean_ctor_set(v___x_2256_, 1, v_val_2255_);
        v___x_2257_ = lean_box(0);
        v___x_2258_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_2258_, 0, v___x_2256_);
        lean_ctor_set(v___x_2258_, 1, v___x_2257_);
        return v___x_2258_;
    }
}
pub unsafe fn l_Lean_Json_opt___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson_spec__2___boxed(
    mut v_k_2259_: *mut LeanObject,
    mut v_x_2260_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2261_: *mut LeanObject = core::ptr::null_mut();
    v_res_2261_ = l_Lean_Json_opt___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson_spec__2(v_k_2259_, v_x_2260_);
    lean_dec(v_x_2260_);
    return v_res_2261_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson_spec__0(
    mut v_a_2262_: *mut LeanObject,
    mut v_a_2263_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_2262_) == 0 {
                    v___x_2264_ = lean_array_to_list(v_a_2263_);
                    return v___x_2264_;
                } else {
                    v_head_2265_ = lean_ctor_get(v_a_2262_, 0);
                    lean_inc(v_head_2265_);
                    v_tail_2266_ = lean_ctor_get(v_a_2262_, 1);
                    lean_inc(v_tail_2266_);
                    lean_dec_ref_known(v_a_2262_, 2);
                    v___x_2267_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(
                        v_a_2263_,
                        v_head_2265_,
                    );
                    v_a_2262_ = v_tail_2266_;
                    v_a_2263_ = v___x_2267_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__3()
-> *mut LeanObject {
    let mut v___x_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut LeanObject = core::ptr::null_mut();
    v___x_2276_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__3), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__3_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__3);
    v___x_2277_ = l_Lean_JsonNumber_fromInt(v___x_2276_);
    return v___x_2277_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__4()
-> *mut LeanObject {
    let mut v___x_2278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut LeanObject = core::ptr::null_mut();
    v___x_2278_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__3_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__3);
    v___x_2279_ = lean_alloc_ctor(2, 1, (0) as u32);
    lean_ctor_set(v___x_2279_, 0, v___x_2278_);
    return v___x_2279_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__5()
-> *mut LeanObject {
    let mut v___x_2280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut LeanObject = core::ptr::null_mut();
    v___x_2280_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__5), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__5_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__5);
    v___x_2281_ = l_Lean_JsonNumber_fromInt(v___x_2280_);
    return v___x_2281_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__6()
-> *mut LeanObject {
    let mut v___x_2282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut LeanObject = core::ptr::null_mut();
    v___x_2282_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__5_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__5);
    v___x_2283_ = lean_alloc_ctor(2, 1, (0) as u32);
    lean_ctor_set(v___x_2283_, 0, v___x_2282_);
    return v___x_2283_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__7()
-> *mut LeanObject {
    let mut v___x_2284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut LeanObject = core::ptr::null_mut();
    v___x_2284_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__7), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__7_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__7);
    v___x_2285_ = l_Lean_JsonNumber_fromInt(v___x_2284_);
    return v___x_2285_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__8()
-> *mut LeanObject {
    let mut v___x_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut LeanObject = core::ptr::null_mut();
    v___x_2286_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__7_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__7);
    v___x_2287_ = lean_alloc_ctor(2, 1, (0) as u32);
    lean_ctor_set(v___x_2287_, 0, v___x_2286_);
    return v___x_2287_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__9()
-> *mut LeanObject {
    let mut v___x_2288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut LeanObject = core::ptr::null_mut();
    v___x_2288_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__9), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__9_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__9);
    v___x_2289_ = l_Lean_JsonNumber_fromInt(v___x_2288_);
    return v___x_2289_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__10()
-> *mut LeanObject {
    let mut v___x_2290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut LeanObject = core::ptr::null_mut();
    v___x_2290_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__9_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__9);
    v___x_2291_ = lean_alloc_ctor(2, 1, (0) as u32);
    lean_ctor_set(v___x_2291_, 0, v___x_2290_);
    return v___x_2291_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__11()
-> *mut LeanObject {
    let mut v___x_2292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut LeanObject = core::ptr::null_mut();
    v___x_2292_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__11), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__11_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__11);
    v___x_2293_ = l_Lean_JsonNumber_fromInt(v___x_2292_);
    return v___x_2293_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__12()
-> *mut LeanObject {
    let mut v___x_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut LeanObject = core::ptr::null_mut();
    v___x_2294_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__11_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__11);
    v___x_2295_ = lean_alloc_ctor(2, 1, (0) as u32);
    lean_ctor_set(v___x_2295_, 0, v___x_2294_);
    return v___x_2295_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__13()
-> *mut LeanObject {
    let mut v___x_2296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut LeanObject = core::ptr::null_mut();
    v___x_2296_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__13), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__13_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__13);
    v___x_2297_ = l_Lean_JsonNumber_fromInt(v___x_2296_);
    return v___x_2297_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__14()
-> *mut LeanObject {
    let mut v___x_2298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut LeanObject = core::ptr::null_mut();
    v___x_2298_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__13), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__13_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__13);
    v___x_2299_ = lean_alloc_ctor(2, 1, (0) as u32);
    lean_ctor_set(v___x_2299_, 0, v___x_2298_);
    return v___x_2299_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__15()
-> *mut LeanObject {
    let mut v___x_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut LeanObject = core::ptr::null_mut();
    v___x_2300_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__15), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__15_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__15);
    v___x_2301_ = l_Lean_JsonNumber_fromInt(v___x_2300_);
    return v___x_2301_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__16()
-> *mut LeanObject {
    let mut v___x_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut LeanObject = core::ptr::null_mut();
    v___x_2302_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__15), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__15_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__15);
    v___x_2303_ = lean_alloc_ctor(2, 1, (0) as u32);
    lean_ctor_set(v___x_2303_, 0, v___x_2302_);
    return v___x_2303_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__17()
-> *mut LeanObject {
    let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut LeanObject = core::ptr::null_mut();
    v___x_2304_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__17), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__17_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__17);
    v___x_2305_ = l_Lean_JsonNumber_fromInt(v___x_2304_);
    return v___x_2305_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__18()
-> *mut LeanObject {
    let mut v___x_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut LeanObject = core::ptr::null_mut();
    v___x_2306_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__17), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__17_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__17);
    v___x_2307_ = lean_alloc_ctor(2, 1, (0) as u32);
    lean_ctor_set(v___x_2307_, 0, v___x_2306_);
    return v___x_2307_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__19()
-> *mut LeanObject {
    let mut v___x_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut LeanObject = core::ptr::null_mut();
    v___x_2308_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__19), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__19_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__19);
    v___x_2309_ = l_Lean_JsonNumber_fromInt(v___x_2308_);
    return v___x_2309_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__20()
-> *mut LeanObject {
    let mut v___x_2310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut LeanObject = core::ptr::null_mut();
    v___x_2310_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__19), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__19_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__19);
    v___x_2311_ = lean_alloc_ctor(2, 1, (0) as u32);
    lean_ctor_set(v___x_2311_, 0, v___x_2310_);
    return v___x_2311_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__21()
-> *mut LeanObject {
    let mut v___x_2312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut LeanObject = core::ptr::null_mut();
    v___x_2312_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__21), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__21_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__21);
    v___x_2313_ = l_Lean_JsonNumber_fromInt(v___x_2312_);
    return v___x_2313_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__22()
-> *mut LeanObject {
    let mut v___x_2314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut LeanObject = core::ptr::null_mut();
    v___x_2314_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__21), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__21_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__21);
    v___x_2315_ = lean_alloc_ctor(2, 1, (0) as u32);
    lean_ctor_set(v___x_2315_, 0, v___x_2314_);
    return v___x_2315_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__23()
-> *mut LeanObject {
    let mut v___x_2316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut LeanObject = core::ptr::null_mut();
    v___x_2316_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__23), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__23_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__23);
    v___x_2317_ = l_Lean_JsonNumber_fromInt(v___x_2316_);
    return v___x_2317_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__24()
-> *mut LeanObject {
    let mut v___x_2318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut LeanObject = core::ptr::null_mut();
    v___x_2318_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__23), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__23_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__23);
    v___x_2319_ = lean_alloc_ctor(2, 1, (0) as u32);
    lean_ctor_set(v___x_2319_, 0, v___x_2318_);
    return v___x_2319_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__25()
-> *mut LeanObject {
    let mut v___x_2320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut LeanObject = core::ptr::null_mut();
    v___x_2320_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__25), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__25_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__25);
    v___x_2321_ = l_Lean_JsonNumber_fromInt(v___x_2320_);
    return v___x_2321_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__26()
-> *mut LeanObject {
    let mut v___x_2322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut LeanObject = core::ptr::null_mut();
    v___x_2322_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__25), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__25_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__25);
    v___x_2323_ = lean_alloc_ctor(2, 1, (0) as u32);
    lean_ctor_set(v___x_2323_, 0, v___x_2322_);
    return v___x_2323_;
}
pub unsafe fn l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson(
    mut v_x_2324_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_time_2325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_direction_2326_: u8 = 0;
    let mut v_kind_2327_: u8 = 0;
    let mut v_msg_2328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_method_2359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_x3f_2360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_2373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2376_: u8 = 0;
    let mut v___x_2378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2380_: u8 = 0;
    let mut v_n_2381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2384_: u8 = 0;
    let mut v___x_2386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2388_: u8 = 0;
    let mut v___x_2389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_method_2390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_x3f_2391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2394_: u8 = 0;
    let mut v___x_2395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2403_: u8 = 0;
    let mut v_id_2404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_result_2405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2408_: u8 = 0;
    let mut v___x_2409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_2419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2422_: u8 = 0;
    let mut v___x_2424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2426_: u8 = 0;
    let mut v_n_2427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2430_: u8 = 0;
    let mut v___x_2432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2434_: u8 = 0;
    let mut v___x_2435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2436_: u8 = 0;
    let mut v_id_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_2438_: u8 = 0;
    let mut v_message_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_x3f_2440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_2477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2480_: u8 = 0;
    let mut v___x_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2484_: u8 = 0;
    let mut v_n_2485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2488_: u8 = 0;
    let mut v___x_2490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2492_: u8 = 0;
    let mut v___x_2493_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_time_2325_ = lean_ctor_get(v_x_2324_, 0);
                lean_inc_ref(v_time_2325_);
                v_direction_2326_ = lean_ctor_get_uint8(
                    v_x_2324_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                );
                v_kind_2327_ = lean_ctor_get_uint8(
                    v_x_2324_,
                    (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                );
                v_msg_2328_ = lean_ctor_get(v_x_2324_, 1);
                lean_inc_ref(v_msg_2328_);
                lean_dec_ref(v_x_2324_);
                v___x_2329_ = l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__0;
                v___x_2330_ = l_Std_Time_ZonedDateTime_toISO8601String(v_time_2325_);
                v___x_2331_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_2331_, 0, v___x_2330_);
                v___x_2332_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2332_, 0, v___x_2329_);
                lean_ctor_set(v___x_2332_, 1, v___x_2331_);
                v___x_2333_ = lean_box(0);
                v___x_2334_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2334_, 0, v___x_2332_);
                lean_ctor_set(v___x_2334_, 1, v___x_2333_);
                v___x_2335_ = l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__22;
                v___x_2336_ = l_Lean_JsonRpc_instToJsonMessageDirection_toJson(v_direction_2326_);
                v___x_2337_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2337_, 0, v___x_2335_);
                lean_ctor_set(v___x_2337_, 1, v___x_2336_);
                v___x_2338_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2338_, 0, v___x_2337_);
                lean_ctor_set(v___x_2338_, 1, v___x_2333_);
                v___x_2339_ = l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__27;
                v___x_2340_ = l_Lean_JsonRpc_instToJsonMessageKind_toJson(v_kind_2327_);
                v___x_2341_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2341_, 0, v___x_2339_);
                lean_ctor_set(v___x_2341_, 1, v___x_2340_);
                v___x_2342_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2342_, 0, v___x_2341_);
                lean_ctor_set(v___x_2342_, 1, v___x_2333_);
                v___x_2343_ = l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__32;
                v___x_2344_ = l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__1;
                match lean_obj_tag(v_msg_2328_) {
                    0 => {
                        v_id_2358_ = lean_ctor_get(v_msg_2328_, 0);
                        lean_inc(v_id_2358_);
                        v_method_2359_ = lean_ctor_get(v_msg_2328_, 1);
                        lean_inc_ref(v_method_2359_);
                        v_params_x3f_2360_ = lean_ctor_get(v_msg_2328_, 2);
                        lean_inc(v_params_x3f_2360_);
                        lean_dec_ref_known(v_msg_2328_, 3);
                        v___x_2361_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__4;
                        match lean_obj_tag(v_id_2358_) {
                            0 => {
                                v_s_2373_ = lean_ctor_get(v_id_2358_, 0);
                                v_isSharedCheck_2380_ = (!lean_is_exclusive(v_id_2358_)) as u8;
                                if v_isSharedCheck_2380_ == 0 {
                                    v___x_2375_ = v_id_2358_;
                                    v_isShared_2376_ = v_isSharedCheck_2380_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_inc(v_s_2373_);
                                    lean_dec(v_id_2358_);
                                    v___x_2375_ = lean_box(0);
                                    v_isShared_2376_ = v_isSharedCheck_2380_;
                                    state = 3;
                                    continue;
                                }
                            }
                            1 => {
                                v_n_2381_ = lean_ctor_get(v_id_2358_, 0);
                                v_isSharedCheck_2388_ = (!lean_is_exclusive(v_id_2358_)) as u8;
                                if v_isSharedCheck_2388_ == 0 {
                                    v___x_2383_ = v_id_2358_;
                                    v_isShared_2384_ = v_isSharedCheck_2388_;
                                    state = 5;
                                    continue;
                                } else {
                                    lean_inc(v_n_2381_);
                                    lean_dec(v_id_2358_);
                                    v___x_2383_ = lean_box(0);
                                    v_isShared_2384_ = v_isSharedCheck_2388_;
                                    state = 5;
                                    continue;
                                }
                            }
                            _ => {
                                v___x_2389_ = lean_box(0);
                                v___y_2363_ = v___x_2389_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                    1 => {
                        v_method_2390_ = lean_ctor_get(v_msg_2328_, 0);
                        v_params_x3f_2391_ = lean_ctor_get(v_msg_2328_, 1);
                        v_isSharedCheck_2403_ = (!lean_is_exclusive(v_msg_2328_)) as u8;
                        if v_isSharedCheck_2403_ == 0 {
                            v___x_2393_ = v_msg_2328_;
                            v_isShared_2394_ = v_isSharedCheck_2403_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_params_x3f_2391_);
                            lean_inc(v_method_2390_);
                            lean_dec(v_msg_2328_);
                            v___x_2393_ = lean_box(0);
                            v_isShared_2394_ = v_isSharedCheck_2403_;
                            state = 7;
                            continue;
                        }
                    }
                    2 => {
                        v_id_2404_ = lean_ctor_get(v_msg_2328_, 0);
                        v_result_2405_ = lean_ctor_get(v_msg_2328_, 1);
                        v_isSharedCheck_2436_ = (!lean_is_exclusive(v_msg_2328_)) as u8;
                        if v_isSharedCheck_2436_ == 0 {
                            v___x_2407_ = v_msg_2328_;
                            v_isShared_2408_ = v_isSharedCheck_2436_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_result_2405_);
                            lean_inc(v_id_2404_);
                            lean_dec(v_msg_2328_);
                            v___x_2407_ = lean_box(0);
                            v_isShared_2408_ = v_isSharedCheck_2436_;
                            state = 9;
                            continue;
                        }
                    }
                    _ => {
                        v_id_2437_ = lean_ctor_get(v_msg_2328_, 0);
                        lean_inc(v_id_2437_);
                        v_code_2438_ = lean_ctor_get_uint8(
                            v_msg_2328_,
                            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        );
                        v_message_2439_ = lean_ctor_get(v_msg_2328_, 1);
                        lean_inc_ref(v_message_2439_);
                        v_data_x3f_2440_ = lean_ctor_get(v_msg_2328_, 2);
                        lean_inc(v_data_x3f_2440_);
                        lean_dec_ref_known(v_msg_2328_, 3);
                        v___x_2459_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__4;
                        match lean_obj_tag(v_id_2437_) {
                            0 => {
                                v_s_2477_ = lean_ctor_get(v_id_2437_, 0);
                                v_isSharedCheck_2484_ = (!lean_is_exclusive(v_id_2437_)) as u8;
                                if v_isSharedCheck_2484_ == 0 {
                                    v___x_2479_ = v_id_2437_;
                                    v_isShared_2480_ = v_isSharedCheck_2484_;
                                    state = 18;
                                    continue;
                                } else {
                                    lean_inc(v_s_2477_);
                                    lean_dec(v_id_2437_);
                                    v___x_2479_ = lean_box(0);
                                    v_isShared_2480_ = v_isSharedCheck_2484_;
                                    state = 18;
                                    continue;
                                }
                            }
                            1 => {
                                v_n_2485_ = lean_ctor_get(v_id_2437_, 0);
                                v_isSharedCheck_2492_ = (!lean_is_exclusive(v_id_2437_)) as u8;
                                if v_isSharedCheck_2492_ == 0 {
                                    v___x_2487_ = v_id_2437_;
                                    v_isShared_2488_ = v_isSharedCheck_2492_;
                                    state = 20;
                                    continue;
                                } else {
                                    lean_inc(v_n_2485_);
                                    lean_dec(v_id_2437_);
                                    v___x_2487_ = lean_box(0);
                                    v_isShared_2488_ = v_isSharedCheck_2492_;
                                    state = 20;
                                    continue;
                                }
                            }
                            _ => {
                                v___x_2493_ = lean_box(0);
                                v___y_2461_ = v___x_2493_;
                                state = 17;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_2347_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2347_, 0, v___x_2344_);
                lean_ctor_set(v___x_2347_, 1, v___y_2346_);
                v___x_2348_ = l_Lean_Json_mkObj(v___x_2347_);
                lean_dec_ref_known(v___x_2347_, 2);
                v___x_2349_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2349_, 0, v___x_2343_);
                lean_ctor_set(v___x_2349_, 1, v___x_2348_);
                v___x_2350_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2350_, 0, v___x_2349_);
                lean_ctor_set(v___x_2350_, 1, v___x_2333_);
                v___x_2351_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2351_, 0, v___x_2350_);
                lean_ctor_set(v___x_2351_, 1, v___x_2333_);
                v___x_2352_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2352_, 0, v___x_2342_);
                lean_ctor_set(v___x_2352_, 1, v___x_2351_);
                v___x_2353_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2353_, 0, v___x_2338_);
                lean_ctor_set(v___x_2353_, 1, v___x_2352_);
                v___x_2354_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2354_, 0, v___x_2334_);
                lean_ctor_set(v___x_2354_, 1, v___x_2353_);
                v___x_2355_ = l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__2;
                v___x_2356_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson_spec__0(v___x_2354_, v___x_2355_);
                v___x_2357_ = l_Lean_Json_mkObj(v___x_2356_);
                lean_dec(v___x_2356_);
                return v___x_2357_;
            }
            2 => {
                v___x_2364_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2364_, 0, v___x_2361_);
                lean_ctor_set(v___x_2364_, 1, v___y_2363_);
                v___x_2365_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__9;
                v___x_2366_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_2366_, 0, v_method_2359_);
                v___x_2367_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2367_, 0, v___x_2365_);
                lean_ctor_set(v___x_2367_, 1, v___x_2366_);
                v___x_2368_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2368_, 0, v___x_2367_);
                lean_ctor_set(v___x_2368_, 1, v___x_2333_);
                v___x_2369_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2369_, 0, v___x_2364_);
                lean_ctor_set(v___x_2369_, 1, v___x_2368_);
                v___x_2370_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__11;
                v___x_2371_ = l_Lean_Json_opt___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson_spec__1(v___x_2370_, v_params_x3f_2360_);
                v___x_2372_ = l_List_appendTR___redArg(v___x_2369_, v___x_2371_);
                v___y_2346_ = v___x_2372_;
                state = 1;
                continue;
            }
            3 => {
                if v_isShared_2376_ == 0 {
                    lean_ctor_set_tag(v___x_2375_, 3);
                    v___x_2378_ = v___x_2375_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2379_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_s_2373_);
                    v___x_2378_ = v_reuseFailAlloc_2379_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___y_2363_ = v___x_2378_;
                state = 2;
                continue;
            }
            5 => {
                if v_isShared_2384_ == 0 {
                    lean_ctor_set_tag(v___x_2383_, 2);
                    v___x_2386_ = v___x_2383_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2387_ = lean_alloc_ctor(2, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2387_, 0, v_n_2381_);
                    v___x_2386_ = v_reuseFailAlloc_2387_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___y_2363_ = v___x_2386_;
                state = 2;
                continue;
            }
            7 => {
                v___x_2395_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__9;
                v___x_2396_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_2396_, 0, v_method_2390_);
                if v_isShared_2394_ == 0 {
                    lean_ctor_set_tag(v___x_2393_, 0);
                    lean_ctor_set(v___x_2393_, 1, v___x_2396_);
                    lean_ctor_set(v___x_2393_, 0, v___x_2395_);
                    v___x_2398_ = v___x_2393_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2402_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2402_, 0, v___x_2395_);
                    lean_ctor_set(v_reuseFailAlloc_2402_, 1, v___x_2396_);
                    v___x_2398_ = v_reuseFailAlloc_2402_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2399_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__11;
                v___x_2400_ = l_Lean_Json_opt___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson_spec__1(v___x_2399_, v_params_x3f_2391_);
                v___x_2401_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2401_, 0, v___x_2398_);
                lean_ctor_set(v___x_2401_, 1, v___x_2400_);
                v___y_2346_ = v___x_2401_;
                state = 1;
                continue;
            }
            9 => {
                v___x_2409_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__4;
                match lean_obj_tag(v_id_2404_) {
                    0 => {
                        v_s_2419_ = lean_ctor_get(v_id_2404_, 0);
                        v_isSharedCheck_2426_ = (!lean_is_exclusive(v_id_2404_)) as u8;
                        if v_isSharedCheck_2426_ == 0 {
                            v___x_2421_ = v_id_2404_;
                            v_isShared_2422_ = v_isSharedCheck_2426_;
                            state = 12;
                            continue;
                        } else {
                            lean_inc(v_s_2419_);
                            lean_dec(v_id_2404_);
                            v___x_2421_ = lean_box(0);
                            v_isShared_2422_ = v_isSharedCheck_2426_;
                            state = 12;
                            continue;
                        }
                    }
                    1 => {
                        v_n_2427_ = lean_ctor_get(v_id_2404_, 0);
                        v_isSharedCheck_2434_ = (!lean_is_exclusive(v_id_2404_)) as u8;
                        if v_isSharedCheck_2434_ == 0 {
                            v___x_2429_ = v_id_2404_;
                            v_isShared_2430_ = v_isSharedCheck_2434_;
                            state = 14;
                            continue;
                        } else {
                            lean_inc(v_n_2427_);
                            lean_dec(v_id_2404_);
                            v___x_2429_ = lean_box(0);
                            v_isShared_2430_ = v_isSharedCheck_2434_;
                            state = 14;
                            continue;
                        }
                    }
                    _ => {
                        v___x_2435_ = lean_box(0);
                        v___y_2411_ = v___x_2435_;
                        state = 10;
                        continue;
                    }
                }
            }
            10 => {
                if v_isShared_2408_ == 0 {
                    lean_ctor_set_tag(v___x_2407_, 0);
                    lean_ctor_set(v___x_2407_, 1, v___y_2411_);
                    lean_ctor_set(v___x_2407_, 0, v___x_2409_);
                    v___x_2413_ = v___x_2407_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2418_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2418_, 0, v___x_2409_);
                    lean_ctor_set(v_reuseFailAlloc_2418_, 1, v___y_2411_);
                    v___x_2413_ = v_reuseFailAlloc_2418_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_2414_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__10;
                v___x_2415_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2415_, 0, v___x_2414_);
                lean_ctor_set(v___x_2415_, 1, v_result_2405_);
                v___x_2416_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2416_, 0, v___x_2415_);
                lean_ctor_set(v___x_2416_, 1, v___x_2333_);
                v___x_2417_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2417_, 0, v___x_2413_);
                lean_ctor_set(v___x_2417_, 1, v___x_2416_);
                v___y_2346_ = v___x_2417_;
                state = 1;
                continue;
            }
            12 => {
                if v_isShared_2422_ == 0 {
                    lean_ctor_set_tag(v___x_2421_, 3);
                    v___x_2424_ = v___x_2421_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2425_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2425_, 0, v_s_2419_);
                    v___x_2424_ = v_reuseFailAlloc_2425_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___y_2411_ = v___x_2424_;
                state = 10;
                continue;
            }
            14 => {
                if v_isShared_2430_ == 0 {
                    lean_ctor_set_tag(v___x_2429_, 2);
                    v___x_2432_ = v___x_2429_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2433_ = lean_alloc_ctor(2, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2433_, 0, v_n_2427_);
                    v___x_2432_ = v_reuseFailAlloc_2433_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___y_2411_ = v___x_2432_;
                state = 10;
                continue;
            }
            16 => {
                lean_inc(v___y_2445_);
                lean_inc_ref(v___y_2442_);
                v___x_2446_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2446_, 0, v___y_2442_);
                lean_ctor_set(v___x_2446_, 1, v___y_2445_);
                v___x_2447_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__7;
                v___x_2448_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_2448_, 0, v_message_2439_);
                v___x_2449_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2449_, 0, v___x_2447_);
                lean_ctor_set(v___x_2449_, 1, v___x_2448_);
                v___x_2450_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2450_, 0, v___x_2449_);
                lean_ctor_set(v___x_2450_, 1, v___x_2333_);
                v___x_2451_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2451_, 0, v___x_2446_);
                lean_ctor_set(v___x_2451_, 1, v___x_2450_);
                v___x_2452_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__8;
                v___x_2453_ = l_Lean_Json_opt___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson_spec__2(v___x_2452_, v_data_x3f_2440_);
                lean_dec(v_data_x3f_2440_);
                v___x_2454_ = l_List_appendTR___redArg(v___x_2451_, v___x_2453_);
                v___x_2455_ = l_Lean_Json_mkObj(v___x_2454_);
                lean_dec(v___x_2454_);
                lean_inc_ref(v___y_2443_);
                v___x_2456_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2456_, 0, v___y_2443_);
                lean_ctor_set(v___x_2456_, 1, v___x_2455_);
                v___x_2457_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2457_, 0, v___x_2456_);
                lean_ctor_set(v___x_2457_, 1, v___x_2333_);
                v___x_2458_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2458_, 0, v___y_2444_);
                lean_ctor_set(v___x_2458_, 1, v___x_2457_);
                v___y_2346_ = v___x_2458_;
                state = 1;
                continue;
            }
            17 => {
                v___x_2462_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2462_, 0, v___x_2459_);
                lean_ctor_set(v___x_2462_, 1, v___y_2461_);
                v___x_2463_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__5;
                v___x_2464_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__6;
                match v_code_2438_ {
                    0 => {
                        v___x_2465_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__4_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__4);
                        v___y_2442_ = v___x_2464_;
                        v___y_2443_ = v___x_2463_;
                        v___y_2444_ = v___x_2462_;
                        v___y_2445_ = v___x_2465_;
                        state = 16;
                        continue;
                    }
                    1 => {
                        v___x_2466_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__6_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__6);
                        v___y_2442_ = v___x_2464_;
                        v___y_2443_ = v___x_2463_;
                        v___y_2444_ = v___x_2462_;
                        v___y_2445_ = v___x_2466_;
                        state = 16;
                        continue;
                    }
                    2 => {
                        v___x_2467_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__8_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__8);
                        v___y_2442_ = v___x_2464_;
                        v___y_2443_ = v___x_2463_;
                        v___y_2444_ = v___x_2462_;
                        v___y_2445_ = v___x_2467_;
                        state = 16;
                        continue;
                    }
                    3 => {
                        v___x_2468_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__10_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__10);
                        v___y_2442_ = v___x_2464_;
                        v___y_2443_ = v___x_2463_;
                        v___y_2444_ = v___x_2462_;
                        v___y_2445_ = v___x_2468_;
                        state = 16;
                        continue;
                    }
                    4 => {
                        v___x_2469_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__12), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__12_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__12);
                        v___y_2442_ = v___x_2464_;
                        v___y_2443_ = v___x_2463_;
                        v___y_2444_ = v___x_2462_;
                        v___y_2445_ = v___x_2469_;
                        state = 16;
                        continue;
                    }
                    5 => {
                        v___x_2470_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__14), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__14_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__14);
                        v___y_2442_ = v___x_2464_;
                        v___y_2443_ = v___x_2463_;
                        v___y_2444_ = v___x_2462_;
                        v___y_2445_ = v___x_2470_;
                        state = 16;
                        continue;
                    }
                    6 => {
                        v___x_2471_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__16), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__16_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__16);
                        v___y_2442_ = v___x_2464_;
                        v___y_2443_ = v___x_2463_;
                        v___y_2444_ = v___x_2462_;
                        v___y_2445_ = v___x_2471_;
                        state = 16;
                        continue;
                    }
                    7 => {
                        v___x_2472_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__18), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__18_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__18);
                        v___y_2442_ = v___x_2464_;
                        v___y_2443_ = v___x_2463_;
                        v___y_2444_ = v___x_2462_;
                        v___y_2445_ = v___x_2472_;
                        state = 16;
                        continue;
                    }
                    8 => {
                        v___x_2473_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__20), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__20_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__20);
                        v___y_2442_ = v___x_2464_;
                        v___y_2443_ = v___x_2463_;
                        v___y_2444_ = v___x_2462_;
                        v___y_2445_ = v___x_2473_;
                        state = 16;
                        continue;
                    }
                    9 => {
                        v___x_2474_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__22), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__22_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__22);
                        v___y_2442_ = v___x_2464_;
                        v___y_2443_ = v___x_2463_;
                        v___y_2444_ = v___x_2462_;
                        v___y_2445_ = v___x_2474_;
                        state = 16;
                        continue;
                    }
                    10 => {
                        v___x_2475_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__24), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__24_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__24);
                        v___y_2442_ = v___x_2464_;
                        v___y_2443_ = v___x_2463_;
                        v___y_2444_ = v___x_2462_;
                        v___y_2445_ = v___x_2475_;
                        state = 16;
                        continue;
                    }
                    _ => {
                        v___x_2476_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__26), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__26_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__26);
                        v___y_2442_ = v___x_2464_;
                        v___y_2443_ = v___x_2463_;
                        v___y_2444_ = v___x_2462_;
                        v___y_2445_ = v___x_2476_;
                        state = 16;
                        continue;
                    }
                }
            }
            18 => {
                if v_isShared_2480_ == 0 {
                    lean_ctor_set_tag(v___x_2479_, 3);
                    v___x_2482_ = v___x_2479_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2483_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_s_2477_);
                    v___x_2482_ = v_reuseFailAlloc_2483_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                v___y_2461_ = v___x_2482_;
                state = 17;
                continue;
            }
            20 => {
                if v_isShared_2488_ == 0 {
                    lean_ctor_set_tag(v___x_2487_, 2);
                    v___x_2490_ = v___x_2487_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_2491_ = lean_alloc_ctor(2, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_n_2485_);
                    v___x_2490_ = v_reuseFailAlloc_2491_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v___y_2461_ = v___x_2490_;
                state = 17;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_Logging_writeLogEntry(
    mut v_cfg_2496_: *mut LeanObject,
    mut v_pending_2497_: *mut LeanObject,
    mut v_log_2498_: *mut LeanObject,
    mut v_direction_2499_: u8,
    mut v_msg_2500_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2502_: u8 = 0;
    let mut v___x_2503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: u8 = 0;
    let mut v___x_2515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initialLocalTimeType_2520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_transitions_2521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2528_: u8 = 0;
    let mut v___x_2530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2532_: u8 = 0;
    let mut v_a_2533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2536_: u8 = 0;
    let mut v___x_2538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2540_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_msg_2500_);
                v___x_2502_ = l___private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed(
                    v_cfg_2496_,
                    v_pending_2497_,
                    v_msg_2500_,
                );
                if v___x_2502_ == 0 {
                    lean_dec_ref(v_msg_2500_);
                    v___x_2503_ = lean_box(0);
                    v___x_2504_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2504_, 0, v___x_2503_);
                    return v___x_2504_;
                } else {
                    v___x_2505_ = lean_get_current_time();
                    if lean_obj_tag(v___x_2505_) == 0 {
                        v_a_2506_ = lean_ctor_get(v___x_2505_, 0);
                        lean_inc(v_a_2506_);
                        lean_dec_ref_known(v___x_2505_, 1);
                        v___x_2507_ = l_Std_Time_Database_defaultGetLocalZoneRules();
                        if lean_obj_tag(v___x_2507_) == 0 {
                            v_a_2508_ = lean_ctor_get(v___x_2507_, 0);
                            lean_inc(v_a_2508_);
                            lean_dec_ref_known(v___x_2507_, 1);
                            v_initialLocalTimeType_2520_ = lean_ctor_get(v_a_2508_, 0);
                            v_transitions_2521_ = lean_ctor_get(v_a_2508_, 1);
                            v___x_2522_ = l_Std_Time_TimeZone_Transition_timezoneAt(
                                v_transitions_2521_,
                                v_a_2506_,
                            );
                            if lean_obj_tag(v___x_2522_) == 0 {
                                lean_dec_ref_known(v___x_2522_, 1);
                                v___x_2523_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(
                                    v_initialLocalTimeType_2520_,
                                );
                                v___y_2510_ = v___x_2523_;
                                state = 1;
                                continue;
                            } else {
                                v_a_2524_ = lean_ctor_get(v___x_2522_, 0);
                                lean_inc(v_a_2524_);
                                lean_dec_ref_known(v___x_2522_, 1);
                                v___y_2510_ = v_a_2524_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_2506_);
                            lean_dec_ref(v_msg_2500_);
                            v_a_2525_ = lean_ctor_get(v___x_2507_, 0);
                            v_isSharedCheck_2532_ = (!lean_is_exclusive(v___x_2507_)) as u8;
                            if v_isSharedCheck_2532_ == 0 {
                                v___x_2527_ = v___x_2507_;
                                v_isShared_2528_ = v_isSharedCheck_2532_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_a_2525_);
                                lean_dec(v___x_2507_);
                                v___x_2527_ = lean_box(0);
                                v_isShared_2528_ = v_isSharedCheck_2532_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_msg_2500_);
                        v_a_2533_ = lean_ctor_get(v___x_2505_, 0);
                        v_isSharedCheck_2540_ = (!lean_is_exclusive(v___x_2505_)) as u8;
                        if v_isSharedCheck_2540_ == 0 {
                            v___x_2535_ = v___x_2505_;
                            v_isShared_2536_ = v_isSharedCheck_2540_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_2533_);
                            lean_dec(v___x_2505_);
                            v___x_2535_ = lean_box(0);
                            v_isShared_2536_ = v_isSharedCheck_2540_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                lean_inc(v_a_2506_);
                lean_inc_ref(v___y_2510_);
                v___f_2511_ = lean_alloc_closure(
                    l_Lean_Server_Logging_LogConfig_ofLspLogConfig___lam__0___boxed
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_2511_, 0, v___y_2510_);
                lean_closure_set(v___f_2511_, 1, v_a_2506_);
                v___x_2512_ = lean_mk_thunk(v___f_2511_);
                v___x_2513_ = lean_alloc_ctor(0, 4, (0) as u32);
                lean_ctor_set(v___x_2513_, 0, v___x_2512_);
                lean_ctor_set(v___x_2513_, 1, v_a_2506_);
                lean_ctor_set(v___x_2513_, 2, v_a_2508_);
                lean_ctor_set(v___x_2513_, 3, v___y_2510_);
                v___x_2514_ = l_Lean_JsonRpc_MessageKind_ofMessage(v_msg_2500_);
                v___x_2515_ = lean_alloc_ctor(0, 2, (2) as u32);
                lean_ctor_set(v___x_2515_, 0, v___x_2513_);
                lean_ctor_set(v___x_2515_, 1, v_msg_2500_);
                lean_ctor_set_uint8(
                    v___x_2515_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v_direction_2499_,
                );
                lean_ctor_set_uint8(
                    v___x_2515_,
                    (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                    v___x_2514_,
                );
                v___x_2516_ = l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson(v___x_2515_);
                v___x_2517_ = l_Lean_Json_compress(v___x_2516_);
                v___x_2518_ = l_IO_FS_Handle_putStrLn(v_log_2498_, v___x_2517_);
                if lean_obj_tag(v___x_2518_) == 0 {
                    lean_dec_ref_known(v___x_2518_, 1);
                    v___x_2519_ = lean_io_prim_handle_flush(v_log_2498_);
                    return v___x_2519_;
                } else {
                    return v___x_2518_;
                }
            }
            2 => {
                if v_isShared_2528_ == 0 {
                    v___x_2530_ = v___x_2527_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2531_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2531_, 0, v_a_2525_);
                    v___x_2530_ = v_reuseFailAlloc_2531_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2530_;
            }
            4 => {
                if v_isShared_2536_ == 0 {
                    v___x_2538_ = v___x_2535_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2539_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2539_, 0, v_a_2533_);
                    v___x_2538_ = v_reuseFailAlloc_2539_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2538_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_Logging_writeLogEntry___boxed(
    mut v_cfg_2541_: *mut LeanObject,
    mut v_pending_2542_: *mut LeanObject,
    mut v_log_2543_: *mut LeanObject,
    mut v_direction_2544_: *mut LeanObject,
    mut v_msg_2545_: *mut LeanObject,
    mut v_a_2546_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_direction_boxed_2547_: u8 = 0;
    let mut v_res_2548_: *mut LeanObject = core::ptr::null_mut();
    v_direction_boxed_2547_ = (lean_unbox(v_direction_2544_) as u8);
    v_res_2548_ = l_Lean_Server_Logging_writeLogEntry(
        v_cfg_2541_,
        v_pending_2542_,
        v_log_2543_,
        v_direction_boxed_2547_,
        v_msg_2545_,
    );
    lean_dec(v_log_2543_);
    lean_dec_ref(v_pending_2542_);
    lean_dec_ref(v_cfg_2541_);
    return v_res_2548_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Server_Logging(builtin: u8) -> *mut LeanObject {
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
    res = runtime_initialize_Lean_Data_Lsp_InitShutdown(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Server_Logging(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Server_Logging(builtin: u8) -> *mut LeanObject {
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
    res = initialize_Lean_Data_Lsp_InitShutdown(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_Logging(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Server_Logging(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Server_Logging(builtin);
}
