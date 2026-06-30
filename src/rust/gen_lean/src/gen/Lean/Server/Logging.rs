// Lean compiler output
// Module: Lean.Server.Logging
// Imports: Std.Time Lean.Data.Lsp.InitShutdown
use crate::ffi::{
    lean_array_get_size, lean_array_push, lean_array_to_list, lean_array_uget_borrowed,
    lean_get_current_time, lean_int_add, lean_int_dec_eq, lean_int_mul, lean_int_neg,
    lean_io_prim_handle_flush, lean_mk_empty_array_with_capacity, lean_mk_thunk, lean_nat_dec_eq,
    lean_nat_dec_lt, lean_nat_to_int, lean_string_append, lean_string_dec_eq, lean_string_hash,
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_add,
    lean_usize_dec_eq, lean_usize_land, lean_usize_of_nat, lean_usize_sub,
};
use crate::r#gen::Init::Data::Array::Basic::l_List_foldl___at___00Array_appendList_spec__0___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_appendTR___redArg;
use crate::r#gen::Init::Data::Rat::Basic::l_Rat_ofInt;
use crate::r#gen::Init::Data::ToString::Name::{
    l_Lean_Name_toString, l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0,
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
static mut l_Lean_Server_Logging_LogConfig_ofLspLogConfig___lam__0___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_Logging_LogConfig_ofLspLogConfig___lam__0___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Server_Logging_LogConfig_ofLspLogConfig___lam__0___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_Logging_LogConfig_ofLspLogConfig___lam__0___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Server_Logging_LogConfig_ofLspLogConfig___closed__0_value:
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
        121, 121, 121, 121, 45, 77, 77, 45, 100, 100, 45, 72, 72, 45, 109, 109, 45, 115, 115, 45,
        83, 83, 83, 83, 88, 88, 0,
    ],
};
static mut l_Lean_Server_Logging_LogConfig_ofLspLogConfig___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_Logging_LogConfig_ofLspLogConfig___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Server_Logging_LogConfig_ofLspLogConfig___closed__1_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Server_Logging_LogConfig_ofLspLogConfig___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_Logging_LogConfig_ofLspLogConfig___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Server_Logging_LogConfig_ofLspLogConfig___closed__2_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Server_Logging_LogConfig_ofLspLogConfig___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_Logging_LogConfig_ofLspLogConfig___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Server_Logging_LogConfig_ofLspLogConfig___closed__3_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Server_Logging_LogConfig_ofLspLogConfig___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_Logging_LogConfig_ofLspLogConfig___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Server_Logging_instInhabitedMessageMethod_default___closed__0_value:
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
static mut l_Lean_Server_Logging_instInhabitedMessageMethod_default___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_Logging_instInhabitedMessageMethod_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Server_Logging_instInhabitedMessageMethod_default___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Server_Logging_instInhabitedMessageMethod_default___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Server_Logging_instInhabitedMessageMethod_default___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_Logging_instInhabitedMessageMethod_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Server_Logging_instInhabitedMessageMethod_default:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_Logging_instInhabitedMessageMethod_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Server_Logging_instInhabitedMessageMethod: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_Logging_instInhabitedMessageMethod_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_MessageMethod_all___closed__0_value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [36, 47, 108, 101, 97, 110, 47, 114, 112, 99, 47, 99, 97, 108, 108, 0]};
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_MessageMethod_all___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Server_Logging_0__Lean_Server_Logging_MessageMethod_all___closed__0_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_MessageMethod_all___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_MessageMethod_all___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonZonedDateTime___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonZonedDateTime___lam__0 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonZonedDateTime___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonZonedDateTime___closed__0_value) as *mut leanh::LeanObject;
pub static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonZonedDateTime: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonZonedDateTime___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonZonedDateTime___lam__0___closed__0_value: leanh::LeanStringObject<63> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 63, m_capacity: 63, m_length: 62, m_data: [69, 120, 112, 101, 99, 116, 101, 100, 32, 115, 116, 114, 105, 110, 103, 32, 119, 104, 101, 110, 32, 99, 111, 110, 118, 101, 114, 116, 105, 110, 103, 32, 74, 83, 79, 78, 32, 116, 111, 32, 83, 116, 100, 46, 84, 105, 109, 101, 46, 90, 111, 110, 101, 100, 68, 97, 116, 101, 84, 105, 109, 101, 0]};
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonZonedDateTime___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonZonedDateTime___lam__0___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonZonedDateTime___lam__0___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonZonedDateTime___lam__0___closed__0_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonZonedDateTime___lam__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonZonedDateTime___lam__0___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonZonedDateTime___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonZonedDateTime___lam__0 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonZonedDateTime___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonZonedDateTime___closed__0_value) as *mut leanh::LeanObject;
pub static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonZonedDateTime: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonZonedDateTime___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__0_value: leanh::LeanStringObject<20> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [101, 120, 112, 101, 99, 116, 101, 100, 32, 101, 114, 114, 111, 114, 32, 99, 111, 100, 101, 0]};
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__0_value) as *mut leanh::LeanObject] };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__8_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__8: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__10_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__10: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__12_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__12: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__14_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__14: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__15_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__15: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__16_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__16: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__17_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__17: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__18_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__18: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__19_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__19: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__20_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__20: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__21_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__21: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__22_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__22: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__23_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__23: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__24_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__24: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__25_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__25: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__26_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 11 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__26: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__26_value) as *mut leanh::LeanObject;
pub static l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__27_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 10 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__27: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__27_value) as *mut leanh::LeanObject;
pub static l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__28_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 9 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__28: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__28_value) as *mut leanh::LeanObject;
pub static l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__29_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 8 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__29: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__29_value) as *mut leanh::LeanObject;
pub static l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__30_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 7 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__30: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__30_value) as *mut leanh::LeanObject;
pub static l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__31_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 6 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__31: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__31_value) as *mut leanh::LeanObject;
pub static l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__32_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 5 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__32: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__32_value) as *mut leanh::LeanObject;
pub static l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__33_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 4 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__33: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__33_value) as *mut leanh::LeanObject;
pub static l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__34_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 3 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__34: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__34_value) as *mut leanh::LeanObject;
pub static l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__35_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__35: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__35_value) as *mut leanh::LeanObject;
pub static l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__36_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__36: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__36_value) as *mut leanh::LeanObject;
pub static l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__37_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__37: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__37_value) as *mut leanh::LeanObject;
pub static l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__3___closed__0_value: leanh::LeanStringObject<46> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 46, m_capacity: 46, m_length: 45, m_data: [97, 32, 114, 101, 113, 117, 101, 115, 116, 32, 105, 100, 32, 110, 101, 101, 100, 115, 32, 116, 111, 32, 98, 101, 32, 97, 32, 110, 117, 109, 98, 101, 114, 32, 111, 114, 32, 97, 32, 115, 116, 114, 105, 110, 103, 0]};
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__3___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__3___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__3___closed__0_value) as *mut leanh::LeanObject] };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__3___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__3___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__0_value: leanh::LeanStringObject<42> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 42, m_capacity: 42, m_length: 41, m_data: [111, 110, 108, 121, 32, 118, 101, 114, 115, 105, 111, 110, 32, 50, 46, 48, 32, 111, 102, 32, 74, 83, 79, 78, 32, 82, 80, 67, 32, 105, 115, 32, 115, 117, 112, 112, 111, 114, 116, 101, 100, 0]};
static mut l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__0_value) as *mut leanh::LeanObject] };
static mut l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__2_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [106, 115, 111, 110, 114, 112, 99, 0]};
static mut l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__3_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [50, 46, 48, 0]};
static mut l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__4_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [105, 100, 0]};
static mut l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__5_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [101, 114, 114, 111, 114, 0]};
static mut l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__6_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [99, 111, 100, 101, 0]};
static mut l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__6_value) as *mut leanh::LeanObject;
pub static l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__7_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [109, 101, 115, 115, 97, 103, 101, 0]};
static mut l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__7_value) as *mut leanh::LeanObject;
pub static l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__8_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [100, 97, 116, 97, 0]};
static mut l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__8_value) as *mut leanh::LeanObject;
pub static l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__9_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [109, 101, 116, 104, 111, 100, 0]};
static mut l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__9_value) as *mut leanh::LeanObject;
pub static l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__10_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [114, 101, 115, 117, 108, 116, 0]};
static mut l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__10_value) as *mut leanh::LeanObject;
pub static l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__11_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [112, 97, 114, 97, 109, 115, 0]};
static mut l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__11_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 105, 109, 101, 0]};
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__1_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__1_value) as *mut leanh::LeanObject,11079354408986465895 as *mut leanh::LeanObject] };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__3_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__2_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__3_value) as *mut leanh::LeanObject,10352885018404983386 as *mut leanh::LeanObject] };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__5_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [83, 101, 114, 118, 101, 114, 0]};
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__6_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__4_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__5_value) as *mut leanh::LeanObject,12337524736695414095 as *mut leanh::LeanObject] };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__7_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [76, 111, 103, 103, 105, 110, 103, 0]};
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__7_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__6_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__7_value) as *mut leanh::LeanObject,13795635718385987595 as *mut leanh::LeanObject] };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__8_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__9_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__8_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,10771712435572913910 as *mut leanh::LeanObject] };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__9_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__10_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__9_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__3_value) as *mut leanh::LeanObject,16696290940608711967 as *mut leanh::LeanObject] };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__10_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__11_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__10_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__5_value) as *mut leanh::LeanObject,8428733202386381774 as *mut leanh::LeanObject] };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__11_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__12_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__11_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__7_value) as *mut leanh::LeanObject,2923788871047101174 as *mut leanh::LeanObject] };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__12_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__13_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [76, 111, 103, 69, 110, 116, 114, 121, 0]};
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__13_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__14_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__12_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__13_value) as *mut leanh::LeanObject,14170570813020572205 as *mut leanh::LeanObject] };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__14_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__15_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__15: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__16_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__16: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__17_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__0_value) as *mut leanh::LeanObject,5547123645457395768 as *mut leanh::LeanObject] };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__17: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__17_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__18_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__18: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__19_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__19: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__20_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [58, 32, 0]};
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__20: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__20_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__21_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__21: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__22_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [100, 105, 114, 101, 99, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__22: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__22_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__23_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__22_value) as *mut leanh::LeanObject,12068223408101116769 as *mut leanh::LeanObject] };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__23: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__23_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__24_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__24: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__25_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__25: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__26_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__26: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__27_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [107, 105, 110, 100, 0]};
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__27: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__27_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__28_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__27_value) as *mut leanh::LeanObject,11445860042738416218 as *mut leanh::LeanObject] };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__28: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__28_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__29_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__29: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__30_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__30: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__31_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__31: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__32_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [109, 115, 103, 0]};
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__32: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__32_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__33_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__32_value) as *mut leanh::LeanObject,5921405926628438706 as *mut leanh::LeanObject] };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__33: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__33_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__34_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__34: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__35_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__35: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__36_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__36: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry___closed__0_value) as *mut leanh::LeanObject;
pub static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__3_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__1_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__2_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__0_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__2_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__8_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__8: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__10_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__10: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__12_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__12: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__14_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__14: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__15_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__15: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__16_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__16: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__17_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__17: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__18_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__18: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__19_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__19: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__20_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__20: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__21_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__21: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__22_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__22: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__23_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__23: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__24_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__24: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__25_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__25: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__26_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__26: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry___closed__0_value
) as *mut leanh::LeanObject;
pub static mut l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry___closed__0_value
) as *mut leanh::LeanObject;
pub unsafe fn _init_l_Lean_Server_Logging_LogConfig_ofLspLogConfig___lam__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1275_ = leanh::lean_unsigned_to_nat(0);
    v___x_1276_ = lean_nat_to_int(v___x_1275_);
    return v___x_1276_;
}
pub unsafe fn _init_l_Lean_Server_Logging_LogConfig_ofLspLogConfig___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1277_ = leanh::lean_unsigned_to_nat(1000000000);
    v___x_1278_ = lean_nat_to_int(v___x_1277_);
    return v___x_1278_;
}
pub unsafe fn l_Lean_Server_Logging_LogConfig_ofLspLogConfig___lam__0(
    mut v___y_1279_: *mut leanh::LeanObject,
    mut v_a_1280_: *mut leanh::LeanObject,
    mut v_x_1281_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_offset_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_offset_1282_ = leanh::lean_ctor_get(v___y_1279_, 0);
    v_second_1283_ = leanh::lean_ctor_get(v_a_1280_, 0);
    v_nano_1284_ = leanh::lean_ctor_get(v_a_1280_, 1);
    v___x_1285_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Server_Logging_LogConfig_ofLspLogConfig___lam__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Server_Logging_LogConfig_ofLspLogConfig___lam__0___closed__0_once
        ),
        _init_l_Lean_Server_Logging_LogConfig_ofLspLogConfig___lam__0___closed__0,
    );
    v___x_1286_ = leanh::lean_obj_once(
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
    leanh::lean_dec(v___x_1287_);
    v___x_1289_ = lean_int_mul(v_offset_1282_, v___x_1286_);
    v___x_1290_ = lean_int_add(v___x_1289_, v___x_1285_);
    leanh::lean_dec(v___x_1289_);
    v___x_1291_ = lean_int_add(v___x_1288_, v___x_1290_);
    leanh::lean_dec(v___x_1290_);
    leanh::lean_dec(v___x_1288_);
    v___x_1292_ = l_Std_Time_Duration_ofNanoseconds(v___x_1291_);
    leanh::lean_dec(v___x_1291_);
    v___x_1293_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1292_);
    return v___x_1293_;
}
pub unsafe fn l_Lean_Server_Logging_LogConfig_ofLspLogConfig___lam__0___boxed(
    mut v___y_1294_: *mut leanh::LeanObject,
    mut v_a_1295_: *mut leanh::LeanObject,
    mut v_x_1296_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1297_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1297_ =
        l_Lean_Server_Logging_LogConfig_ofLspLogConfig___lam__0(v___y_1294_, v_a_1295_, v_x_1296_);
    leanh::lean_dec_ref(v_a_1295_);
    leanh::lean_dec_ref(v___y_1294_);
    return v_res_1297_;
}
pub unsafe fn l_Lean_Server_Logging_LogConfig_ofLspLogConfig(
    mut v_lspCfg_x3f_1302_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1308_: u8 = 0;
    let mut v___x_1309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1313_: u8 = 0;
    let mut v___y_1315_: u8 = 0;
    let mut v_allowedMethods_x3f_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_disallowedMethods_x3f_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_logDir_x3f_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_allowedMethods_x3f_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_disallowedMethods_x3f_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: u8 = 0;
    let mut v_val_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: u8 = 0;
    let mut v___x_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initialLocalTimeType_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_transitions_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1354_: u8 = 0;
    let mut v_a_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1358_: u8 = 0;
    let mut v___x_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1362_: u8 = 0;
    let mut v_isSharedCheck_1363_: u8 = 0;
    let mut v_a_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1367_: u8 = 0;
    let mut v___x_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1371_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1304_ = lean_get_current_time();
                if leanh::lean_obj_tag(v___x_1304_) == 0 {
                    v_a_1305_ = leanh::lean_ctor_get(v___x_1304_, 0);
                    v_isSharedCheck_1363_ = (!leanh::lean_is_exclusive(v___x_1304_)) as u8;
                    if v_isSharedCheck_1363_ == 0 {
                        v___x_1307_ = v___x_1304_;
                        v_isShared_1308_ = v_isSharedCheck_1363_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1305_);
                        leanh::lean_dec(v___x_1304_);
                        v___x_1307_ = leanh::lean_box(0);
                        v_isShared_1308_ = v_isSharedCheck_1363_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_lspCfg_x3f_1302_);
                    v_a_1364_ = leanh::lean_ctor_get(v___x_1304_, 0);
                    v_isSharedCheck_1371_ = (!leanh::lean_is_exclusive(v___x_1304_)) as u8;
                    if v_isSharedCheck_1371_ == 0 {
                        v___x_1366_ = v___x_1304_;
                        v_isShared_1367_ = v_isSharedCheck_1371_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1364_);
                        leanh::lean_dec(v___x_1304_);
                        v___x_1366_ = leanh::lean_box(0);
                        v_isShared_1367_ = v_isSharedCheck_1371_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1309_ = l_Std_Time_Database_defaultGetLocalZoneRules();
                if leanh::lean_obj_tag(v___x_1309_) == 0 {
                    v_a_1310_ = leanh::lean_ctor_get(v___x_1309_, 0);
                    v_isSharedCheck_1354_ = (!leanh::lean_is_exclusive(v___x_1309_)) as u8;
                    if v_isSharedCheck_1354_ == 0 {
                        v___x_1312_ = v___x_1309_;
                        v_isShared_1313_ = v_isSharedCheck_1354_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1310_);
                        leanh::lean_dec(v___x_1309_);
                        v___x_1312_ = leanh::lean_box(0);
                        v_isShared_1313_ = v_isSharedCheck_1354_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1307_);
                    leanh::lean_dec(v_a_1305_);
                    leanh::lean_dec(v_lspCfg_x3f_1302_);
                    v_a_1355_ = leanh::lean_ctor_get(v___x_1309_, 0);
                    v_isSharedCheck_1362_ = (!leanh::lean_is_exclusive(v___x_1309_)) as u8;
                    if v_isSharedCheck_1362_ == 0 {
                        v___x_1357_ = v___x_1309_;
                        v_isShared_1358_ = v_isSharedCheck_1362_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1355_);
                        leanh::lean_dec(v___x_1309_);
                        v___x_1357_ = leanh::lean_box(0);
                        v_isShared_1358_ = v_isSharedCheck_1362_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                v_initialLocalTimeType_1349_ = leanh::lean_ctor_get(v_a_1310_, 0);
                v_transitions_1350_ = leanh::lean_ctor_get(v_a_1310_, 1);
                v___x_1351_ =
                    l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_1350_, v_a_1305_);
                if leanh::lean_obj_tag(v___x_1351_) == 0 {
                    leanh::lean_dec_ref_known(v___x_1351_, 1);
                    v___x_1352_ =
                        l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_1349_);
                    v___y_1324_ = v___x_1352_;
                    state = 5;
                    continue;
                } else {
                    v_a_1353_ = leanh::lean_ctor_get(v___x_1351_, 0);
                    leanh::lean_inc(v_a_1353_);
                    leanh::lean_dec_ref_known(v___x_1351_, 1);
                    v___y_1324_ = v_a_1353_;
                    state = 5;
                    continue;
                }
            }
            3 => {
                v___x_1319_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                leanh::lean_ctor_set(v___x_1319_, 0, v___y_1318_);
                leanh::lean_ctor_set(v___x_1319_, 1, v_allowedMethods_x3f_1316_);
                leanh::lean_ctor_set(v___x_1319_, 2, v_disallowedMethods_x3f_1317_);
                leanh::lean_ctor_set_uint8(
                    v___x_1319_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___y_1315_,
                );
                if v_isShared_1313_ == 0 {
                    leanh::lean_ctor_set(v___x_1312_, 0, v___x_1319_);
                    v___x_1321_ = v___x_1312_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1322_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1322_, 0, v___x_1319_);
                    v___x_1321_ = v_reuseFailAlloc_1322_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1321_;
            }
            5 => {
                leanh::lean_inc(v_a_1305_);
                leanh::lean_inc_ref(v___y_1324_);
                v___f_1325_ = leanh::lean_alloc_closure(
                    l_Lean_Server_Logging_LogConfig_ofLspLogConfig___lam__0___boxed
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___f_1325_, 0, v___y_1324_);
                leanh::lean_closure_set(v___f_1325_, 1, v_a_1305_);
                v___x_1326_ = lean_mk_thunk(v___f_1325_);
                v___x_1327_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_1327_, 0, v___x_1326_);
                leanh::lean_ctor_set(v___x_1327_, 1, v_a_1305_);
                leanh::lean_ctor_set(v___x_1327_, 2, v_a_1310_);
                leanh::lean_ctor_set(v___x_1327_, 3, v___y_1324_);
                v___x_1328_ = l_Lean_Server_Logging_LogConfig_ofLspLogConfig___closed__0;
                v___x_1329_ = l_Std_Time_ZonedDateTime_format(v___x_1327_, v___x_1328_);
                v___x_1330_ = l_Lean_Server_Logging_LogConfig_ofLspLogConfig___closed__1;
                v___x_1331_ = lean_string_append(v___x_1330_, v___x_1329_);
                leanh::lean_dec_ref(v___x_1329_);
                v___x_1332_ = l_Lean_Server_Logging_LogConfig_ofLspLogConfig___closed__2;
                v___x_1333_ = lean_string_append(v___x_1331_, v___x_1332_);
                v___x_1334_ = l_Lean_Server_Logging_LogConfig_ofLspLogConfig___closed__3;
                leanh::lean_inc_ref(v___x_1333_);
                v___x_1335_ = l_System_FilePath_join(v___x_1334_, v___x_1333_);
                if leanh::lean_obj_tag(v_lspCfg_x3f_1302_) == 1 {
                    leanh::lean_del_object(v___x_1307_);
                    v_val_1336_ = leanh::lean_ctor_get(v_lspCfg_x3f_1302_, 0);
                    leanh::lean_inc(v_val_1336_);
                    leanh::lean_dec_ref_known(v_lspCfg_x3f_1302_, 1);
                    v_logDir_x3f_1337_ = leanh::lean_ctor_get(v_val_1336_, 0);
                    leanh::lean_inc(v_logDir_x3f_1337_);
                    v_allowedMethods_x3f_1338_ = leanh::lean_ctor_get(v_val_1336_, 1);
                    leanh::lean_inc(v_allowedMethods_x3f_1338_);
                    v_disallowedMethods_x3f_1339_ = leanh::lean_ctor_get(v_val_1336_, 2);
                    leanh::lean_inc(v_disallowedMethods_x3f_1339_);
                    leanh::lean_dec(v_val_1336_);
                    v___x_1340_ = 1;
                    if leanh::lean_obj_tag(v_logDir_x3f_1337_) == 0 {
                        leanh::lean_dec_ref(v___x_1333_);
                        v___y_1315_ = v___x_1340_;
                        v_allowedMethods_x3f_1316_ = v_allowedMethods_x3f_1338_;
                        v_disallowedMethods_x3f_1317_ = v_disallowedMethods_x3f_1339_;
                        v___y_1318_ = v___x_1335_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v___x_1335_);
                        v_val_1341_ = leanh::lean_ctor_get(v_logDir_x3f_1337_, 0);
                        leanh::lean_inc(v_val_1341_);
                        leanh::lean_dec_ref_known(v_logDir_x3f_1337_, 1);
                        v___x_1342_ = l_System_FilePath_join(v_val_1341_, v___x_1333_);
                        v___y_1315_ = v___x_1340_;
                        v_allowedMethods_x3f_1316_ = v_allowedMethods_x3f_1338_;
                        v_disallowedMethods_x3f_1317_ = v_disallowedMethods_x3f_1339_;
                        v___y_1318_ = v___x_1342_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___x_1333_);
                    leanh::lean_del_object(v___x_1312_);
                    leanh::lean_dec(v_lspCfg_x3f_1302_);
                    v___x_1343_ = 0;
                    v___x_1344_ = leanh::lean_box(0);
                    v___x_1345_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    leanh::lean_ctor_set(v___x_1345_, 0, v___x_1335_);
                    leanh::lean_ctor_set(v___x_1345_, 1, v___x_1344_);
                    leanh::lean_ctor_set(v___x_1345_, 2, v___x_1344_);
                    leanh::lean_ctor_set_uint8(
                        v___x_1345_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        v___x_1343_,
                    );
                    if v_isShared_1308_ == 0 {
                        leanh::lean_ctor_set(v___x_1307_, 0, v___x_1345_);
                        v___x_1347_ = v___x_1307_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1348_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1348_, 0, v___x_1345_);
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
                    v_reuseFailAlloc_1361_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_a_1355_);
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
                    v_reuseFailAlloc_1370_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_a_1364_);
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
    mut v_lspCfg_x3f_1372_: *mut leanh::LeanObject,
    mut v_a_1373_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1374_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1374_ = l_Lean_Server_Logging_LogConfig_ofLspLogConfig(v_lspCfg_x3f_1372_);
    return v_res_1374_;
}
pub unsafe fn l_Nat_cast___at___00Nat_cast___at___00Lean_Server_Logging_LogConfig_ofLspLogConfig_spec__0_spec__0(
    mut v_a_1375_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1376_ = lean_nat_to_int(v_a_1375_);
    return v___x_1376_;
}
pub unsafe fn l_Nat_cast___at___00Lean_Server_Logging_LogConfig_ofLspLogConfig_spec__0(
    mut v_a_1377_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1378_ = lean_nat_to_int(v_a_1377_);
    v___x_1379_ = l_Rat_ofInt(v___x_1378_);
    return v___x_1379_;
}
pub unsafe fn l_Lean_Server_Logging_MessageMethod_ctorIdx(
    mut v_x_1380_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_1380_) {
        0 => {
            let mut v___x_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1381_ = leanh::lean_unsigned_to_nat(0);
            return v___x_1381_;
        }
        1 => {
            let mut v___x_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1382_ = leanh::lean_unsigned_to_nat(1);
            return v___x_1382_;
        }
        _ => {
            let mut v___x_1383_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1383_ = leanh::lean_unsigned_to_nat(2);
            return v___x_1383_;
        }
    }
}
pub unsafe fn l_Lean_Server_Logging_MessageMethod_ctorIdx___boxed(
    mut v_x_1384_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1385_ = l_Lean_Server_Logging_MessageMethod_ctorIdx(v_x_1384_);
    leanh::lean_dec_ref(v_x_1384_);
    return v_res_1385_;
}
pub unsafe fn l_Lean_Server_Logging_MessageMethod_ctorElim___redArg(
    mut v_t_1386_: *mut leanh::LeanObject,
    mut v_k_1387_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_method_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_method_1388_ = leanh::lean_ctor_get(v_t_1386_, 0);
    leanh::lean_inc_ref(v_method_1388_);
    leanh::lean_dec_ref(v_t_1386_);
    v___x_1389_ = leanh::lean_apply_1(v_k_1387_, v_method_1388_);
    return v___x_1389_;
}
pub unsafe fn l_Lean_Server_Logging_MessageMethod_ctorElim(
    mut v_motive_1390_: *mut leanh::LeanObject,
    mut v_ctorIdx_1391_: *mut leanh::LeanObject,
    mut v_t_1392_: *mut leanh::LeanObject,
    mut v_h_1393_: *mut leanh::LeanObject,
    mut v_k_1394_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1395_ = l_Lean_Server_Logging_MessageMethod_ctorElim___redArg(v_t_1392_, v_k_1394_);
    return v___x_1395_;
}
pub unsafe fn l_Lean_Server_Logging_MessageMethod_ctorElim___boxed(
    mut v_motive_1396_: *mut leanh::LeanObject,
    mut v_ctorIdx_1397_: *mut leanh::LeanObject,
    mut v_t_1398_: *mut leanh::LeanObject,
    mut v_h_1399_: *mut leanh::LeanObject,
    mut v_k_1400_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1401_ = l_Lean_Server_Logging_MessageMethod_ctorElim(
        v_motive_1396_,
        v_ctorIdx_1397_,
        v_t_1398_,
        v_h_1399_,
        v_k_1400_,
    );
    leanh::lean_dec(v_ctorIdx_1397_);
    return v_res_1401_;
}
pub unsafe fn l_Lean_Server_Logging_MessageMethod_request_elim___redArg(
    mut v_t_1402_: *mut leanh::LeanObject,
    mut v_request_1403_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1404_ = l_Lean_Server_Logging_MessageMethod_ctorElim___redArg(v_t_1402_, v_request_1403_);
    return v___x_1404_;
}
pub unsafe fn l_Lean_Server_Logging_MessageMethod_request_elim(
    mut v_motive_1405_: *mut leanh::LeanObject,
    mut v_t_1406_: *mut leanh::LeanObject,
    mut v_h_1407_: *mut leanh::LeanObject,
    mut v_request_1408_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1409_ = l_Lean_Server_Logging_MessageMethod_ctorElim___redArg(v_t_1406_, v_request_1408_);
    return v___x_1409_;
}
pub unsafe fn l_Lean_Server_Logging_MessageMethod_rpcRequest_elim___redArg(
    mut v_t_1410_: *mut leanh::LeanObject,
    mut v_rpcRequest_1411_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1412_ =
        l_Lean_Server_Logging_MessageMethod_ctorElim___redArg(v_t_1410_, v_rpcRequest_1411_);
    return v___x_1412_;
}
pub unsafe fn l_Lean_Server_Logging_MessageMethod_rpcRequest_elim(
    mut v_motive_1413_: *mut leanh::LeanObject,
    mut v_t_1414_: *mut leanh::LeanObject,
    mut v_h_1415_: *mut leanh::LeanObject,
    mut v_rpcRequest_1416_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1417_ =
        l_Lean_Server_Logging_MessageMethod_ctorElim___redArg(v_t_1414_, v_rpcRequest_1416_);
    return v___x_1417_;
}
pub unsafe fn l_Lean_Server_Logging_MessageMethod_notification_elim___redArg(
    mut v_t_1418_: *mut leanh::LeanObject,
    mut v_notification_1419_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1420_ =
        l_Lean_Server_Logging_MessageMethod_ctorElim___redArg(v_t_1418_, v_notification_1419_);
    return v___x_1420_;
}
pub unsafe fn l_Lean_Server_Logging_MessageMethod_notification_elim(
    mut v_motive_1421_: *mut leanh::LeanObject,
    mut v_t_1422_: *mut leanh::LeanObject,
    mut v_h_1423_: *mut leanh::LeanObject,
    mut v_notification_1424_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1425_ =
        l_Lean_Server_Logging_MessageMethod_ctorElim___redArg(v_t_1422_, v_notification_1424_);
    return v___x_1425_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_MessageMethod_all___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1432_ =
        l___private_Lean_Server_Logging_0__Lean_Server_Logging_MessageMethod_all___closed__0;
    v___x_1433_ = leanh::lean_unsigned_to_nat(2);
    v___x_1434_ = lean_mk_empty_array_with_capacity(v___x_1433_);
    v___x_1435_ = lean_array_push(v___x_1434_, v___x_1432_);
    return v___x_1435_;
}
pub unsafe fn l___private_Lean_Server_Logging_0__Lean_Server_Logging_MessageMethod_all(
    mut v_x_1436_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_method_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_method_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_method_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1436_) == 1 {
                    v_method_1442_ = leanh::lean_ctor_get(v_x_1436_, 0);
                    leanh::lean_inc_ref(v_method_1442_);
                    leanh::lean_dec_ref_known(v_x_1436_, 1);
                    v___x_1443_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_MessageMethod_all___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_MessageMethod_all___closed__1_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_MessageMethod_all___closed__1);
                    v___x_1444_ = lean_array_push(v___x_1443_, v_method_1442_);
                    return v___x_1444_;
                } else {
                    v_method_1445_ = leanh::lean_ctor_get(v_x_1436_, 0);
                    leanh::lean_inc_ref(v_method_1445_);
                    leanh::lean_dec_ref(v_x_1436_);
                    v_method_1438_ = v_method_1445_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1439_ = leanh::lean_unsigned_to_nat(1);
                v___x_1440_ = lean_mk_empty_array_with_capacity(v___x_1439_);
                v___x_1441_ = lean_array_push(v___x_1440_, v_method_1438_);
                return v___x_1441_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_toJson___at___00Lean_Server_Logging_messageMethod_x3f_spec__0(
    mut v_x_1446_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1446_) == 0 {
        let mut v___x_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1447_ = leanh::lean_box(0);
        return v___x_1447_;
    } else {
        let mut v_val_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1449_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1448_ = leanh::lean_ctor_get(v_x_1446_, 0);
        leanh::lean_inc(v_val_1448_);
        leanh::lean_dec_ref_known(v_x_1446_, 1);
        v___x_1449_ = l_Lean_Json_Structured_toJson(v_val_1448_);
        return v___x_1449_;
    }
}
pub unsafe fn l_Lean_Server_Logging_messageMethod_x3f(
    mut v_x_1450_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_method_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_x3f_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: u8 = 0;
    let mut v_params_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1463_: u8 = 0;
    let mut v_method_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1470_: u8 = 0;
    let mut v_method_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                match leanh::lean_obj_tag(v_x_1450_) {
                    0 => {
                        v_method_1451_ = leanh::lean_ctor_get(v_x_1450_, 1);
                        leanh::lean_inc_ref(v_method_1451_);
                        v_params_x3f_1452_ = leanh::lean_ctor_get(v_x_1450_, 2);
                        leanh::lean_inc(v_params_x3f_1452_);
                        leanh::lean_dec_ref_known(v_x_1450_, 3);
                        v___x_1456_ = l___private_Lean_Server_Logging_0__Lean_Server_Logging_MessageMethod_all___closed__0;
                        v___x_1457_ = lean_string_dec_eq(v_method_1451_, v___x_1456_);
                        if v___x_1457_ == 0 {
                            leanh::lean_dec(v_params_x3f_1452_);
                            state = 1;
                            continue;
                        } else {
                            v_params_1458_ = l_Option_toJson___at___00Lean_Server_Logging_messageMethod_x3f_spec__0(v_params_x3f_1452_);
                            v___x_1459_ =
                                l_Lean_Lsp_instFromJsonRpcCallParams_fromJson(v_params_1458_);
                            if leanh::lean_obj_tag(v___x_1459_) == 1 {
                                leanh::lean_dec_ref(v_method_1451_);
                                v_a_1460_ = leanh::lean_ctor_get(v___x_1459_, 0);
                                v_isSharedCheck_1470_ =
                                    (!leanh::lean_is_exclusive(v___x_1459_)) as u8;
                                if v_isSharedCheck_1470_ == 0 {
                                    v___x_1462_ = v___x_1459_;
                                    v_isShared_1463_ = v_isSharedCheck_1470_;
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1460_);
                                    leanh::lean_dec(v___x_1459_);
                                    v___x_1462_ = leanh::lean_box(0);
                                    v_isShared_1463_ = v_isSharedCheck_1470_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec_ref(v___x_1459_);
                                state = 1;
                                continue;
                            }
                        }
                    }
                    1 => {
                        v_method_1471_ = leanh::lean_ctor_get(v_x_1450_, 0);
                        leanh::lean_inc_ref(v_method_1471_);
                        leanh::lean_dec_ref_known(v_x_1450_, 2);
                        v___x_1472_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1472_, 0, v_method_1471_);
                        v___x_1473_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1473_, 0, v___x_1472_);
                        return v___x_1473_;
                    }
                    _ => {
                        leanh::lean_dec_ref(v_x_1450_);
                        v___x_1474_ = leanh::lean_box(0);
                        return v___x_1474_;
                    }
                }
            }
            1 => {
                v___x_1454_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1454_, 0, v_method_1451_);
                v___x_1455_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1455_, 0, v___x_1454_);
                return v___x_1455_;
            }
            2 => {
                v_method_1464_ = leanh::lean_ctor_get(v_a_1460_, 1);
                leanh::lean_inc(v_method_1464_);
                leanh::lean_dec(v_a_1460_);
                v___x_1465_ = l_Lean_Name_toString(v_method_1464_, v___x_1457_);
                if v_isShared_1463_ == 0 {
                    leanh::lean_ctor_set(v___x_1462_, 0, v___x_1465_);
                    v___x_1467_ = v___x_1462_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1469_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1469_, 0, v___x_1465_);
                    v___x_1467_ = v_reuseFailAlloc_1469_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1468_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1468_, 0, v___x_1467_);
                return v___x_1468_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_Logging_0__Lean_Server_Logging_messageId_x3f(
    mut v_x_1475_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_1475_) {
        0 => {
            let mut v_id_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_id_1476_ = leanh::lean_ctor_get(v_x_1475_, 0);
            leanh::lean_inc(v_id_1476_);
            v___x_1477_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_1477_, 0, v_id_1476_);
            return v___x_1477_;
        }
        2 => {
            let mut v_id_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_id_1478_ = leanh::lean_ctor_get(v_x_1475_, 0);
            leanh::lean_inc(v_id_1478_);
            v___x_1479_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_1479_, 0, v_id_1478_);
            return v___x_1479_;
        }
        3 => {
            let mut v_id_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_id_1480_ = leanh::lean_ctor_get(v_x_1475_, 0);
            leanh::lean_inc(v_id_1480_);
            v___x_1481_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_1481_, 0, v_id_1480_);
            return v___x_1481_;
        }
        _ => {
            let mut v___x_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1482_ = leanh::lean_box(0);
            return v___x_1482_;
        }
    }
}
pub unsafe fn l___private_Lean_Server_Logging_0__Lean_Server_Logging_messageId_x3f___boxed(
    mut v_x_1483_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1484_ = l___private_Lean_Server_Logging_0__Lean_Server_Logging_messageId_x3f(v_x_1483_);
    leanh::lean_dec_ref(v_x_1483_);
    return v_res_1484_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_method_x3f_spec__0_spec__0___redArg(
    mut v_a_1485_: *mut leanh::LeanObject,
    mut v_x_1486_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: u8 = 0;
    let mut v___x_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1486_) == 0 {
                    v___x_1487_ = leanh::lean_box(0);
                    return v___x_1487_;
                } else {
                    v_key_1488_ = leanh::lean_ctor_get(v_x_1486_, 0);
                    v_value_1489_ = leanh::lean_ctor_get(v_x_1486_, 1);
                    v_tail_1490_ = leanh::lean_ctor_get(v_x_1486_, 2);
                    v___x_1491_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_key_1488_, v_a_1485_);
                    if v___x_1491_ == 0 {
                        v_x_1486_ = v_tail_1490_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc(v_value_1489_);
                        v___x_1493_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1493_, 0, v_value_1489_);
                        return v___x_1493_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_method_x3f_spec__0_spec__0___redArg___boxed(
    mut v_a_1494_: *mut leanh::LeanObject,
    mut v_x_1495_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1496_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_method_x3f_spec__0_spec__0___redArg(v_a_1494_, v_x_1495_);
    leanh::lean_dec(v_x_1495_);
    leanh::lean_dec(v_a_1494_);
    return v_res_1496_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_method_x3f_spec__0___redArg(
    mut v_m_1497_: *mut leanh::LeanObject,
    mut v_a_1498_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_1499_ = leanh::lean_ctor_get(v_m_1497_, 1);
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
    mut v_m_1515_: *mut leanh::LeanObject,
    mut v_a_1516_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1517_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_method_x3f_spec__0___redArg(v_m_1515_, v_a_1516_);
    leanh::lean_dec(v_a_1516_);
    leanh::lean_dec_ref(v_m_1515_);
    return v_res_1517_;
}
pub unsafe fn l___private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_method_x3f(
    mut v_pending_1518_: *mut leanh::LeanObject,
    mut v_msg_1519_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_msg_1519_);
    v___x_1520_ = l_Lean_Server_Logging_messageMethod_x3f(v_msg_1519_);
    if leanh::lean_obj_tag(v___x_1520_) == 0 {
        let mut v___x_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1521_ =
            l___private_Lean_Server_Logging_0__Lean_Server_Logging_messageId_x3f(v_msg_1519_);
        leanh::lean_dec_ref(v_msg_1519_);
        if leanh::lean_obj_tag(v___x_1521_) == 0 {
            return v___x_1520_;
        } else {
            let mut v_val_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_val_1522_ = leanh::lean_ctor_get(v___x_1521_, 0);
            leanh::lean_inc(v_val_1522_);
            leanh::lean_dec_ref_known(v___x_1521_, 1);
            v___x_1523_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_method_x3f_spec__0___redArg(v_pending_1518_, v_val_1522_);
            leanh::lean_dec(v_val_1522_);
            return v___x_1523_;
        }
    } else {
        leanh::lean_dec_ref(v_msg_1519_);
        return v___x_1520_;
    }
}
pub unsafe fn l___private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_method_x3f___boxed(
    mut v_pending_1524_: *mut leanh::LeanObject,
    mut v_msg_1525_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1526_ = l___private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_method_x3f(
        v_pending_1524_,
        v_msg_1525_,
    );
    leanh::lean_dec_ref(v_pending_1524_);
    return v_res_1526_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_method_x3f_spec__0(
    mut v_00_u03b2_1527_: *mut leanh::LeanObject,
    mut v_m_1528_: *mut leanh::LeanObject,
    mut v_a_1529_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1530_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_method_x3f_spec__0___redArg(v_m_1528_, v_a_1529_);
    return v___x_1530_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_method_x3f_spec__0___boxed(
    mut v_00_u03b2_1531_: *mut leanh::LeanObject,
    mut v_m_1532_: *mut leanh::LeanObject,
    mut v_a_1533_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1534_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_method_x3f_spec__0(v_00_u03b2_1531_, v_m_1532_, v_a_1533_);
    leanh::lean_dec(v_a_1533_);
    leanh::lean_dec_ref(v_m_1532_);
    return v_res_1534_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_method_x3f_spec__0_spec__0(
    mut v_00_u03b2_1535_: *mut leanh::LeanObject,
    mut v_a_1536_: *mut leanh::LeanObject,
    mut v_x_1537_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1538_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_method_x3f_spec__0_spec__0___redArg(v_a_1536_, v_x_1537_);
    return v___x_1538_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_method_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b2_1539_: *mut leanh::LeanObject,
    mut v_a_1540_: *mut leanh::LeanObject,
    mut v_x_1541_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1542_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_method_x3f_spec__0_spec__0(v_00_u03b2_1539_, v_a_1540_, v_x_1541_);
    leanh::lean_dec(v_x_1541_);
    leanh::lean_dec(v_a_1540_);
    return v_res_1542_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_spec__0_spec__0___redArg(
    mut v_a_1543_: *mut leanh::LeanObject,
    mut v_x_1544_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1545_: u8 = 0;
    let mut v_key_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1544_) == 0 {
                    v___x_1545_ = 0;
                    return v___x_1545_;
                } else {
                    v_key_1546_ = leanh::lean_ctor_get(v_x_1544_, 0);
                    v_tail_1547_ = leanh::lean_ctor_get(v_x_1544_, 2);
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
    mut v_a_1550_: *mut leanh::LeanObject,
    mut v_x_1551_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1552_: u8 = 0;
    let mut v_r_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1552_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_spec__0_spec__0___redArg(v_a_1550_, v_x_1551_);
    leanh::lean_dec(v_x_1551_);
    leanh::lean_dec_ref(v_a_1550_);
    v_r_1553_ = leanh::lean_box((v_res_1552_) as usize);
    return v_r_1553_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_spec__0___redArg(
    mut v_m_1554_: *mut leanh::LeanObject,
    mut v_a_1555_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_buckets_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: u8 = 0;
    v_buckets_1556_ = leanh::lean_ctor_get(v_m_1554_, 1);
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
    mut v_m_1572_: *mut leanh::LeanObject,
    mut v_a_1573_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1574_: u8 = 0;
    let mut v_r_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1574_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_spec__0___redArg(v_m_1572_, v_a_1573_);
    leanh::lean_dec_ref(v_a_1573_);
    leanh::lean_dec_ref(v_m_1572_);
    v_r_1575_ = leanh::lean_box((v_res_1574_) as usize);
    return v_r_1575_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_spec__2(
    mut v_val_1576_: *mut leanh::LeanObject,
    mut v___x_1577_: u8,
    mut v_as_1578_: *mut leanh::LeanObject,
    mut v_i_1579_: usize,
    mut v_stop_1580_: usize,
) -> u8 {
    let mut v___x_1582_: usize = 0;
    let mut v___x_1583_: usize = 0;
    let mut v___x_1585_: u8 = 0;
    let mut v___x_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_val_1589_: *mut leanh::LeanObject,
    mut v___x_1590_: *mut leanh::LeanObject,
    mut v_as_1591_: *mut leanh::LeanObject,
    mut v_i_1592_: *mut leanh::LeanObject,
    mut v_stop_1593_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1504__boxed_1594_: u8 = 0;
    let mut v_i_boxed_1595_: usize = 0;
    let mut v_stop_boxed_1596_: usize = 0;
    let mut v_res_1597_: u8 = 0;
    let mut v_r_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1504__boxed_1594_ = (leanh::lean_unbox(v___x_1590_) as u8);
    v_i_boxed_1595_ = leanh::lean_unbox_usize(v_i_1592_);
    leanh::lean_dec(v_i_1592_);
    v_stop_boxed_1596_ = leanh::lean_unbox_usize(v_stop_1593_);
    leanh::lean_dec(v_stop_1593_);
    v_res_1597_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_spec__2(v_val_1589_, v___x_1504__boxed_1594_, v_as_1591_, v_i_boxed_1595_, v_stop_boxed_1596_);
    leanh::lean_dec_ref(v_as_1591_);
    leanh::lean_dec_ref(v_val_1589_);
    v_r_1598_ = leanh::lean_box((v_res_1597_) as usize);
    return v_r_1598_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_spec__1(
    mut v_val_1599_: *mut leanh::LeanObject,
    mut v_as_1600_: *mut leanh::LeanObject,
    mut v_i_1601_: usize,
    mut v_stop_1602_: usize,
) -> u8 {
    let mut v___x_1603_: u8 = 0;
    let mut v___x_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_val_1610_: *mut leanh::LeanObject,
    mut v_as_1611_: *mut leanh::LeanObject,
    mut v_i_1612_: *mut leanh::LeanObject,
    mut v_stop_1613_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1614_: usize = 0;
    let mut v_stop_boxed_1615_: usize = 0;
    let mut v_res_1616_: u8 = 0;
    let mut v_r_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1614_ = leanh::lean_unbox_usize(v_i_1612_);
    leanh::lean_dec(v_i_1612_);
    v_stop_boxed_1615_ = leanh::lean_unbox_usize(v_stop_1613_);
    leanh::lean_dec(v_stop_1613_);
    v_res_1616_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_spec__1(v_val_1610_, v_as_1611_, v_i_boxed_1614_, v_stop_boxed_1615_);
    leanh::lean_dec_ref(v_as_1611_);
    leanh::lean_dec_ref(v_val_1610_);
    v_r_1617_ = leanh::lean_box((v_res_1616_) as usize);
    return v_r_1617_;
}
pub unsafe fn l___private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed(
    mut v_cfg_1618_: *mut leanh::LeanObject,
    mut v_pending_1619_: *mut leanh::LeanObject,
    mut v_msg_1620_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_isEnabled_1621_: u8 = 0;
    let mut v_allowedMethods_x3f_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_disallowedMethods_x3f_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: u8 = 0;
    let mut v___x_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_allMethods_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: u8 = 0;
    let mut v___x_1633_: usize = 0;
    let mut v___x_1634_: usize = 0;
    let mut v___x_1635_: u8 = 0;
    let mut v_val_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: u8 = 0;
    let mut v___x_1640_: usize = 0;
    let mut v___x_1641_: usize = 0;
    let mut v___x_1642_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_isEnabled_1621_ = leanh::lean_ctor_get_uint8(
                    v_cfg_1618_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                if v_isEnabled_1621_ == 0 {
                    leanh::lean_dec_ref(v_msg_1620_);
                    return v_isEnabled_1621_;
                } else {
                    v_allowedMethods_x3f_1622_ = leanh::lean_ctor_get(v_cfg_1618_, 1);
                    v_disallowedMethods_x3f_1623_ = leanh::lean_ctor_get(v_cfg_1618_, 2);
                    v___x_1624_ = 0;
                    v___x_1625_ = l___private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_method_x3f(v_pending_1619_, v_msg_1620_);
                    if leanh::lean_obj_tag(v___x_1625_) == 1 {
                        v_val_1626_ = leanh::lean_ctor_get(v___x_1625_, 0);
                        leanh::lean_inc(v_val_1626_);
                        leanh::lean_dec_ref_known(v___x_1625_, 1);
                        v_allMethods_1627_ = l___private_Lean_Server_Logging_0__Lean_Server_Logging_MessageMethod_all(v_val_1626_);
                        if leanh::lean_obj_tag(v_allowedMethods_x3f_1622_) == 1 {
                            v_val_1636_ =
                                leanh::lean_ctor_get(v_allowedMethods_x3f_1622_, 0);
                            v___x_1637_ = leanh::lean_unsigned_to_nat(0);
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
                                        leanh::lean_dec_ref(v_allMethods_1627_);
                                        return v___x_1624_;
                                    }
                                }
                            }
                        } else {
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_1625_);
                        return v___x_1624_;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_disallowedMethods_x3f_1623_) == 1 {
                    v_val_1629_ = leanh::lean_ctor_get(v_disallowedMethods_x3f_1623_, 0);
                    v___x_1630_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1631_ = lean_array_get_size(v_allMethods_1627_);
                    v___x_1632_ = lean_nat_dec_lt(v___x_1630_, v___x_1631_);
                    if v___x_1632_ == 0 {
                        leanh::lean_dec_ref(v_allMethods_1627_);
                        return v_isEnabled_1621_;
                    } else {
                        if v___x_1632_ == 0 {
                            leanh::lean_dec_ref(v_allMethods_1627_);
                            return v_isEnabled_1621_;
                        } else {
                            v___x_1633_ = 0usize;
                            v___x_1634_ = lean_usize_of_nat(v___x_1631_);
                            v___x_1635_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_spec__1(v_val_1629_, v_allMethods_1627_, v___x_1633_, v___x_1634_);
                            leanh::lean_dec_ref(v_allMethods_1627_);
                            if v___x_1635_ == 0 {
                                return v_isEnabled_1621_;
                            } else {
                                return v___x_1624_;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_allMethods_1627_);
                    return v_isEnabled_1621_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed___boxed(
    mut v_cfg_1643_: *mut leanh::LeanObject,
    mut v_pending_1644_: *mut leanh::LeanObject,
    mut v_msg_1645_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1646_: u8 = 0;
    let mut v_r_1647_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1646_ = l___private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed(
        v_cfg_1643_,
        v_pending_1644_,
        v_msg_1645_,
    );
    leanh::lean_dec_ref(v_pending_1644_);
    leanh::lean_dec_ref(v_cfg_1643_);
    v_r_1647_ = leanh::lean_box((v_res_1646_) as usize);
    return v_r_1647_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_spec__0(
    mut v_00_u03b2_1648_: *mut leanh::LeanObject,
    mut v_m_1649_: *mut leanh::LeanObject,
    mut v_a_1650_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1651_: u8 = 0;
    v___x_1651_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_spec__0___redArg(v_m_1649_, v_a_1650_);
    return v___x_1651_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_spec__0___boxed(
    mut v_00_u03b2_1652_: *mut leanh::LeanObject,
    mut v_m_1653_: *mut leanh::LeanObject,
    mut v_a_1654_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1655_: u8 = 0;
    let mut v_r_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1655_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_spec__0(v_00_u03b2_1652_, v_m_1653_, v_a_1654_);
    leanh::lean_dec_ref(v_a_1654_);
    leanh::lean_dec_ref(v_m_1653_);
    v_r_1656_ = leanh::lean_box((v_res_1655_) as usize);
    return v_r_1656_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_spec__0_spec__0(
    mut v_00_u03b2_1657_: *mut leanh::LeanObject,
    mut v_a_1658_: *mut leanh::LeanObject,
    mut v_x_1659_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1660_: u8 = 0;
    v___x_1660_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_spec__0_spec__0___redArg(v_a_1658_, v_x_1659_);
    return v___x_1660_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_spec__0_spec__0___boxed(
    mut v_00_u03b2_1661_: *mut leanh::LeanObject,
    mut v_a_1662_: *mut leanh::LeanObject,
    mut v_x_1663_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1664_: u8 = 0;
    let mut v_r_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1664_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed_spec__0_spec__0(v_00_u03b2_1661_, v_a_1662_, v_x_1663_);
    leanh::lean_dec(v_x_1663_);
    leanh::lean_dec_ref(v_a_1662_);
    v_r_1665_ = leanh::lean_box((v_res_1664_) as usize);
    return v_r_1665_;
}
pub unsafe fn l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonZonedDateTime___lam__0(
    mut v_dt_1666_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1667_ = l_Std_Time_ZonedDateTime_toISO8601String(v_dt_1666_);
    v___x_1668_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1668_, 0, v___x_1667_);
    return v___x_1668_;
}
pub unsafe fn l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonZonedDateTime___lam__0(
    mut v_x_1674_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1674_) == 3 {
        let mut v_s_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_s_1675_ = leanh::lean_ctor_get(v_x_1674_, 0);
        leanh::lean_inc_ref(v_s_1675_);
        leanh::lean_dec_ref_known(v_x_1674_, 1);
        v___x_1676_ = l_Std_Time_ZonedDateTime_fromISO8601String(v_s_1675_);
        return v___x_1676_;
    } else {
        let mut v___x_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_1674_);
        v___x_1677_ = l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonZonedDateTime___lam__0___closed__1;
        return v___x_1677_;
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__0(
    mut v_j_1680_: *mut leanh::LeanObject,
    mut v_k_1681_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1682_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1682_ = l_Lean_Json_getObjValD(v_j_1680_, v_k_1681_);
    if leanh::lean_obj_tag(v___x_1682_) == 3 {
        let mut v_s_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1684_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_s_1683_ = leanh::lean_ctor_get(v___x_1682_, 0);
        leanh::lean_inc_ref(v_s_1683_);
        leanh::lean_dec_ref_known(v___x_1682_, 1);
        v___x_1684_ = l_Std_Time_ZonedDateTime_fromISO8601String(v_s_1683_);
        return v___x_1684_;
    } else {
        let mut v___x_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___x_1682_);
        v___x_1685_ = l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonZonedDateTime___lam__0___closed__1;
        return v___x_1685_;
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__0___boxed(
    mut v_j_1686_: *mut leanh::LeanObject,
    mut v_k_1687_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1688_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__0(v_j_1686_, v_k_1687_);
    leanh::lean_dec_ref(v_k_1687_);
    return v_res_1688_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__1(
    mut v_j_1689_: *mut leanh::LeanObject,
    mut v_k_1690_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1691_ = l_Lean_Json_getObjValD(v_j_1689_, v_k_1690_);
    v___x_1692_ = l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson(v___x_1691_);
    return v___x_1692_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__1___boxed(
    mut v_j_1693_: *mut leanh::LeanObject,
    mut v_k_1694_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1695_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__1(v_j_1693_, v_k_1694_);
    leanh::lean_dec_ref(v_k_1694_);
    return v_res_1695_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__2(
    mut v_j_1696_: *mut leanh::LeanObject,
    mut v_k_1697_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1698_ = l_Lean_Json_getObjValD(v_j_1696_, v_k_1697_);
    v___x_1699_ = l_Lean_JsonRpc_instFromJsonMessageKind_fromJson(v___x_1698_);
    return v___x_1699_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__2___boxed(
    mut v_j_1700_: *mut leanh::LeanObject,
    mut v_k_1701_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1702_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__2(v_j_1700_, v_k_1701_);
    leanh::lean_dec_ref(v_k_1701_);
    return v_res_1702_;
}
pub unsafe fn _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1706_ = leanh::lean_unsigned_to_nat(32700);
    v___x_1707_ = lean_nat_to_int(v___x_1706_);
    return v___x_1707_;
}
pub unsafe fn _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1708_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__2), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__2_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__2);
    v___x_1709_ = lean_int_neg(v___x_1708_);
    return v___x_1709_;
}
pub unsafe fn _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1710_ = leanh::lean_unsigned_to_nat(32600);
    v___x_1711_ = lean_nat_to_int(v___x_1710_);
    return v___x_1711_;
}
pub unsafe fn _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1712_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__4), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__4_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__4);
    v___x_1713_ = lean_int_neg(v___x_1712_);
    return v___x_1713_;
}
pub unsafe fn _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1714_ = leanh::lean_unsigned_to_nat(32601);
    v___x_1715_ = lean_nat_to_int(v___x_1714_);
    return v___x_1715_;
}
pub unsafe fn _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1716_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__6), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__6_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__6);
    v___x_1717_ = lean_int_neg(v___x_1716_);
    return v___x_1717_;
}
pub unsafe fn _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1718_ = leanh::lean_unsigned_to_nat(32602);
    v___x_1719_ = lean_nat_to_int(v___x_1718_);
    return v___x_1719_;
}
pub unsafe fn _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1720_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__8), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__8_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__8);
    v___x_1721_ = lean_int_neg(v___x_1720_);
    return v___x_1721_;
}
pub unsafe fn _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1722_ = leanh::lean_unsigned_to_nat(32603);
    v___x_1723_ = lean_nat_to_int(v___x_1722_);
    return v___x_1723_;
}
pub unsafe fn _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1724_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__10), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__10_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__10);
    v___x_1725_ = lean_int_neg(v___x_1724_);
    return v___x_1725_;
}
pub unsafe fn _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1726_ = leanh::lean_unsigned_to_nat(32002);
    v___x_1727_ = lean_nat_to_int(v___x_1726_);
    return v___x_1727_;
}
pub unsafe fn _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1728_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__12), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__12_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__12);
    v___x_1729_ = lean_int_neg(v___x_1728_);
    return v___x_1729_;
}
pub unsafe fn _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__14()
-> *mut leanh::LeanObject {
    let mut v___x_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1730_ = leanh::lean_unsigned_to_nat(32001);
    v___x_1731_ = lean_nat_to_int(v___x_1730_);
    return v___x_1731_;
}
pub unsafe fn _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_1732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1732_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__14), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__14_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__14);
    v___x_1733_ = lean_int_neg(v___x_1732_);
    return v___x_1733_;
}
pub unsafe fn _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__16()
-> *mut leanh::LeanObject {
    let mut v___x_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1734_ = leanh::lean_unsigned_to_nat(32801);
    v___x_1735_ = lean_nat_to_int(v___x_1734_);
    return v___x_1735_;
}
pub unsafe fn _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1736_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__16), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__16_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__16);
    v___x_1737_ = lean_int_neg(v___x_1736_);
    return v___x_1737_;
}
pub unsafe fn _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__18()
-> *mut leanh::LeanObject {
    let mut v___x_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1738_ = leanh::lean_unsigned_to_nat(32800);
    v___x_1739_ = lean_nat_to_int(v___x_1738_);
    return v___x_1739_;
}
pub unsafe fn _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1740_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__18), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__18_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__18);
    v___x_1741_ = lean_int_neg(v___x_1740_);
    return v___x_1741_;
}
pub unsafe fn _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__20()
-> *mut leanh::LeanObject {
    let mut v___x_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1742_ = leanh::lean_unsigned_to_nat(32900);
    v___x_1743_ = lean_nat_to_int(v___x_1742_);
    return v___x_1743_;
}
pub unsafe fn _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__21()
-> *mut leanh::LeanObject {
    let mut v___x_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1744_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__20), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__20_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__20);
    v___x_1745_ = lean_int_neg(v___x_1744_);
    return v___x_1745_;
}
pub unsafe fn _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__22()
-> *mut leanh::LeanObject {
    let mut v___x_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1746_ = leanh::lean_unsigned_to_nat(32901);
    v___x_1747_ = lean_nat_to_int(v___x_1746_);
    return v___x_1747_;
}
pub unsafe fn _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__23()
-> *mut leanh::LeanObject {
    let mut v___x_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1748_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__22), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__22_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__22);
    v___x_1749_ = lean_int_neg(v___x_1748_);
    return v___x_1749_;
}
pub unsafe fn _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__24()
-> *mut leanh::LeanObject {
    let mut v___x_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1750_ = leanh::lean_unsigned_to_nat(32902);
    v___x_1751_ = lean_nat_to_int(v___x_1750_);
    return v___x_1751_;
}
pub unsafe fn _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__25()
-> *mut leanh::LeanObject {
    let mut v___x_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1752_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__24), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__24_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__24);
    v___x_1753_ = lean_int_neg(v___x_1752_);
    return v___x_1753_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4(
    mut v_j_1790_: *mut leanh::LeanObject,
    mut v_k_1791_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mantissa_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exponent_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: u8 = 0;
    let mut v___x_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: u8 = 0;
    let mut v___x_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: u8 = 0;
    let mut v___x_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: u8 = 0;
    let mut v___x_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: u8 = 0;
    let mut v___x_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: u8 = 0;
    let mut v___x_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: u8 = 0;
    let mut v___x_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: u8 = 0;
    let mut v___x_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: u8 = 0;
    let mut v___x_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: u8 = 0;
    let mut v___x_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: u8 = 0;
    let mut v___x_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: u8 = 0;
    let mut v___x_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: u8 = 0;
    let mut v___x_1824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: u8 = 0;
    let mut v___x_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: u8 = 0;
    let mut v___x_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: u8 = 0;
    let mut v___x_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: u8 = 0;
    let mut v___x_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: u8 = 0;
    let mut v___x_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: u8 = 0;
    let mut v___x_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: u8 = 0;
    let mut v___x_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: u8 = 0;
    let mut v___x_1848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: u8 = 0;
    let mut v___x_1851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: u8 = 0;
    let mut v___x_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: u8 = 0;
    let mut v___x_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1794_ = l_Lean_Json_getObjValD(v_j_1790_, v_k_1791_);
                if leanh::lean_obj_tag(v___x_1794_) == 2 {
                    v_n_1795_ = leanh::lean_ctor_get(v___x_1794_, 0);
                    leanh::lean_inc_ref(v_n_1795_);
                    leanh::lean_dec_ref_known(v___x_1794_, 1);
                    v_mantissa_1796_ = leanh::lean_ctor_get(v_n_1795_, 0);
                    leanh::lean_inc(v_mantissa_1796_);
                    v_exponent_1797_ = leanh::lean_ctor_get(v_n_1795_, 1);
                    leanh::lean_inc(v_exponent_1797_);
                    leanh::lean_dec_ref(v_n_1795_);
                    v___x_1798_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__3), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__3_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__3);
                    v___x_1799_ = lean_int_dec_eq(v_mantissa_1796_, v___x_1798_);
                    if v___x_1799_ == 0 {
                        v___x_1800_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__5), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__5_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__5);
                        v___x_1801_ = lean_int_dec_eq(v_mantissa_1796_, v___x_1800_);
                        if v___x_1801_ == 0 {
                            v___x_1802_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__7), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__7_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__7);
                            v___x_1803_ = lean_int_dec_eq(v_mantissa_1796_, v___x_1802_);
                            if v___x_1803_ == 0 {
                                v___x_1804_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__9), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__9_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__9);
                                v___x_1805_ = lean_int_dec_eq(v_mantissa_1796_, v___x_1804_);
                                if v___x_1805_ == 0 {
                                    v___x_1806_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__11), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__11_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__11);
                                    v___x_1807_ = lean_int_dec_eq(v_mantissa_1796_, v___x_1806_);
                                    if v___x_1807_ == 0 {
                                        v___x_1808_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__13), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__13_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__13);
                                        v___x_1809_ =
                                            lean_int_dec_eq(v_mantissa_1796_, v___x_1808_);
                                        if v___x_1809_ == 0 {
                                            v___x_1810_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__15), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__15_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__15);
                                            v___x_1811_ =
                                                lean_int_dec_eq(v_mantissa_1796_, v___x_1810_);
                                            if v___x_1811_ == 0 {
                                                v___x_1812_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__17), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__17_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__17);
                                                v___x_1813_ =
                                                    lean_int_dec_eq(v_mantissa_1796_, v___x_1812_);
                                                if v___x_1813_ == 0 {
                                                    v___x_1814_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__19), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__19_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__19);
                                                    v___x_1815_ = lean_int_dec_eq(
                                                        v_mantissa_1796_,
                                                        v___x_1814_,
                                                    );
                                                    if v___x_1815_ == 0 {
                                                        v___x_1816_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__21), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__21_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__21);
                                                        v___x_1817_ = lean_int_dec_eq(
                                                            v_mantissa_1796_,
                                                            v___x_1816_,
                                                        );
                                                        if v___x_1817_ == 0 {
                                                            v___x_1818_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__23), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__23_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__23);
                                                            v___x_1819_ = lean_int_dec_eq(
                                                                v_mantissa_1796_,
                                                                v___x_1818_,
                                                            );
                                                            if v___x_1819_ == 0 {
                                                                v___x_1820_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__25), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__25_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__25);
                                                                v___x_1821_ = lean_int_dec_eq(
                                                                    v_mantissa_1796_,
                                                                    v___x_1820_,
                                                                );
                                                                leanh::lean_dec(
                                                                    v_mantissa_1796_,
                                                                );
                                                                if v___x_1821_ == 0 {
                                                                    leanh::lean_dec(
                                                                        v_exponent_1797_,
                                                                    );
                                                                    state = 1;
                                                                    continue;
                                                                } else {
                                                                    v___x_1822_ = leanh::lean_unsigned_to_nat(0);
                                                                    v___x_1823_ = lean_nat_dec_eq(
                                                                        v_exponent_1797_,
                                                                        v___x_1822_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v_exponent_1797_,
                                                                    );
                                                                    if v___x_1823_ == 0 {
                                                                        state = 1;
                                                                        continue;
                                                                    } else {
                                                                        v___x_1824_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__26;
                                                                        return v___x_1824_;
                                                                    }
                                                                }
                                                            } else {
                                                                leanh::lean_dec(
                                                                    v_mantissa_1796_,
                                                                );
                                                                v___x_1825_ = leanh::lean_unsigned_to_nat(0);
                                                                v___x_1826_ = lean_nat_dec_eq(
                                                                    v_exponent_1797_,
                                                                    v___x_1825_,
                                                                );
                                                                leanh::lean_dec(
                                                                    v_exponent_1797_,
                                                                );
                                                                if v___x_1826_ == 0 {
                                                                    state = 1;
                                                                    continue;
                                                                } else {
                                                                    v___x_1827_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__27;
                                                                    return v___x_1827_;
                                                                }
                                                            }
                                                        } else {
                                                            leanh::lean_dec(
                                                                v_mantissa_1796_,
                                                            );
                                                            v___x_1828_ =
                                                                leanh::lean_unsigned_to_nat(
                                                                    0,
                                                                );
                                                            v___x_1829_ = lean_nat_dec_eq(
                                                                v_exponent_1797_,
                                                                v___x_1828_,
                                                            );
                                                            leanh::lean_dec(
                                                                v_exponent_1797_,
                                                            );
                                                            if v___x_1829_ == 0 {
                                                                state = 1;
                                                                continue;
                                                            } else {
                                                                v___x_1830_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__28;
                                                                return v___x_1830_;
                                                            }
                                                        }
                                                    } else {
                                                        leanh::lean_dec(v_mantissa_1796_);
                                                        v___x_1831_ =
                                                            leanh::lean_unsigned_to_nat(0);
                                                        v___x_1832_ = lean_nat_dec_eq(
                                                            v_exponent_1797_,
                                                            v___x_1831_,
                                                        );
                                                        leanh::lean_dec(v_exponent_1797_);
                                                        if v___x_1832_ == 0 {
                                                            state = 1;
                                                            continue;
                                                        } else {
                                                            v___x_1833_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__29;
                                                            return v___x_1833_;
                                                        }
                                                    }
                                                } else {
                                                    leanh::lean_dec(v_mantissa_1796_);
                                                    v___x_1834_ =
                                                        leanh::lean_unsigned_to_nat(0);
                                                    v___x_1835_ = lean_nat_dec_eq(
                                                        v_exponent_1797_,
                                                        v___x_1834_,
                                                    );
                                                    leanh::lean_dec(v_exponent_1797_);
                                                    if v___x_1835_ == 0 {
                                                        state = 1;
                                                        continue;
                                                    } else {
                                                        v___x_1836_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__30;
                                                        return v___x_1836_;
                                                    }
                                                }
                                            } else {
                                                leanh::lean_dec(v_mantissa_1796_);
                                                v___x_1837_ = leanh::lean_unsigned_to_nat(0);
                                                v___x_1838_ =
                                                    lean_nat_dec_eq(v_exponent_1797_, v___x_1837_);
                                                leanh::lean_dec(v_exponent_1797_);
                                                if v___x_1838_ == 0 {
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    v___x_1839_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__31;
                                                    return v___x_1839_;
                                                }
                                            }
                                        } else {
                                            leanh::lean_dec(v_mantissa_1796_);
                                            v___x_1840_ = leanh::lean_unsigned_to_nat(0);
                                            v___x_1841_ =
                                                lean_nat_dec_eq(v_exponent_1797_, v___x_1840_);
                                            leanh::lean_dec(v_exponent_1797_);
                                            if v___x_1841_ == 0 {
                                                state = 1;
                                                continue;
                                            } else {
                                                v___x_1842_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__32;
                                                return v___x_1842_;
                                            }
                                        }
                                    } else {
                                        leanh::lean_dec(v_mantissa_1796_);
                                        v___x_1843_ = leanh::lean_unsigned_to_nat(0);
                                        v___x_1844_ =
                                            lean_nat_dec_eq(v_exponent_1797_, v___x_1843_);
                                        leanh::lean_dec(v_exponent_1797_);
                                        if v___x_1844_ == 0 {
                                            state = 1;
                                            continue;
                                        } else {
                                            v___x_1845_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__33;
                                            return v___x_1845_;
                                        }
                                    }
                                } else {
                                    leanh::lean_dec(v_mantissa_1796_);
                                    v___x_1846_ = leanh::lean_unsigned_to_nat(0);
                                    v___x_1847_ = lean_nat_dec_eq(v_exponent_1797_, v___x_1846_);
                                    leanh::lean_dec(v_exponent_1797_);
                                    if v___x_1847_ == 0 {
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_1848_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__34;
                                        return v___x_1848_;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_mantissa_1796_);
                                v___x_1849_ = leanh::lean_unsigned_to_nat(0);
                                v___x_1850_ = lean_nat_dec_eq(v_exponent_1797_, v___x_1849_);
                                leanh::lean_dec(v_exponent_1797_);
                                if v___x_1850_ == 0 {
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_1851_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__35;
                                    return v___x_1851_;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_mantissa_1796_);
                            v___x_1852_ = leanh::lean_unsigned_to_nat(0);
                            v___x_1853_ = lean_nat_dec_eq(v_exponent_1797_, v___x_1852_);
                            leanh::lean_dec(v_exponent_1797_);
                            if v___x_1853_ == 0 {
                                state = 1;
                                continue;
                            } else {
                                v___x_1854_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__36;
                                return v___x_1854_;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_mantissa_1796_);
                        v___x_1855_ = leanh::lean_unsigned_to_nat(0);
                        v___x_1856_ = lean_nat_dec_eq(v_exponent_1797_, v___x_1855_);
                        leanh::lean_dec(v_exponent_1797_);
                        if v___x_1856_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            v___x_1857_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__37;
                            return v___x_1857_;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_1794_);
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
    mut v_j_1858_: *mut leanh::LeanObject,
    mut v_k_1859_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1860_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4(v_j_1858_, v_k_1859_);
    leanh::lean_dec_ref(v_k_1859_);
    return v_res_1860_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__3(
    mut v_j_1864_: *mut leanh::LeanObject,
    mut v_k_1865_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1870_: u8 = 0;
    let mut v___x_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1875_: u8 = 0;
    let mut v_n_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1879_: u8 = 0;
    let mut v___x_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1884_: u8 = 0;
    let mut v___x_1885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1866_ = l_Lean_Json_getObjValD(v_j_1864_, v_k_1865_);
                match leanh::lean_obj_tag(v___x_1866_) {
                    3 => {
                        v_s_1867_ = leanh::lean_ctor_get(v___x_1866_, 0);
                        v_isSharedCheck_1875_ =
                            (!leanh::lean_is_exclusive(v___x_1866_)) as u8;
                        if v_isSharedCheck_1875_ == 0 {
                            v___x_1869_ = v___x_1866_;
                            v_isShared_1870_ = v_isSharedCheck_1875_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_s_1867_);
                            leanh::lean_dec(v___x_1866_);
                            v___x_1869_ = leanh::lean_box(0);
                            v_isShared_1870_ = v_isSharedCheck_1875_;
                            state = 1;
                            continue;
                        }
                    }
                    2 => {
                        v_n_1876_ = leanh::lean_ctor_get(v___x_1866_, 0);
                        v_isSharedCheck_1884_ =
                            (!leanh::lean_is_exclusive(v___x_1866_)) as u8;
                        if v_isSharedCheck_1884_ == 0 {
                            v___x_1878_ = v___x_1866_;
                            v_isShared_1879_ = v_isSharedCheck_1884_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_n_1876_);
                            leanh::lean_dec(v___x_1866_);
                            v___x_1878_ = leanh::lean_box(0);
                            v_isShared_1879_ = v_isSharedCheck_1884_;
                            state = 3;
                            continue;
                        }
                    }
                    _ => {
                        leanh::lean_dec(v___x_1866_);
                        v___x_1885_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__3___closed__1;
                        return v___x_1885_;
                    }
                }
            }
            1 => {
                if v_isShared_1870_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1869_, 0);
                    v___x_1872_ = v___x_1869_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1874_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_s_1867_);
                    v___x_1872_ = v_reuseFailAlloc_1874_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1873_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1873_, 0, v___x_1872_);
                return v___x_1873_;
            }
            3 => {
                if v_isShared_1879_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1878_, 1);
                    v___x_1881_ = v___x_1878_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1883_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_n_1876_);
                    v___x_1881_ = v_reuseFailAlloc_1883_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1882_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1882_, 0, v___x_1881_);
                return v___x_1882_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__3___boxed(
    mut v_j_1886_: *mut leanh::LeanObject,
    mut v_k_1887_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1888_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1888_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__3(v_j_1886_, v_k_1887_);
    leanh::lean_dec_ref(v_k_1887_);
    return v_res_1888_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__5(
    mut v_j_1889_: *mut leanh::LeanObject,
    mut v_k_1890_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1891_ = l_Lean_Json_getObjValD(v_j_1889_, v_k_1890_);
    v___x_1892_ = l_Lean_Json_getStr_x3f(v___x_1891_);
    return v___x_1892_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__5___boxed(
    mut v_j_1893_: *mut leanh::LeanObject,
    mut v_k_1894_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1895_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__5(v_j_1893_, v_k_1894_);
    leanh::lean_dec_ref(v_k_1894_);
    return v_res_1895_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__6(
    mut v_j_1896_: *mut leanh::LeanObject,
    mut v_k_1897_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1898_ = l_Lean_Json_getObjValD(v_j_1896_, v_k_1897_);
    v___x_1899_ = l_Lean_Json_Structured_fromJson_x3f(v___x_1898_);
    return v___x_1899_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__6___boxed(
    mut v_j_1900_: *mut leanh::LeanObject,
    mut v_k_1901_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1902_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1902_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__6(v_j_1900_, v_k_1901_);
    leanh::lean_dec_ref(v_k_1901_);
    return v_res_1902_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3(
    mut v_j_1916_: *mut leanh::LeanObject,
    mut v_k_1917_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1923_: u8 = 0;
    let mut v___y_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1938_: u8 = 0;
    let mut v___x_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1942_: u8 = 0;
    let mut v_a_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: u8 = 0;
    let mut v___x_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1953_: u8 = 0;
    let mut v___x_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1957_: u8 = 0;
    let mut v_a_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1964_: u8 = 0;
    let mut v___x_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1968_: u8 = 0;
    let mut v_a_1969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1975_: u8 = 0;
    let mut v___x_1977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1979_: u8 = 0;
    let mut v_a_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1986_: u8 = 0;
    let mut v___x_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1990_: u8 = 0;
    let mut v_a_1991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: u8 = 0;
    let mut v_a_1996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1999_: u8 = 0;
    let mut v___x_2001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: u8 = 0;
    let mut v_reuseFailAlloc_2003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2004_: u8 = 0;
    let mut v___x_2006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2014_: u8 = 0;
    let mut v___x_2015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2019_: u8 = 0;
    let mut v_a_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2027_: u8 = 0;
    let mut v___x_2029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2031_: u8 = 0;
    let mut v_a_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2038_: u8 = 0;
    let mut v___y_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2051_: u8 = 0;
    let mut v___x_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2055_: u8 = 0;
    let mut v_isSharedCheck_2056_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1932_ = l_Lean_Json_getObjValD(v_j_1916_, v_k_1917_);
                v___x_1933_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__2;
                leanh::lean_inc(v___x_1932_);
                v___x_1934_ = l_Lean_Json_getObjVal_x3f(v___x_1932_, v___x_1933_);
                if leanh::lean_obj_tag(v___x_1934_) == 0 {
                    leanh::lean_dec(v___x_1932_);
                    v_a_1935_ = leanh::lean_ctor_get(v___x_1934_, 0);
                    v_isSharedCheck_1942_ = (!leanh::lean_is_exclusive(v___x_1934_)) as u8;
                    if v_isSharedCheck_1942_ == 0 {
                        v___x_1937_ = v___x_1934_;
                        v_isShared_1938_ = v_isSharedCheck_1942_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1935_);
                        leanh::lean_dec(v___x_1934_);
                        v___x_1937_ = leanh::lean_box(0);
                        v_isShared_1938_ = v_isSharedCheck_1942_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_1943_ = leanh::lean_ctor_get(v___x_1934_, 0);
                    leanh::lean_inc(v_a_1943_);
                    leanh::lean_dec_ref_known(v___x_1934_, 1);
                    if leanh::lean_obj_tag(v_a_1943_) == 3 {
                        v_s_1944_ = leanh::lean_ctor_get(v_a_1943_, 0);
                        leanh::lean_inc_ref(v_s_1944_);
                        leanh::lean_dec_ref_known(v_a_1943_, 1);
                        v___x_1945_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__3;
                        v___x_1946_ = lean_string_dec_eq(v_s_1944_, v___x_1945_);
                        leanh::lean_dec_ref(v_s_1944_);
                        if v___x_1946_ == 0 {
                            leanh::lean_dec(v___x_1932_);
                            state = 1;
                            continue;
                        } else {
                            v___x_1947_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__4;
                            leanh::lean_inc(v___x_1932_);
                            v___x_1948_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__3(v___x_1932_, v___x_1947_);
                            if leanh::lean_obj_tag(v___x_1948_) == 0 {
                                state = 17;
                                continue;
                            } else {
                                v_a_2032_ = leanh::lean_ctor_get(v___x_1948_, 0);
                                leanh::lean_inc(v_a_2032_);
                                v___x_2033_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__9;
                                leanh::lean_inc(v___x_1932_);
                                v___x_2034_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__5(v___x_1932_, v___x_2033_);
                                if leanh::lean_obj_tag(v___x_2034_) == 0 {
                                    leanh::lean_dec_ref_known(v___x_2034_, 1);
                                    leanh::lean_dec(v_a_2032_);
                                    state = 17;
                                    continue;
                                } else {
                                    leanh::lean_dec_ref_known(v___x_1948_, 1);
                                    v_a_2035_ = leanh::lean_ctor_get(v___x_2034_, 0);
                                    v_isSharedCheck_2056_ =
                                        (!leanh::lean_is_exclusive(v___x_2034_)) as u8;
                                    if v_isSharedCheck_2056_ == 0 {
                                        v___x_2037_ = v___x_2034_;
                                        v_isShared_2038_ = v_isSharedCheck_2056_;
                                        state = 22;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_2035_);
                                        leanh::lean_dec(v___x_2034_);
                                        v___x_2037_ = leanh::lean_box(0);
                                        v_isShared_2038_ = v_isSharedCheck_2056_;
                                        state = 22;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_1943_);
                        leanh::lean_dec(v___x_1932_);
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
                v___x_1925_ = leanh::lean_alloc_ctor(3, 3, (1) as u32);
                leanh::lean_ctor_set(v___x_1925_, 0, v___y_1921_);
                leanh::lean_ctor_set(v___x_1925_, 1, v___y_1922_);
                leanh::lean_ctor_set(v___x_1925_, 2, v___y_1924_);
                leanh::lean_ctor_set_uint8(
                    v___x_1925_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___y_1923_,
                );
                v___x_1926_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1926_, 0, v___x_1925_);
                return v___x_1926_;
            }
            3 => {
                v___x_1930_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1930_, 0, v___y_1928_);
                leanh::lean_ctor_set(v___x_1930_, 1, v___y_1929_);
                v___x_1931_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1931_, 0, v___x_1930_);
                return v___x_1931_;
            }
            4 => {
                if v_isShared_1938_ == 0 {
                    v___x_1940_ = v___x_1937_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1941_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1941_, 0, v_a_1935_);
                    v___x_1940_ = v_reuseFailAlloc_1941_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1940_;
            }
            6 => {
                if leanh::lean_obj_tag(v___x_1948_) == 0 {
                    leanh::lean_dec(v___x_1932_);
                    v_a_1950_ = leanh::lean_ctor_get(v___x_1948_, 0);
                    v_isSharedCheck_1957_ = (!leanh::lean_is_exclusive(v___x_1948_)) as u8;
                    if v_isSharedCheck_1957_ == 0 {
                        v___x_1952_ = v___x_1948_;
                        v_isShared_1953_ = v_isSharedCheck_1957_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1950_);
                        leanh::lean_dec(v___x_1948_);
                        v___x_1952_ = leanh::lean_box(0);
                        v_isShared_1953_ = v_isSharedCheck_1957_;
                        state = 7;
                        continue;
                    }
                } else {
                    v_a_1958_ = leanh::lean_ctor_get(v___x_1948_, 0);
                    leanh::lean_inc(v_a_1958_);
                    leanh::lean_dec_ref_known(v___x_1948_, 1);
                    v___x_1959_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__5;
                    v___x_1960_ = l_Lean_Json_getObjVal_x3f(v___x_1932_, v___x_1959_);
                    if leanh::lean_obj_tag(v___x_1960_) == 0 {
                        leanh::lean_dec(v_a_1958_);
                        v_a_1961_ = leanh::lean_ctor_get(v___x_1960_, 0);
                        v_isSharedCheck_1968_ =
                            (!leanh::lean_is_exclusive(v___x_1960_)) as u8;
                        if v_isSharedCheck_1968_ == 0 {
                            v___x_1963_ = v___x_1960_;
                            v_isShared_1964_ = v_isSharedCheck_1968_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1961_);
                            leanh::lean_dec(v___x_1960_);
                            v___x_1963_ = leanh::lean_box(0);
                            v_isShared_1964_ = v_isSharedCheck_1968_;
                            state = 9;
                            continue;
                        }
                    } else {
                        v_a_1969_ = leanh::lean_ctor_get(v___x_1960_, 0);
                        leanh::lean_inc_n(v_a_1969_, 2);
                        leanh::lean_dec_ref_known(v___x_1960_, 1);
                        v___x_1970_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__6;
                        v___x_1971_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4(v_a_1969_, v___x_1970_);
                        if leanh::lean_obj_tag(v___x_1971_) == 0 {
                            leanh::lean_dec(v_a_1969_);
                            leanh::lean_dec(v_a_1958_);
                            v_a_1972_ = leanh::lean_ctor_get(v___x_1971_, 0);
                            v_isSharedCheck_1979_ =
                                (!leanh::lean_is_exclusive(v___x_1971_)) as u8;
                            if v_isSharedCheck_1979_ == 0 {
                                v___x_1974_ = v___x_1971_;
                                v_isShared_1975_ = v_isSharedCheck_1979_;
                                state = 11;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1972_);
                                leanh::lean_dec(v___x_1971_);
                                v___x_1974_ = leanh::lean_box(0);
                                v_isShared_1975_ = v_isSharedCheck_1979_;
                                state = 11;
                                continue;
                            }
                        } else {
                            v_a_1980_ = leanh::lean_ctor_get(v___x_1971_, 0);
                            leanh::lean_inc(v_a_1980_);
                            leanh::lean_dec_ref_known(v___x_1971_, 1);
                            v___x_1981_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__7;
                            leanh::lean_inc(v_a_1969_);
                            v___x_1982_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__5(v_a_1969_, v___x_1981_);
                            if leanh::lean_obj_tag(v___x_1982_) == 0 {
                                leanh::lean_dec(v_a_1980_);
                                leanh::lean_dec(v_a_1969_);
                                leanh::lean_dec(v_a_1958_);
                                v_a_1983_ = leanh::lean_ctor_get(v___x_1982_, 0);
                                v_isSharedCheck_1990_ =
                                    (!leanh::lean_is_exclusive(v___x_1982_)) as u8;
                                if v_isSharedCheck_1990_ == 0 {
                                    v___x_1985_ = v___x_1982_;
                                    v_isShared_1986_ = v_isSharedCheck_1990_;
                                    state = 13;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1983_);
                                    leanh::lean_dec(v___x_1982_);
                                    v___x_1985_ = leanh::lean_box(0);
                                    v_isShared_1986_ = v_isSharedCheck_1990_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                v_a_1991_ = leanh::lean_ctor_get(v___x_1982_, 0);
                                leanh::lean_inc(v_a_1991_);
                                leanh::lean_dec_ref_known(v___x_1982_, 1);
                                v___x_1992_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__8;
                                v___x_1993_ = l_Lean_Json_getObjVal_x3f(v_a_1969_, v___x_1992_);
                                if leanh::lean_obj_tag(v___x_1993_) == 0 {
                                    leanh::lean_dec_ref_known(v___x_1993_, 1);
                                    v___x_1994_ = leanh::lean_box(0);
                                    v___x_1995_ = (leanh::lean_unbox(v_a_1980_) as u8);
                                    leanh::lean_dec(v_a_1980_);
                                    v___y_1921_ = v_a_1958_;
                                    v___y_1922_ = v_a_1991_;
                                    v___y_1923_ = v___x_1995_;
                                    v___y_1924_ = v___x_1994_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_a_1996_ = leanh::lean_ctor_get(v___x_1993_, 0);
                                    v_isSharedCheck_2004_ =
                                        (!leanh::lean_is_exclusive(v___x_1993_)) as u8;
                                    if v_isSharedCheck_2004_ == 0 {
                                        v___x_1998_ = v___x_1993_;
                                        v_isShared_1999_ = v_isSharedCheck_2004_;
                                        state = 15;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_1996_);
                                        leanh::lean_dec(v___x_1993_);
                                        v___x_1998_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_1956_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_a_1950_);
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
                    v_reuseFailAlloc_1967_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1967_, 0, v_a_1961_);
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
                    v_reuseFailAlloc_1978_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_a_1972_);
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
                    v_reuseFailAlloc_1989_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_a_1983_);
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
                    v_reuseFailAlloc_2003_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2003_, 0, v_a_1996_);
                    v___x_2001_ = v_reuseFailAlloc_2003_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___x_2002_ = (leanh::lean_unbox(v_a_1980_) as u8);
                leanh::lean_dec(v_a_1980_);
                v___y_1921_ = v_a_1958_;
                v___y_1922_ = v_a_1991_;
                v___y_1923_ = v___x_2002_;
                v___y_1924_ = v___x_2001_;
                state = 2;
                continue;
            }
            17 => {
                v___x_2006_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__9;
                leanh::lean_inc(v___x_1932_);
                v___x_2007_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__5(v___x_1932_, v___x_2006_);
                if leanh::lean_obj_tag(v___x_2007_) == 0 {
                    leanh::lean_dec_ref_known(v___x_2007_, 1);
                    if leanh::lean_obj_tag(v___x_1948_) == 0 {
                        state = 6;
                        continue;
                    } else {
                        v_a_2008_ = leanh::lean_ctor_get(v___x_1948_, 0);
                        leanh::lean_inc(v_a_2008_);
                        v___x_2009_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__10;
                        leanh::lean_inc(v___x_1932_);
                        v___x_2010_ = l_Lean_Json_getObjVal_x3f(v___x_1932_, v___x_2009_);
                        if leanh::lean_obj_tag(v___x_2010_) == 0 {
                            leanh::lean_dec_ref_known(v___x_2010_, 1);
                            leanh::lean_dec(v_a_2008_);
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_dec_ref_known(v___x_1948_, 1);
                            leanh::lean_dec(v___x_1932_);
                            v_a_2011_ = leanh::lean_ctor_get(v___x_2010_, 0);
                            v_isSharedCheck_2019_ =
                                (!leanh::lean_is_exclusive(v___x_2010_)) as u8;
                            if v_isSharedCheck_2019_ == 0 {
                                v___x_2013_ = v___x_2010_;
                                v_isShared_2014_ = v_isSharedCheck_2019_;
                                state = 18;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2011_);
                                leanh::lean_dec(v___x_2010_);
                                v___x_2013_ = leanh::lean_box(0);
                                v_isShared_2014_ = v_isSharedCheck_2019_;
                                state = 18;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___x_1948_);
                    v_a_2020_ = leanh::lean_ctor_get(v___x_2007_, 0);
                    leanh::lean_inc(v_a_2020_);
                    leanh::lean_dec_ref_known(v___x_2007_, 1);
                    v___x_2021_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__11;
                    v___x_2022_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__6(v___x_1932_, v___x_2021_);
                    if leanh::lean_obj_tag(v___x_2022_) == 0 {
                        leanh::lean_dec_ref_known(v___x_2022_, 1);
                        v___x_2023_ = leanh::lean_box(0);
                        v___y_1928_ = v_a_2020_;
                        v___y_1929_ = v___x_2023_;
                        state = 3;
                        continue;
                    } else {
                        v_a_2024_ = leanh::lean_ctor_get(v___x_2022_, 0);
                        v_isSharedCheck_2031_ =
                            (!leanh::lean_is_exclusive(v___x_2022_)) as u8;
                        if v_isSharedCheck_2031_ == 0 {
                            v___x_2026_ = v___x_2022_;
                            v_isShared_2027_ = v_isSharedCheck_2031_;
                            state = 20;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2024_);
                            leanh::lean_dec(v___x_2022_);
                            v___x_2026_ = leanh::lean_box(0);
                            v_isShared_2027_ = v_isSharedCheck_2031_;
                            state = 20;
                            continue;
                        }
                    }
                }
            }
            18 => {
                v___x_2015_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2015_, 0, v_a_2008_);
                leanh::lean_ctor_set(v___x_2015_, 1, v_a_2011_);
                if v_isShared_2014_ == 0 {
                    leanh::lean_ctor_set(v___x_2013_, 0, v___x_2015_);
                    v___x_2017_ = v___x_2013_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2018_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2018_, 0, v___x_2015_);
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
                    v_reuseFailAlloc_2030_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2030_, 0, v_a_2024_);
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
                if leanh::lean_obj_tag(v___x_2046_) == 0 {
                    leanh::lean_dec_ref_known(v___x_2046_, 1);
                    v___x_2047_ = leanh::lean_box(0);
                    v___y_2040_ = v___x_2047_;
                    state = 23;
                    continue;
                } else {
                    v_a_2048_ = leanh::lean_ctor_get(v___x_2046_, 0);
                    v_isSharedCheck_2055_ = (!leanh::lean_is_exclusive(v___x_2046_)) as u8;
                    if v_isSharedCheck_2055_ == 0 {
                        v___x_2050_ = v___x_2046_;
                        v_isShared_2051_ = v_isSharedCheck_2055_;
                        state = 25;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2048_);
                        leanh::lean_dec(v___x_2046_);
                        v___x_2050_ = leanh::lean_box(0);
                        v_isShared_2051_ = v_isSharedCheck_2055_;
                        state = 25;
                        continue;
                    }
                }
            }
            23 => {
                v___x_2041_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2041_, 0, v_a_2032_);
                leanh::lean_ctor_set(v___x_2041_, 1, v_a_2035_);
                leanh::lean_ctor_set(v___x_2041_, 2, v___y_2040_);
                if v_isShared_2038_ == 0 {
                    leanh::lean_ctor_set(v___x_2037_, 0, v___x_2041_);
                    v___x_2043_ = v___x_2037_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_2044_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2044_, 0, v___x_2041_);
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
                    v_reuseFailAlloc_2054_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_a_2048_);
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
    mut v_j_2057_: *mut leanh::LeanObject,
    mut v_k_2058_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2059_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2059_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3(v_j_2057_, v_k_2058_);
    leanh::lean_dec_ref(v_k_2058_);
    return v_res_2059_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_2093_: u8 = 0;
    let mut v___x_2094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2093_ = 1;
    v___x_2094_ = l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__14;
    v___x_2095_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2094_, v___x_2093_);
    return v___x_2095_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__16()
-> *mut leanh::LeanObject {
    let mut v___x_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2096_ = l_Lean_Server_Logging_LogConfig_ofLspLogConfig___closed__3;
    v___x_2097_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__15), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__15_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__15);
    v___x_2098_ = lean_string_append(v___x_2097_, v___x_2096_);
    return v___x_2098_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__18()
-> *mut leanh::LeanObject {
    let mut v___x_2101_: u8 = 0;
    let mut v___x_2102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2101_ = 1;
    v___x_2102_ = l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__17;
    v___x_2103_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2102_, v___x_2101_);
    return v___x_2103_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_2104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2104_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__18), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__18_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__18);
    v___x_2105_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__16), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__16_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__16);
    v___x_2106_ = lean_string_append(v___x_2105_, v___x_2104_);
    return v___x_2106_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__21()
-> *mut leanh::LeanObject {
    let mut v___x_2108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2108_ = l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__20;
    v___x_2109_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__19), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__19_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__19);
    v___x_2110_ = lean_string_append(v___x_2109_, v___x_2108_);
    return v___x_2110_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__24()
-> *mut leanh::LeanObject {
    let mut v___x_2114_: u8 = 0;
    let mut v___x_2115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2114_ = 1;
    v___x_2115_ = l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__23;
    v___x_2116_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2115_, v___x_2114_);
    return v___x_2116_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__25()
-> *mut leanh::LeanObject {
    let mut v___x_2117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2117_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__24), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__24_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__24);
    v___x_2118_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__16), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__16_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__16);
    v___x_2119_ = lean_string_append(v___x_2118_, v___x_2117_);
    return v___x_2119_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__26()
-> *mut leanh::LeanObject {
    let mut v___x_2120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2120_ = l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__20;
    v___x_2121_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__25), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__25_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__25);
    v___x_2122_ = lean_string_append(v___x_2121_, v___x_2120_);
    return v___x_2122_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__29()
-> *mut leanh::LeanObject {
    let mut v___x_2126_: u8 = 0;
    let mut v___x_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2126_ = 1;
    v___x_2127_ = l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__28;
    v___x_2128_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2127_, v___x_2126_);
    return v___x_2128_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__30()
-> *mut leanh::LeanObject {
    let mut v___x_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2129_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__29), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__29_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__29);
    v___x_2130_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__16), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__16_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__16);
    v___x_2131_ = lean_string_append(v___x_2130_, v___x_2129_);
    return v___x_2131_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__31()
-> *mut leanh::LeanObject {
    let mut v___x_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2132_ = l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__20;
    v___x_2133_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__30), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__30_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__30);
    v___x_2134_ = lean_string_append(v___x_2133_, v___x_2132_);
    return v___x_2134_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__34()
-> *mut leanh::LeanObject {
    let mut v___x_2138_: u8 = 0;
    let mut v___x_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2138_ = 1;
    v___x_2139_ = l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__33;
    v___x_2140_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2139_, v___x_2138_);
    return v___x_2140_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__35()
-> *mut leanh::LeanObject {
    let mut v___x_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2141_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__34), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__34_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__34);
    v___x_2142_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__16), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__16_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__16);
    v___x_2143_ = lean_string_append(v___x_2142_, v___x_2141_);
    return v___x_2143_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__36()
-> *mut leanh::LeanObject {
    let mut v___x_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2144_ = l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__20;
    v___x_2145_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__35), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__35_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__35);
    v___x_2146_ = lean_string_append(v___x_2145_, v___x_2144_);
    return v___x_2146_;
}
pub unsafe fn l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson(
    mut v_json_2147_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2153_: u8 = 0;
    let mut v___x_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2159_: u8 = 0;
    let mut v_a_2160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2163_: u8 = 0;
    let mut v___x_2165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2167_: u8 = 0;
    let mut v_a_2168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2174_: u8 = 0;
    let mut v___x_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2180_: u8 = 0;
    let mut v_a_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2184_: u8 = 0;
    let mut v___x_2186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2188_: u8 = 0;
    let mut v_a_2189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2195_: u8 = 0;
    let mut v___x_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2201_: u8 = 0;
    let mut v_a_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2205_: u8 = 0;
    let mut v___x_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2209_: u8 = 0;
    let mut v_a_2210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2216_: u8 = 0;
    let mut v___x_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2222_: u8 = 0;
    let mut v_a_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2226_: u8 = 0;
    let mut v___x_2228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2230_: u8 = 0;
    let mut v_a_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2234_: u8 = 0;
    let mut v___x_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: u8 = 0;
    let mut v___x_2237_: u8 = 0;
    let mut v___x_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2241_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2148_ = l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__0;
                leanh::lean_inc(v_json_2147_);
                v___x_2149_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__0(v_json_2147_, v___x_2148_);
                if leanh::lean_obj_tag(v___x_2149_) == 0 {
                    leanh::lean_dec(v_json_2147_);
                    v_a_2150_ = leanh::lean_ctor_get(v___x_2149_, 0);
                    v_isSharedCheck_2159_ = (!leanh::lean_is_exclusive(v___x_2149_)) as u8;
                    if v_isSharedCheck_2159_ == 0 {
                        v___x_2152_ = v___x_2149_;
                        v_isShared_2153_ = v_isSharedCheck_2159_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2150_);
                        leanh::lean_dec(v___x_2149_);
                        v___x_2152_ = leanh::lean_box(0);
                        v_isShared_2153_ = v_isSharedCheck_2159_;
                        state = 1;
                        continue;
                    }
                } else {
                    if leanh::lean_obj_tag(v___x_2149_) == 0 {
                        leanh::lean_dec(v_json_2147_);
                        v_a_2160_ = leanh::lean_ctor_get(v___x_2149_, 0);
                        v_isSharedCheck_2167_ =
                            (!leanh::lean_is_exclusive(v___x_2149_)) as u8;
                        if v_isSharedCheck_2167_ == 0 {
                            v___x_2162_ = v___x_2149_;
                            v_isShared_2163_ = v_isSharedCheck_2167_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2160_);
                            leanh::lean_dec(v___x_2149_);
                            v___x_2162_ = leanh::lean_box(0);
                            v_isShared_2163_ = v_isSharedCheck_2167_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_2168_ = leanh::lean_ctor_get(v___x_2149_, 0);
                        leanh::lean_inc(v_a_2168_);
                        leanh::lean_dec_ref_known(v___x_2149_, 1);
                        v___x_2169_ = l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__22;
                        leanh::lean_inc(v_json_2147_);
                        v___x_2170_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__1(v_json_2147_, v___x_2169_);
                        if leanh::lean_obj_tag(v___x_2170_) == 0 {
                            leanh::lean_dec(v_a_2168_);
                            leanh::lean_dec(v_json_2147_);
                            v_a_2171_ = leanh::lean_ctor_get(v___x_2170_, 0);
                            v_isSharedCheck_2180_ =
                                (!leanh::lean_is_exclusive(v___x_2170_)) as u8;
                            if v_isSharedCheck_2180_ == 0 {
                                v___x_2173_ = v___x_2170_;
                                v_isShared_2174_ = v_isSharedCheck_2180_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2171_);
                                leanh::lean_dec(v___x_2170_);
                                v___x_2173_ = leanh::lean_box(0);
                                v_isShared_2174_ = v_isSharedCheck_2180_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if leanh::lean_obj_tag(v___x_2170_) == 0 {
                                leanh::lean_dec(v_a_2168_);
                                leanh::lean_dec(v_json_2147_);
                                v_a_2181_ = leanh::lean_ctor_get(v___x_2170_, 0);
                                v_isSharedCheck_2188_ =
                                    (!leanh::lean_is_exclusive(v___x_2170_)) as u8;
                                if v_isSharedCheck_2188_ == 0 {
                                    v___x_2183_ = v___x_2170_;
                                    v_isShared_2184_ = v_isSharedCheck_2188_;
                                    state = 7;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2181_);
                                    leanh::lean_dec(v___x_2170_);
                                    v___x_2183_ = leanh::lean_box(0);
                                    v_isShared_2184_ = v_isSharedCheck_2188_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_2189_ = leanh::lean_ctor_get(v___x_2170_, 0);
                                leanh::lean_inc(v_a_2189_);
                                leanh::lean_dec_ref_known(v___x_2170_, 1);
                                v___x_2190_ = l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__27;
                                leanh::lean_inc(v_json_2147_);
                                v___x_2191_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__2(v_json_2147_, v___x_2190_);
                                if leanh::lean_obj_tag(v___x_2191_) == 0 {
                                    leanh::lean_dec(v_a_2189_);
                                    leanh::lean_dec(v_a_2168_);
                                    leanh::lean_dec(v_json_2147_);
                                    v_a_2192_ = leanh::lean_ctor_get(v___x_2191_, 0);
                                    v_isSharedCheck_2201_ =
                                        (!leanh::lean_is_exclusive(v___x_2191_)) as u8;
                                    if v_isSharedCheck_2201_ == 0 {
                                        v___x_2194_ = v___x_2191_;
                                        v_isShared_2195_ = v_isSharedCheck_2201_;
                                        state = 9;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_2192_);
                                        leanh::lean_dec(v___x_2191_);
                                        v___x_2194_ = leanh::lean_box(0);
                                        v_isShared_2195_ = v_isSharedCheck_2201_;
                                        state = 9;
                                        continue;
                                    }
                                } else {
                                    if leanh::lean_obj_tag(v___x_2191_) == 0 {
                                        leanh::lean_dec(v_a_2189_);
                                        leanh::lean_dec(v_a_2168_);
                                        leanh::lean_dec(v_json_2147_);
                                        v_a_2202_ = leanh::lean_ctor_get(v___x_2191_, 0);
                                        v_isSharedCheck_2209_ =
                                            (!leanh::lean_is_exclusive(v___x_2191_)) as u8;
                                        if v_isSharedCheck_2209_ == 0 {
                                            v___x_2204_ = v___x_2191_;
                                            v_isShared_2205_ = v_isSharedCheck_2209_;
                                            state = 11;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_2202_);
                                            leanh::lean_dec(v___x_2191_);
                                            v___x_2204_ = leanh::lean_box(0);
                                            v_isShared_2205_ = v_isSharedCheck_2209_;
                                            state = 11;
                                            continue;
                                        }
                                    } else {
                                        v_a_2210_ = leanh::lean_ctor_get(v___x_2191_, 0);
                                        leanh::lean_inc(v_a_2210_);
                                        leanh::lean_dec_ref_known(v___x_2191_, 1);
                                        v___x_2211_ = l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__32;
                                        v___x_2212_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3(v_json_2147_, v___x_2211_);
                                        if leanh::lean_obj_tag(v___x_2212_) == 0 {
                                            leanh::lean_dec(v_a_2210_);
                                            leanh::lean_dec(v_a_2189_);
                                            leanh::lean_dec(v_a_2168_);
                                            v_a_2213_ = leanh::lean_ctor_get(v___x_2212_, 0);
                                            v_isSharedCheck_2222_ =
                                                (!leanh::lean_is_exclusive(v___x_2212_))
                                                    as u8;
                                            if v_isSharedCheck_2222_ == 0 {
                                                v___x_2215_ = v___x_2212_;
                                                v_isShared_2216_ = v_isSharedCheck_2222_;
                                                state = 13;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_2213_);
                                                leanh::lean_dec(v___x_2212_);
                                                v___x_2215_ = leanh::lean_box(0);
                                                v_isShared_2216_ = v_isSharedCheck_2222_;
                                                state = 13;
                                                continue;
                                            }
                                        } else {
                                            if leanh::lean_obj_tag(v___x_2212_) == 0 {
                                                leanh::lean_dec(v_a_2210_);
                                                leanh::lean_dec(v_a_2189_);
                                                leanh::lean_dec(v_a_2168_);
                                                v_a_2223_ =
                                                    leanh::lean_ctor_get(v___x_2212_, 0);
                                                v_isSharedCheck_2230_ =
                                                    (!leanh::lean_is_exclusive(v___x_2212_))
                                                        as u8;
                                                if v_isSharedCheck_2230_ == 0 {
                                                    v___x_2225_ = v___x_2212_;
                                                    v_isShared_2226_ = v_isSharedCheck_2230_;
                                                    state = 15;
                                                    continue;
                                                } else {
                                                    leanh::lean_inc(v_a_2223_);
                                                    leanh::lean_dec(v___x_2212_);
                                                    v___x_2225_ = leanh::lean_box(0);
                                                    v_isShared_2226_ = v_isSharedCheck_2230_;
                                                    state = 15;
                                                    continue;
                                                }
                                            } else {
                                                v_a_2231_ =
                                                    leanh::lean_ctor_get(v___x_2212_, 0);
                                                v_isSharedCheck_2241_ =
                                                    (!leanh::lean_is_exclusive(v___x_2212_))
                                                        as u8;
                                                if v_isSharedCheck_2241_ == 0 {
                                                    v___x_2233_ = v___x_2212_;
                                                    v_isShared_2234_ = v_isSharedCheck_2241_;
                                                    state = 17;
                                                    continue;
                                                } else {
                                                    leanh::lean_inc(v_a_2231_);
                                                    leanh::lean_dec(v___x_2212_);
                                                    v___x_2233_ = leanh::lean_box(0);
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
                v___x_2154_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__21), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__21_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__21);
                v___x_2155_ = lean_string_append(v___x_2154_, v_a_2150_);
                leanh::lean_dec(v_a_2150_);
                if v_isShared_2153_ == 0 {
                    leanh::lean_ctor_set(v___x_2152_, 0, v___x_2155_);
                    v___x_2157_ = v___x_2152_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2158_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2158_, 0, v___x_2155_);
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
                    leanh::lean_ctor_set_tag(v___x_2162_, 0);
                    v___x_2165_ = v___x_2162_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2166_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2166_, 0, v_a_2160_);
                    v___x_2165_ = v_reuseFailAlloc_2166_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2165_;
            }
            5 => {
                v___x_2175_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__26), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__26_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__26);
                v___x_2176_ = lean_string_append(v___x_2175_, v_a_2171_);
                leanh::lean_dec(v_a_2171_);
                if v_isShared_2174_ == 0 {
                    leanh::lean_ctor_set(v___x_2173_, 0, v___x_2176_);
                    v___x_2178_ = v___x_2173_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2179_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2179_, 0, v___x_2176_);
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
                    leanh::lean_ctor_set_tag(v___x_2183_, 0);
                    v___x_2186_ = v___x_2183_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2187_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_a_2181_);
                    v___x_2186_ = v_reuseFailAlloc_2187_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2186_;
            }
            9 => {
                v___x_2196_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__31), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__31_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__31);
                v___x_2197_ = lean_string_append(v___x_2196_, v_a_2192_);
                leanh::lean_dec(v_a_2192_);
                if v_isShared_2195_ == 0 {
                    leanh::lean_ctor_set(v___x_2194_, 0, v___x_2197_);
                    v___x_2199_ = v___x_2194_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2200_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2200_, 0, v___x_2197_);
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
                    leanh::lean_ctor_set_tag(v___x_2204_, 0);
                    v___x_2207_ = v___x_2204_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2208_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2208_, 0, v_a_2202_);
                    v___x_2207_ = v_reuseFailAlloc_2208_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2207_;
            }
            13 => {
                v___x_2217_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__36), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__36_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__36);
                v___x_2218_ = lean_string_append(v___x_2217_, v_a_2213_);
                leanh::lean_dec(v_a_2213_);
                if v_isShared_2216_ == 0 {
                    leanh::lean_ctor_set(v___x_2215_, 0, v___x_2218_);
                    v___x_2220_ = v___x_2215_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2221_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2221_, 0, v___x_2218_);
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
                    leanh::lean_ctor_set_tag(v___x_2225_, 0);
                    v___x_2228_ = v___x_2225_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2229_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_a_2223_);
                    v___x_2228_ = v_reuseFailAlloc_2229_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2228_;
            }
            17 => {
                v___x_2235_ = leanh::lean_alloc_ctor(0, 2, (2) as u32);
                leanh::lean_ctor_set(v___x_2235_, 0, v_a_2168_);
                leanh::lean_ctor_set(v___x_2235_, 1, v_a_2231_);
                v___x_2236_ = (leanh::lean_unbox(v_a_2189_) as u8);
                leanh::lean_dec(v_a_2189_);
                leanh::lean_ctor_set_uint8(
                    v___x_2235_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_2236_,
                );
                v___x_2237_ = (leanh::lean_unbox(v_a_2210_) as u8);
                leanh::lean_dec(v_a_2210_);
                leanh::lean_ctor_set_uint8(
                    v___x_2235_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                    v___x_2237_,
                );
                if v_isShared_2234_ == 0 {
                    leanh::lean_ctor_set(v___x_2233_, 0, v___x_2235_);
                    v___x_2239_ = v___x_2233_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2240_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2240_, 0, v___x_2235_);
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
    mut v_k_2244_: *mut leanh::LeanObject,
    mut v_x_2245_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2245_) == 0 {
        let mut v___x_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_k_2244_);
        v___x_2246_ = leanh::lean_box(0);
        return v___x_2246_;
    } else {
        let mut v_val_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2248_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2249_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2250_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2251_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2247_ = leanh::lean_ctor_get(v_x_2245_, 0);
        leanh::lean_inc(v_val_2247_);
        leanh::lean_dec_ref_known(v_x_2245_, 1);
        v___x_2248_ = l_Lean_Json_Structured_toJson(v_val_2247_);
        v___x_2249_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2249_, 0, v_k_2244_);
        leanh::lean_ctor_set(v___x_2249_, 1, v___x_2248_);
        v___x_2250_ = leanh::lean_box(0);
        v___x_2251_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2251_, 0, v___x_2249_);
        leanh::lean_ctor_set(v___x_2251_, 1, v___x_2250_);
        return v___x_2251_;
    }
}
pub unsafe fn l_Lean_Json_opt___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson_spec__2(
    mut v_k_2252_: *mut leanh::LeanObject,
    mut v_x_2253_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2253_) == 0 {
        let mut v___x_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_k_2252_);
        v___x_2254_ = leanh::lean_box(0);
        return v___x_2254_;
    } else {
        let mut v_val_2255_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2256_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2257_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2258_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2255_ = leanh::lean_ctor_get(v_x_2253_, 0);
        leanh::lean_inc(v_val_2255_);
        v___x_2256_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2256_, 0, v_k_2252_);
        leanh::lean_ctor_set(v___x_2256_, 1, v_val_2255_);
        v___x_2257_ = leanh::lean_box(0);
        v___x_2258_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2258_, 0, v___x_2256_);
        leanh::lean_ctor_set(v___x_2258_, 1, v___x_2257_);
        return v___x_2258_;
    }
}
pub unsafe fn l_Lean_Json_opt___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson_spec__2___boxed(
    mut v_k_2259_: *mut leanh::LeanObject,
    mut v_x_2260_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2261_ = l_Lean_Json_opt___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson_spec__2(v_k_2259_, v_x_2260_);
    leanh::lean_dec(v_x_2260_);
    return v_res_2261_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson_spec__0(
    mut v_a_2262_: *mut leanh::LeanObject,
    mut v_a_2263_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_2262_) == 0 {
                    v___x_2264_ = lean_array_to_list(v_a_2263_);
                    return v___x_2264_;
                } else {
                    v_head_2265_ = leanh::lean_ctor_get(v_a_2262_, 0);
                    leanh::lean_inc(v_head_2265_);
                    v_tail_2266_ = leanh::lean_ctor_get(v_a_2262_, 1);
                    leanh::lean_inc(v_tail_2266_);
                    leanh::lean_dec_ref_known(v_a_2262_, 2);
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
-> *mut leanh::LeanObject {
    let mut v___x_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2276_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__3), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__3_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__3);
    v___x_2277_ = l_Lean_JsonNumber_fromInt(v___x_2276_);
    return v___x_2277_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2278_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__3_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__3);
    v___x_2279_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2279_, 0, v___x_2278_);
    return v___x_2279_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2280_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__5), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__5_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__5);
    v___x_2281_ = l_Lean_JsonNumber_fromInt(v___x_2280_);
    return v___x_2281_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_2282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2282_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__5_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__5);
    v___x_2283_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2283_, 0, v___x_2282_);
    return v___x_2283_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2284_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__7), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__7_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__7);
    v___x_2285_ = l_Lean_JsonNumber_fromInt(v___x_2284_);
    return v___x_2285_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_2286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2286_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__7_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__7);
    v___x_2287_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2287_, 0, v___x_2286_);
    return v___x_2287_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_2288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2288_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__9), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__9_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__9);
    v___x_2289_ = l_Lean_JsonNumber_fromInt(v___x_2288_);
    return v___x_2289_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2290_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__9_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__9);
    v___x_2291_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2291_, 0, v___x_2290_);
    return v___x_2291_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_2292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2292_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__11), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__11_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__11);
    v___x_2293_ = l_Lean_JsonNumber_fromInt(v___x_2292_);
    return v___x_2293_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_2294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2294_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__11_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__11);
    v___x_2295_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2295_, 0, v___x_2294_);
    return v___x_2295_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2296_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__13), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__13_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__13);
    v___x_2297_ = l_Lean_JsonNumber_fromInt(v___x_2296_);
    return v___x_2297_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__14()
-> *mut leanh::LeanObject {
    let mut v___x_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2298_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__13), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__13_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__13);
    v___x_2299_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2299_, 0, v___x_2298_);
    return v___x_2299_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2300_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__15), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__15_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__15);
    v___x_2301_ = l_Lean_JsonNumber_fromInt(v___x_2300_);
    return v___x_2301_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__16()
-> *mut leanh::LeanObject {
    let mut v___x_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2302_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__15), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__15_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__15);
    v___x_2303_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2303_, 0, v___x_2302_);
    return v___x_2303_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2304_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__17), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__17_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__17);
    v___x_2305_ = l_Lean_JsonNumber_fromInt(v___x_2304_);
    return v___x_2305_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__18()
-> *mut leanh::LeanObject {
    let mut v___x_2306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2306_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__17), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__17_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__17);
    v___x_2307_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2307_, 0, v___x_2306_);
    return v___x_2307_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2308_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__19), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__19_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__19);
    v___x_2309_ = l_Lean_JsonNumber_fromInt(v___x_2308_);
    return v___x_2309_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__20()
-> *mut leanh::LeanObject {
    let mut v___x_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2310_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__19), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__19_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__19);
    v___x_2311_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2311_, 0, v___x_2310_);
    return v___x_2311_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__21()
-> *mut leanh::LeanObject {
    let mut v___x_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2312_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__21), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__21_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__21);
    v___x_2313_ = l_Lean_JsonNumber_fromInt(v___x_2312_);
    return v___x_2313_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__22()
-> *mut leanh::LeanObject {
    let mut v___x_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2314_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__21), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__21_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__21);
    v___x_2315_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2315_, 0, v___x_2314_);
    return v___x_2315_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__23()
-> *mut leanh::LeanObject {
    let mut v___x_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2316_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__23), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__23_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__23);
    v___x_2317_ = l_Lean_JsonNumber_fromInt(v___x_2316_);
    return v___x_2317_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__24()
-> *mut leanh::LeanObject {
    let mut v___x_2318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2318_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__23), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__23_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__23);
    v___x_2319_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2319_, 0, v___x_2318_);
    return v___x_2319_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__25()
-> *mut leanh::LeanObject {
    let mut v___x_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2320_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__25), core::ptr::addr_of_mut!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__25_once), _init_l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3_spec__4___closed__25);
    v___x_2321_ = l_Lean_JsonNumber_fromInt(v___x_2320_);
    return v___x_2321_;
}
pub unsafe fn _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__26()
-> *mut leanh::LeanObject {
    let mut v___x_2322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2322_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__25), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__25_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__25);
    v___x_2323_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2323_, 0, v___x_2322_);
    return v___x_2323_;
}
pub unsafe fn l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson(
    mut v_x_2324_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_time_2325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_direction_2326_: u8 = 0;
    let mut v_kind_2327_: u8 = 0;
    let mut v_msg_2328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_2358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_method_2359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_x3f_2360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_2373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2376_: u8 = 0;
    let mut v___x_2378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2380_: u8 = 0;
    let mut v_n_2381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2384_: u8 = 0;
    let mut v___x_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2388_: u8 = 0;
    let mut v___x_2389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_method_2390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_x3f_2391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2394_: u8 = 0;
    let mut v___x_2395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2403_: u8 = 0;
    let mut v_id_2404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_2405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2408_: u8 = 0;
    let mut v___x_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_2419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2422_: u8 = 0;
    let mut v___x_2424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2426_: u8 = 0;
    let mut v_n_2427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2430_: u8 = 0;
    let mut v___x_2432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2434_: u8 = 0;
    let mut v___x_2435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2436_: u8 = 0;
    let mut v_id_2437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_2438_: u8 = 0;
    let mut v_message_2439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_x3f_2440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_2477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2480_: u8 = 0;
    let mut v___x_2482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2484_: u8 = 0;
    let mut v_n_2485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2488_: u8 = 0;
    let mut v___x_2490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2492_: u8 = 0;
    let mut v___x_2493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_time_2325_ = leanh::lean_ctor_get(v_x_2324_, 0);
                leanh::lean_inc_ref(v_time_2325_);
                v_direction_2326_ = leanh::lean_ctor_get_uint8(
                    v_x_2324_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                );
                v_kind_2327_ = leanh::lean_ctor_get_uint8(
                    v_x_2324_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                );
                v_msg_2328_ = leanh::lean_ctor_get(v_x_2324_, 1);
                leanh::lean_inc_ref(v_msg_2328_);
                leanh::lean_dec_ref(v_x_2324_);
                v___x_2329_ = l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__0;
                v___x_2330_ = l_Std_Time_ZonedDateTime_toISO8601String(v_time_2325_);
                v___x_2331_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2331_, 0, v___x_2330_);
                v___x_2332_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2332_, 0, v___x_2329_);
                leanh::lean_ctor_set(v___x_2332_, 1, v___x_2331_);
                v___x_2333_ = leanh::lean_box(0);
                v___x_2334_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2334_, 0, v___x_2332_);
                leanh::lean_ctor_set(v___x_2334_, 1, v___x_2333_);
                v___x_2335_ = l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__22;
                v___x_2336_ = l_Lean_JsonRpc_instToJsonMessageDirection_toJson(v_direction_2326_);
                v___x_2337_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2337_, 0, v___x_2335_);
                leanh::lean_ctor_set(v___x_2337_, 1, v___x_2336_);
                v___x_2338_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2338_, 0, v___x_2337_);
                leanh::lean_ctor_set(v___x_2338_, 1, v___x_2333_);
                v___x_2339_ = l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__27;
                v___x_2340_ = l_Lean_JsonRpc_instToJsonMessageKind_toJson(v_kind_2327_);
                v___x_2341_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2341_, 0, v___x_2339_);
                leanh::lean_ctor_set(v___x_2341_, 1, v___x_2340_);
                v___x_2342_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2342_, 0, v___x_2341_);
                leanh::lean_ctor_set(v___x_2342_, 1, v___x_2333_);
                v___x_2343_ = l___private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson___closed__32;
                v___x_2344_ = l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__1;
                match leanh::lean_obj_tag(v_msg_2328_) {
                    0 => {
                        v_id_2358_ = leanh::lean_ctor_get(v_msg_2328_, 0);
                        leanh::lean_inc(v_id_2358_);
                        v_method_2359_ = leanh::lean_ctor_get(v_msg_2328_, 1);
                        leanh::lean_inc_ref(v_method_2359_);
                        v_params_x3f_2360_ = leanh::lean_ctor_get(v_msg_2328_, 2);
                        leanh::lean_inc(v_params_x3f_2360_);
                        leanh::lean_dec_ref_known(v_msg_2328_, 3);
                        v___x_2361_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__4;
                        match leanh::lean_obj_tag(v_id_2358_) {
                            0 => {
                                v_s_2373_ = leanh::lean_ctor_get(v_id_2358_, 0);
                                v_isSharedCheck_2380_ =
                                    (!leanh::lean_is_exclusive(v_id_2358_)) as u8;
                                if v_isSharedCheck_2380_ == 0 {
                                    v___x_2375_ = v_id_2358_;
                                    v_isShared_2376_ = v_isSharedCheck_2380_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_s_2373_);
                                    leanh::lean_dec(v_id_2358_);
                                    v___x_2375_ = leanh::lean_box(0);
                                    v_isShared_2376_ = v_isSharedCheck_2380_;
                                    state = 3;
                                    continue;
                                }
                            }
                            1 => {
                                v_n_2381_ = leanh::lean_ctor_get(v_id_2358_, 0);
                                v_isSharedCheck_2388_ =
                                    (!leanh::lean_is_exclusive(v_id_2358_)) as u8;
                                if v_isSharedCheck_2388_ == 0 {
                                    v___x_2383_ = v_id_2358_;
                                    v_isShared_2384_ = v_isSharedCheck_2388_;
                                    state = 5;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_n_2381_);
                                    leanh::lean_dec(v_id_2358_);
                                    v___x_2383_ = leanh::lean_box(0);
                                    v_isShared_2384_ = v_isSharedCheck_2388_;
                                    state = 5;
                                    continue;
                                }
                            }
                            _ => {
                                v___x_2389_ = leanh::lean_box(0);
                                v___y_2363_ = v___x_2389_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                    1 => {
                        v_method_2390_ = leanh::lean_ctor_get(v_msg_2328_, 0);
                        v_params_x3f_2391_ = leanh::lean_ctor_get(v_msg_2328_, 1);
                        v_isSharedCheck_2403_ =
                            (!leanh::lean_is_exclusive(v_msg_2328_)) as u8;
                        if v_isSharedCheck_2403_ == 0 {
                            v___x_2393_ = v_msg_2328_;
                            v_isShared_2394_ = v_isSharedCheck_2403_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_params_x3f_2391_);
                            leanh::lean_inc(v_method_2390_);
                            leanh::lean_dec(v_msg_2328_);
                            v___x_2393_ = leanh::lean_box(0);
                            v_isShared_2394_ = v_isSharedCheck_2403_;
                            state = 7;
                            continue;
                        }
                    }
                    2 => {
                        v_id_2404_ = leanh::lean_ctor_get(v_msg_2328_, 0);
                        v_result_2405_ = leanh::lean_ctor_get(v_msg_2328_, 1);
                        v_isSharedCheck_2436_ =
                            (!leanh::lean_is_exclusive(v_msg_2328_)) as u8;
                        if v_isSharedCheck_2436_ == 0 {
                            v___x_2407_ = v_msg_2328_;
                            v_isShared_2408_ = v_isSharedCheck_2436_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_result_2405_);
                            leanh::lean_inc(v_id_2404_);
                            leanh::lean_dec(v_msg_2328_);
                            v___x_2407_ = leanh::lean_box(0);
                            v_isShared_2408_ = v_isSharedCheck_2436_;
                            state = 9;
                            continue;
                        }
                    }
                    _ => {
                        v_id_2437_ = leanh::lean_ctor_get(v_msg_2328_, 0);
                        leanh::lean_inc(v_id_2437_);
                        v_code_2438_ = leanh::lean_ctor_get_uint8(
                            v_msg_2328_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        );
                        v_message_2439_ = leanh::lean_ctor_get(v_msg_2328_, 1);
                        leanh::lean_inc_ref(v_message_2439_);
                        v_data_x3f_2440_ = leanh::lean_ctor_get(v_msg_2328_, 2);
                        leanh::lean_inc(v_data_x3f_2440_);
                        leanh::lean_dec_ref_known(v_msg_2328_, 3);
                        v___x_2459_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__4;
                        match leanh::lean_obj_tag(v_id_2437_) {
                            0 => {
                                v_s_2477_ = leanh::lean_ctor_get(v_id_2437_, 0);
                                v_isSharedCheck_2484_ =
                                    (!leanh::lean_is_exclusive(v_id_2437_)) as u8;
                                if v_isSharedCheck_2484_ == 0 {
                                    v___x_2479_ = v_id_2437_;
                                    v_isShared_2480_ = v_isSharedCheck_2484_;
                                    state = 18;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_s_2477_);
                                    leanh::lean_dec(v_id_2437_);
                                    v___x_2479_ = leanh::lean_box(0);
                                    v_isShared_2480_ = v_isSharedCheck_2484_;
                                    state = 18;
                                    continue;
                                }
                            }
                            1 => {
                                v_n_2485_ = leanh::lean_ctor_get(v_id_2437_, 0);
                                v_isSharedCheck_2492_ =
                                    (!leanh::lean_is_exclusive(v_id_2437_)) as u8;
                                if v_isSharedCheck_2492_ == 0 {
                                    v___x_2487_ = v_id_2437_;
                                    v_isShared_2488_ = v_isSharedCheck_2492_;
                                    state = 20;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_n_2485_);
                                    leanh::lean_dec(v_id_2437_);
                                    v___x_2487_ = leanh::lean_box(0);
                                    v_isShared_2488_ = v_isSharedCheck_2492_;
                                    state = 20;
                                    continue;
                                }
                            }
                            _ => {
                                v___x_2493_ = leanh::lean_box(0);
                                v___y_2461_ = v___x_2493_;
                                state = 17;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_2347_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2347_, 0, v___x_2344_);
                leanh::lean_ctor_set(v___x_2347_, 1, v___y_2346_);
                v___x_2348_ = l_Lean_Json_mkObj(v___x_2347_);
                leanh::lean_dec_ref_known(v___x_2347_, 2);
                v___x_2349_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2349_, 0, v___x_2343_);
                leanh::lean_ctor_set(v___x_2349_, 1, v___x_2348_);
                v___x_2350_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2350_, 0, v___x_2349_);
                leanh::lean_ctor_set(v___x_2350_, 1, v___x_2333_);
                v___x_2351_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2351_, 0, v___x_2350_);
                leanh::lean_ctor_set(v___x_2351_, 1, v___x_2333_);
                v___x_2352_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2352_, 0, v___x_2342_);
                leanh::lean_ctor_set(v___x_2352_, 1, v___x_2351_);
                v___x_2353_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2353_, 0, v___x_2338_);
                leanh::lean_ctor_set(v___x_2353_, 1, v___x_2352_);
                v___x_2354_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2354_, 0, v___x_2334_);
                leanh::lean_ctor_set(v___x_2354_, 1, v___x_2353_);
                v___x_2355_ = l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__2;
                v___x_2356_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson_spec__0(v___x_2354_, v___x_2355_);
                v___x_2357_ = l_Lean_Json_mkObj(v___x_2356_);
                leanh::lean_dec(v___x_2356_);
                return v___x_2357_;
            }
            2 => {
                v___x_2364_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2364_, 0, v___x_2361_);
                leanh::lean_ctor_set(v___x_2364_, 1, v___y_2363_);
                v___x_2365_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__9;
                v___x_2366_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2366_, 0, v_method_2359_);
                v___x_2367_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2367_, 0, v___x_2365_);
                leanh::lean_ctor_set(v___x_2367_, 1, v___x_2366_);
                v___x_2368_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2368_, 0, v___x_2367_);
                leanh::lean_ctor_set(v___x_2368_, 1, v___x_2333_);
                v___x_2369_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2369_, 0, v___x_2364_);
                leanh::lean_ctor_set(v___x_2369_, 1, v___x_2368_);
                v___x_2370_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__11;
                v___x_2371_ = l_Lean_Json_opt___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson_spec__1(v___x_2370_, v_params_x3f_2360_);
                v___x_2372_ = l_List_appendTR___redArg(v___x_2369_, v___x_2371_);
                v___y_2346_ = v___x_2372_;
                state = 1;
                continue;
            }
            3 => {
                if v_isShared_2376_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2375_, 3);
                    v___x_2378_ = v___x_2375_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2379_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_s_2373_);
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
                    leanh::lean_ctor_set_tag(v___x_2383_, 2);
                    v___x_2386_ = v___x_2383_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2387_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2387_, 0, v_n_2381_);
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
                v___x_2396_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2396_, 0, v_method_2390_);
                if v_isShared_2394_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2393_, 0);
                    leanh::lean_ctor_set(v___x_2393_, 1, v___x_2396_);
                    leanh::lean_ctor_set(v___x_2393_, 0, v___x_2395_);
                    v___x_2398_ = v___x_2393_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2402_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2402_, 0, v___x_2395_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2402_, 1, v___x_2396_);
                    v___x_2398_ = v_reuseFailAlloc_2402_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2399_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__11;
                v___x_2400_ = l_Lean_Json_opt___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson_spec__1(v___x_2399_, v_params_x3f_2391_);
                v___x_2401_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2401_, 0, v___x_2398_);
                leanh::lean_ctor_set(v___x_2401_, 1, v___x_2400_);
                v___y_2346_ = v___x_2401_;
                state = 1;
                continue;
            }
            9 => {
                v___x_2409_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__4;
                match leanh::lean_obj_tag(v_id_2404_) {
                    0 => {
                        v_s_2419_ = leanh::lean_ctor_get(v_id_2404_, 0);
                        v_isSharedCheck_2426_ =
                            (!leanh::lean_is_exclusive(v_id_2404_)) as u8;
                        if v_isSharedCheck_2426_ == 0 {
                            v___x_2421_ = v_id_2404_;
                            v_isShared_2422_ = v_isSharedCheck_2426_;
                            state = 12;
                            continue;
                        } else {
                            leanh::lean_inc(v_s_2419_);
                            leanh::lean_dec(v_id_2404_);
                            v___x_2421_ = leanh::lean_box(0);
                            v_isShared_2422_ = v_isSharedCheck_2426_;
                            state = 12;
                            continue;
                        }
                    }
                    1 => {
                        v_n_2427_ = leanh::lean_ctor_get(v_id_2404_, 0);
                        v_isSharedCheck_2434_ =
                            (!leanh::lean_is_exclusive(v_id_2404_)) as u8;
                        if v_isSharedCheck_2434_ == 0 {
                            v___x_2429_ = v_id_2404_;
                            v_isShared_2430_ = v_isSharedCheck_2434_;
                            state = 14;
                            continue;
                        } else {
                            leanh::lean_inc(v_n_2427_);
                            leanh::lean_dec(v_id_2404_);
                            v___x_2429_ = leanh::lean_box(0);
                            v_isShared_2430_ = v_isSharedCheck_2434_;
                            state = 14;
                            continue;
                        }
                    }
                    _ => {
                        v___x_2435_ = leanh::lean_box(0);
                        v___y_2411_ = v___x_2435_;
                        state = 10;
                        continue;
                    }
                }
            }
            10 => {
                if v_isShared_2408_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2407_, 0);
                    leanh::lean_ctor_set(v___x_2407_, 1, v___y_2411_);
                    leanh::lean_ctor_set(v___x_2407_, 0, v___x_2409_);
                    v___x_2413_ = v___x_2407_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2418_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2418_, 0, v___x_2409_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2418_, 1, v___y_2411_);
                    v___x_2413_ = v_reuseFailAlloc_2418_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_2414_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__10;
                v___x_2415_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2415_, 0, v___x_2414_);
                leanh::lean_ctor_set(v___x_2415_, 1, v_result_2405_);
                v___x_2416_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2416_, 0, v___x_2415_);
                leanh::lean_ctor_set(v___x_2416_, 1, v___x_2333_);
                v___x_2417_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2417_, 0, v___x_2413_);
                leanh::lean_ctor_set(v___x_2417_, 1, v___x_2416_);
                v___y_2346_ = v___x_2417_;
                state = 1;
                continue;
            }
            12 => {
                if v_isShared_2422_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2421_, 3);
                    v___x_2424_ = v___x_2421_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2425_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2425_, 0, v_s_2419_);
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
                    leanh::lean_ctor_set_tag(v___x_2429_, 2);
                    v___x_2432_ = v___x_2429_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2433_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2433_, 0, v_n_2427_);
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
                leanh::lean_inc(v___y_2445_);
                leanh::lean_inc_ref(v___y_2442_);
                v___x_2446_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2446_, 0, v___y_2442_);
                leanh::lean_ctor_set(v___x_2446_, 1, v___y_2445_);
                v___x_2447_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__7;
                v___x_2448_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2448_, 0, v_message_2439_);
                v___x_2449_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2449_, 0, v___x_2447_);
                leanh::lean_ctor_set(v___x_2449_, 1, v___x_2448_);
                v___x_2450_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2450_, 0, v___x_2449_);
                leanh::lean_ctor_set(v___x_2450_, 1, v___x_2333_);
                v___x_2451_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2451_, 0, v___x_2446_);
                leanh::lean_ctor_set(v___x_2451_, 1, v___x_2450_);
                v___x_2452_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__8;
                v___x_2453_ = l_Lean_Json_opt___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson_spec__2(v___x_2452_, v_data_x3f_2440_);
                leanh::lean_dec(v_data_x3f_2440_);
                v___x_2454_ = l_List_appendTR___redArg(v___x_2451_, v___x_2453_);
                v___x_2455_ = l_Lean_Json_mkObj(v___x_2454_);
                leanh::lean_dec(v___x_2454_);
                leanh::lean_inc_ref(v___y_2443_);
                v___x_2456_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2456_, 0, v___y_2443_);
                leanh::lean_ctor_set(v___x_2456_, 1, v___x_2455_);
                v___x_2457_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2457_, 0, v___x_2456_);
                leanh::lean_ctor_set(v___x_2457_, 1, v___x_2333_);
                v___x_2458_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2458_, 0, v___y_2444_);
                leanh::lean_ctor_set(v___x_2458_, 1, v___x_2457_);
                v___y_2346_ = v___x_2458_;
                state = 1;
                continue;
            }
            17 => {
                v___x_2462_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2462_, 0, v___x_2459_);
                leanh::lean_ctor_set(v___x_2462_, 1, v___y_2461_);
                v___x_2463_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__5;
                v___x_2464_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Server_Logging_0__Lean_Server_Logging_instFromJsonLogEntry_fromJson_spec__3___closed__6;
                match v_code_2438_ {
                    0 => {
                        v___x_2465_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__4_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__4);
                        v___y_2442_ = v___x_2464_;
                        v___y_2443_ = v___x_2463_;
                        v___y_2444_ = v___x_2462_;
                        v___y_2445_ = v___x_2465_;
                        state = 16;
                        continue;
                    }
                    1 => {
                        v___x_2466_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__6_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__6);
                        v___y_2442_ = v___x_2464_;
                        v___y_2443_ = v___x_2463_;
                        v___y_2444_ = v___x_2462_;
                        v___y_2445_ = v___x_2466_;
                        state = 16;
                        continue;
                    }
                    2 => {
                        v___x_2467_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__8_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__8);
                        v___y_2442_ = v___x_2464_;
                        v___y_2443_ = v___x_2463_;
                        v___y_2444_ = v___x_2462_;
                        v___y_2445_ = v___x_2467_;
                        state = 16;
                        continue;
                    }
                    3 => {
                        v___x_2468_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__10_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__10);
                        v___y_2442_ = v___x_2464_;
                        v___y_2443_ = v___x_2463_;
                        v___y_2444_ = v___x_2462_;
                        v___y_2445_ = v___x_2468_;
                        state = 16;
                        continue;
                    }
                    4 => {
                        v___x_2469_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__12), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__12_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__12);
                        v___y_2442_ = v___x_2464_;
                        v___y_2443_ = v___x_2463_;
                        v___y_2444_ = v___x_2462_;
                        v___y_2445_ = v___x_2469_;
                        state = 16;
                        continue;
                    }
                    5 => {
                        v___x_2470_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__14), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__14_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__14);
                        v___y_2442_ = v___x_2464_;
                        v___y_2443_ = v___x_2463_;
                        v___y_2444_ = v___x_2462_;
                        v___y_2445_ = v___x_2470_;
                        state = 16;
                        continue;
                    }
                    6 => {
                        v___x_2471_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__16), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__16_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__16);
                        v___y_2442_ = v___x_2464_;
                        v___y_2443_ = v___x_2463_;
                        v___y_2444_ = v___x_2462_;
                        v___y_2445_ = v___x_2471_;
                        state = 16;
                        continue;
                    }
                    7 => {
                        v___x_2472_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__18), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__18_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__18);
                        v___y_2442_ = v___x_2464_;
                        v___y_2443_ = v___x_2463_;
                        v___y_2444_ = v___x_2462_;
                        v___y_2445_ = v___x_2472_;
                        state = 16;
                        continue;
                    }
                    8 => {
                        v___x_2473_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__20), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__20_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__20);
                        v___y_2442_ = v___x_2464_;
                        v___y_2443_ = v___x_2463_;
                        v___y_2444_ = v___x_2462_;
                        v___y_2445_ = v___x_2473_;
                        state = 16;
                        continue;
                    }
                    9 => {
                        v___x_2474_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__22), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__22_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__22);
                        v___y_2442_ = v___x_2464_;
                        v___y_2443_ = v___x_2463_;
                        v___y_2444_ = v___x_2462_;
                        v___y_2445_ = v___x_2474_;
                        state = 16;
                        continue;
                    }
                    10 => {
                        v___x_2475_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__24), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__24_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__24);
                        v___y_2442_ = v___x_2464_;
                        v___y_2443_ = v___x_2463_;
                        v___y_2444_ = v___x_2462_;
                        v___y_2445_ = v___x_2475_;
                        state = 16;
                        continue;
                    }
                    _ => {
                        v___x_2476_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__26), core::ptr::addr_of_mut!(l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__26_once), _init_l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson___closed__26);
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
                    leanh::lean_ctor_set_tag(v___x_2479_, 3);
                    v___x_2482_ = v___x_2479_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2483_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_s_2477_);
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
                    leanh::lean_ctor_set_tag(v___x_2487_, 2);
                    v___x_2490_ = v___x_2487_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_2491_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_n_2485_);
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
    mut v_cfg_2496_: *mut leanh::LeanObject,
    mut v_pending_2497_: *mut leanh::LeanObject,
    mut v_log_2498_: *mut leanh::LeanObject,
    mut v_direction_2499_: u8,
    mut v_msg_2500_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2502_: u8 = 0;
    let mut v___x_2503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: u8 = 0;
    let mut v___x_2515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initialLocalTimeType_2520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_transitions_2521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2528_: u8 = 0;
    let mut v___x_2530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2532_: u8 = 0;
    let mut v_a_2533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2536_: u8 = 0;
    let mut v___x_2538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2540_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_msg_2500_);
                v___x_2502_ = l___private_Lean_Server_Logging_0__Lean_Server_Logging_isMsgAllowed(
                    v_cfg_2496_,
                    v_pending_2497_,
                    v_msg_2500_,
                );
                if v___x_2502_ == 0 {
                    leanh::lean_dec_ref(v_msg_2500_);
                    v___x_2503_ = leanh::lean_box(0);
                    v___x_2504_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2504_, 0, v___x_2503_);
                    return v___x_2504_;
                } else {
                    v___x_2505_ = lean_get_current_time();
                    if leanh::lean_obj_tag(v___x_2505_) == 0 {
                        v_a_2506_ = leanh::lean_ctor_get(v___x_2505_, 0);
                        leanh::lean_inc(v_a_2506_);
                        leanh::lean_dec_ref_known(v___x_2505_, 1);
                        v___x_2507_ = l_Std_Time_Database_defaultGetLocalZoneRules();
                        if leanh::lean_obj_tag(v___x_2507_) == 0 {
                            v_a_2508_ = leanh::lean_ctor_get(v___x_2507_, 0);
                            leanh::lean_inc(v_a_2508_);
                            leanh::lean_dec_ref_known(v___x_2507_, 1);
                            v_initialLocalTimeType_2520_ =
                                leanh::lean_ctor_get(v_a_2508_, 0);
                            v_transitions_2521_ = leanh::lean_ctor_get(v_a_2508_, 1);
                            v___x_2522_ = l_Std_Time_TimeZone_Transition_timezoneAt(
                                v_transitions_2521_,
                                v_a_2506_,
                            );
                            if leanh::lean_obj_tag(v___x_2522_) == 0 {
                                leanh::lean_dec_ref_known(v___x_2522_, 1);
                                v___x_2523_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(
                                    v_initialLocalTimeType_2520_,
                                );
                                v___y_2510_ = v___x_2523_;
                                state = 1;
                                continue;
                            } else {
                                v_a_2524_ = leanh::lean_ctor_get(v___x_2522_, 0);
                                leanh::lean_inc(v_a_2524_);
                                leanh::lean_dec_ref_known(v___x_2522_, 1);
                                v___y_2510_ = v_a_2524_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_2506_);
                            leanh::lean_dec_ref(v_msg_2500_);
                            v_a_2525_ = leanh::lean_ctor_get(v___x_2507_, 0);
                            v_isSharedCheck_2532_ =
                                (!leanh::lean_is_exclusive(v___x_2507_)) as u8;
                            if v_isSharedCheck_2532_ == 0 {
                                v___x_2527_ = v___x_2507_;
                                v_isShared_2528_ = v_isSharedCheck_2532_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2525_);
                                leanh::lean_dec(v___x_2507_);
                                v___x_2527_ = leanh::lean_box(0);
                                v_isShared_2528_ = v_isSharedCheck_2532_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_msg_2500_);
                        v_a_2533_ = leanh::lean_ctor_get(v___x_2505_, 0);
                        v_isSharedCheck_2540_ =
                            (!leanh::lean_is_exclusive(v___x_2505_)) as u8;
                        if v_isSharedCheck_2540_ == 0 {
                            v___x_2535_ = v___x_2505_;
                            v_isShared_2536_ = v_isSharedCheck_2540_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2533_);
                            leanh::lean_dec(v___x_2505_);
                            v___x_2535_ = leanh::lean_box(0);
                            v_isShared_2536_ = v_isSharedCheck_2540_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_a_2506_);
                leanh::lean_inc_ref(v___y_2510_);
                v___f_2511_ = leanh::lean_alloc_closure(
                    l_Lean_Server_Logging_LogConfig_ofLspLogConfig___lam__0___boxed
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___f_2511_, 0, v___y_2510_);
                leanh::lean_closure_set(v___f_2511_, 1, v_a_2506_);
                v___x_2512_ = lean_mk_thunk(v___f_2511_);
                v___x_2513_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_2513_, 0, v___x_2512_);
                leanh::lean_ctor_set(v___x_2513_, 1, v_a_2506_);
                leanh::lean_ctor_set(v___x_2513_, 2, v_a_2508_);
                leanh::lean_ctor_set(v___x_2513_, 3, v___y_2510_);
                v___x_2514_ = l_Lean_JsonRpc_MessageKind_ofMessage(v_msg_2500_);
                v___x_2515_ = leanh::lean_alloc_ctor(0, 2, (2) as u32);
                leanh::lean_ctor_set(v___x_2515_, 0, v___x_2513_);
                leanh::lean_ctor_set(v___x_2515_, 1, v_msg_2500_);
                leanh::lean_ctor_set_uint8(
                    v___x_2515_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v_direction_2499_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2515_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                    v___x_2514_,
                );
                v___x_2516_ = l___private_Lean_Server_Logging_0__Lean_Server_Logging_instToJsonLogEntry_toJson(v___x_2515_);
                v___x_2517_ = l_Lean_Json_compress(v___x_2516_);
                v___x_2518_ = l_IO_FS_Handle_putStrLn(v_log_2498_, v___x_2517_);
                if leanh::lean_obj_tag(v___x_2518_) == 0 {
                    leanh::lean_dec_ref_known(v___x_2518_, 1);
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
                    v_reuseFailAlloc_2531_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2531_, 0, v_a_2525_);
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
                    v_reuseFailAlloc_2539_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2539_, 0, v_a_2533_);
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
    mut v_cfg_2541_: *mut leanh::LeanObject,
    mut v_pending_2542_: *mut leanh::LeanObject,
    mut v_log_2543_: *mut leanh::LeanObject,
    mut v_direction_2544_: *mut leanh::LeanObject,
    mut v_msg_2545_: *mut leanh::LeanObject,
    mut v_a_2546_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_direction_boxed_2547_: u8 = 0;
    let mut v_res_2548_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_direction_boxed_2547_ = (leanh::lean_unbox(v_direction_2544_) as u8);
    v_res_2548_ = l_Lean_Server_Logging_writeLogEntry(
        v_cfg_2541_,
        v_pending_2542_,
        v_log_2543_,
        v_direction_boxed_2547_,
        v_msg_2545_,
    );
    leanh::lean_dec(v_log_2543_);
    leanh::lean_dec_ref(v_pending_2542_);
    leanh::lean_dec_ref(v_cfg_2541_);
    return v_res_2548_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Server_Logging(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Time(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Lsp_InitShutdown(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Server_Logging(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Server_Logging(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Time(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Data_Lsp_InitShutdown(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_Logging(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Server_Logging(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Server_Logging(builtin);
}