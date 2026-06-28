// Lean compiler output
// Module: Lean.Log
// Imports: Lean.ErrorExplanation
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f,
    l_Lean_replaceRef,
};
use crate::r#gen::Lean::Data::Json::Basic::l_Lean_Json_mkObj;
use crate::r#gen::Lean::Data::KVMap::l_Lean_KVMap_instValueBool;
use crate::r#gen::Lean::Data::Options::{l_Lean_Option_get___redArg, lean_register_option};
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::DocString::Links::{
    l_Lean_errorExplanationManualDomain, l_Lean_manualRoot,
};
use crate::r#gen::Lean::ErrorExplanation::{
    initialize_Lean_ErrorExplanation, runtime_initialize_Lean_ErrorExplanation,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_composePreservingKind, l_Lean_MessageData_errorName_x3f,
    l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_nil, l_Lean_MessageData_ofName,
    l_Lean_MessageData_stripNestedTags, l_Lean_MessageData_tagWithErrorName,
    l_Lean_instBEqMessageSeverity_beq, l_Lean_stringToMessageData,
};
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Prelude::lean_string_hash;
pub static l___private_Lean_Log_0__Lean_initFn___closed__0_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [119, 97, 114, 110, 105, 110, 103, 65, 115, 69, 114, 114, 111, 114, 0]};
static mut l___private_Lean_Log_0__Lean_initFn___closed__0_00___x40_Lean_Log_3265821404____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Log_0__Lean_initFn___closed__0_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Log_0__Lean_initFn___closed__1_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Log_0__Lean_initFn___closed__0_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,5238986158861308483 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Log_0__Lean_initFn___closed__1_00___x40_Lean_Log_3265821404____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Log_0__Lean_initFn___closed__1_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Log_0__Lean_initFn___closed__2_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [116, 114, 101, 97, 116, 32, 119, 97, 114, 110, 105, 110, 103, 115, 32, 97, 115, 32, 101, 114, 114, 111, 114, 115, 0]};
static mut l___private_Lean_Log_0__Lean_initFn___closed__2_00___x40_Lean_Log_3265821404____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Log_0__Lean_initFn___closed__2_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Log_0__Lean_initFn___closed__3_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Log_0__Lean_initFn___closed__2_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Log_0__Lean_initFn___closed__3_00___x40_Lean_Log_3265821404____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Log_0__Lean_initFn___closed__3_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Log_0__Lean_initFn___closed__4_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Log_0__Lean_initFn___closed__4_00___x40_Lean_Log_3265821404____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Log_0__Lean_initFn___closed__4_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Log_0__Lean_initFn___closed__5_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Log_0__Lean_initFn___closed__4_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Log_0__Lean_initFn___closed__5_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Log_0__Lean_initFn___closed__5_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Log_0__Lean_initFn___closed__0_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,9646326620821618514 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Log_0__Lean_initFn___closed__5_00___x40_Lean_Log_3265821404____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Log_0__Lean_initFn___closed__5_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l_Lean_errorDescriptionWidget___closed__0_value: crate::leanh::LeanStringObject<623> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 623,
        m_capacity: 623,
        m_length: 622,
        m_data: [
            10, 105, 109, 112, 111, 114, 116, 32, 123, 32, 99, 114, 101, 97, 116, 101, 69, 108,
            101, 109, 101, 110, 116, 32, 125, 32, 102, 114, 111, 109, 32, 39, 114, 101, 97, 99,
            116, 39, 59, 10, 10, 101, 120, 112, 111, 114, 116, 32, 100, 101, 102, 97, 117, 108,
            116, 32, 102, 117, 110, 99, 116, 105, 111, 110, 32, 40, 123, 32, 99, 111, 100, 101, 44,
            32, 101, 120, 112, 108, 97, 110, 97, 116, 105, 111, 110, 85, 114, 108, 32, 125, 41, 32,
            123, 10, 32, 32, 99, 111, 110, 115, 116, 32, 115, 97, 110, 115, 84, 101, 120, 116, 32,
            61, 32, 123, 32, 102, 111, 110, 116, 70, 97, 109, 105, 108, 121, 58, 32, 39, 118, 97,
            114, 40, 45, 45, 118, 115, 99, 111, 100, 101, 45, 102, 111, 110, 116, 45, 102, 97, 109,
            105, 108, 121, 41, 39, 32, 125, 10, 10, 32, 32, 99, 111, 110, 115, 116, 32, 99, 111,
            100, 101, 83, 112, 97, 110, 32, 61, 32, 99, 114, 101, 97, 116, 101, 69, 108, 101, 109,
            101, 110, 116, 40, 39, 115, 112, 97, 110, 39, 44, 32, 123, 125, 44, 32, 91, 10, 32, 32,
            32, 32, 99, 114, 101, 97, 116, 101, 69, 108, 101, 109, 101, 110, 116, 40, 39, 115, 112,
            97, 110, 39, 44, 32, 123, 32, 115, 116, 121, 108, 101, 58, 32, 115, 97, 110, 115, 84,
            101, 120, 116, 32, 125, 44, 32, 39, 69, 114, 114, 111, 114, 32, 99, 111, 100, 101, 58,
            32, 39, 41, 44, 32, 99, 111, 100, 101, 93, 41, 10, 32, 32, 99, 111, 110, 115, 116, 32,
            98, 114, 83, 112, 97, 110, 32, 61, 32, 99, 114, 101, 97, 116, 101, 69, 108, 101, 109,
            101, 110, 116, 40, 39, 115, 112, 97, 110, 39, 44, 32, 123, 125, 44, 32, 39, 92, 110,
            39, 41, 10, 32, 32, 99, 111, 110, 115, 116, 32, 108, 105, 110, 107, 83, 112, 97, 110,
            32, 61, 32, 99, 114, 101, 97, 116, 101, 69, 108, 101, 109, 101, 110, 116, 40, 39, 115,
            112, 97, 110, 39, 44, 32, 123, 32, 115, 116, 121, 108, 101, 58, 32, 115, 97, 110, 115,
            84, 101, 120, 116, 32, 125, 44, 10, 32, 32, 32, 32, 99, 114, 101, 97, 116, 101, 69,
            108, 101, 109, 101, 110, 116, 40, 39, 97, 39, 44, 32, 123, 32, 104, 114, 101, 102, 58,
            32, 101, 120, 112, 108, 97, 110, 97, 116, 105, 111, 110, 85, 114, 108, 44, 32, 116, 97,
            114, 103, 101, 116, 58, 32, 39, 95, 98, 108, 97, 110, 107, 39, 44, 32, 114, 101, 108,
            58, 32, 39, 110, 111, 114, 101, 102, 101, 114, 114, 101, 114, 32, 110, 111, 111, 112,
            101, 110, 101, 114, 39, 32, 125, 44, 10, 32, 32, 32, 32, 32, 32, 39, 86, 105, 101, 119,
            32, 101, 120, 112, 108, 97, 110, 97, 116, 105, 111, 110, 39, 41, 41, 10, 10, 32, 32,
            99, 111, 110, 115, 116, 32, 97, 108, 108, 32, 61, 32, 99, 114, 101, 97, 116, 101, 69,
            108, 101, 109, 101, 110, 116, 40, 39, 100, 105, 118, 39, 44, 32, 123, 32, 115, 116,
            121, 108, 101, 58, 32, 123, 32, 109, 97, 114, 103, 105, 110, 84, 111, 112, 58, 32, 39,
            49, 101, 109, 39, 32, 125, 32, 125, 44, 32, 91, 99, 111, 100, 101, 83, 112, 97, 110,
            44, 32, 98, 114, 83, 112, 97, 110, 44, 32, 108, 105, 110, 107, 83, 112, 97, 110, 93,
            41, 10, 32, 32, 114, 101, 116, 117, 114, 110, 32, 97, 108, 108, 10, 125, 0,
        ],
    };
static mut l_Lean_errorDescriptionWidget___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_errorDescriptionWidget___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_errorDescriptionWidget___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_errorDescriptionWidget___closed__1: u64 = 0;
static mut l_Lean_errorDescriptionWidget___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_errorDescriptionWidget___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_errorDescriptionWidget: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__0_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [102, 105, 110, 100, 47, 63, 100, 111, 109, 97, 105, 110, 61, 0]};
static mut l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__2_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [38, 110, 97, 109, 101, 61, 0]};
static mut l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__2_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__4_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [101, 114, 114, 111, 114, 68, 101, 115, 99, 114, 105, 112, 116, 105, 111, 110, 87, 105, 100, 103, 101, 116, 0]};
static mut l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__4_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Log_0__Lean_initFn___closed__4_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__4_value) as *mut crate::leanh::LeanObject,11821295174094476641 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__6_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [99, 111, 100, 101, 0]};
static mut l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__6_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__7_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [101, 120, 112, 108, 97, 110, 97, 116, 105, 111, 110, 85, 114, 108, 0]};
static mut l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__7_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___redArg___lam__0___closed__0_value: crate::leanh::LeanStringObject<1> =
    crate::leanh::LeanStringObject {
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
static mut l_Lean_logAt___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_logAt___redArg___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_logUnknownDecl___redArg___closed__0_value: crate::leanh::LeanStringObject<22> =
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
            117, 110, 107, 110, 111, 119, 110, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111,
            110, 32, 39, 0,
        ],
    };
static mut l_Lean_logUnknownDecl___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_logUnknownDecl___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_logUnknownDecl___redArg___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_logUnknownDecl___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_logUnknownDecl___redArg___closed__2_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [39, 0],
    };
static mut l_Lean_logUnknownDecl___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_logUnknownDecl___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_logUnknownDecl___redArg___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_logUnknownDecl___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_instMonadLogOfMonadLift___redArg___lam__0(
    mut v_logMessage_686_: *mut crate::leanh::LeanObject,
    mut v_inst_687_: *mut crate::leanh::LeanObject,
    mut v_msg_688_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_689_ = crate::leanh::lean_apply_1(v_logMessage_686_, v_msg_688_);
    v___x_690_ = crate::leanh::lean_apply_2(v_inst_687_, crate::leanh::lean_box(0), v___x_689_);
    return v___x_690_;
}
pub unsafe fn l_Lean_instMonadLogOfMonadLift___redArg(
    mut v_inst_691_: *mut crate::leanh::LeanObject,
    mut v_inst_692_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toMonadFileMap_693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRef_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getFileName_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasErrors_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_logMessage_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_700_: u8 = 0;
    let mut v___f_701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_709_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toMonadFileMap_693_ = crate::leanh::lean_ctor_get(v_inst_692_, 0);
                v_getRef_694_ = crate::leanh::lean_ctor_get(v_inst_692_, 1);
                v_getFileName_695_ = crate::leanh::lean_ctor_get(v_inst_692_, 2);
                v_hasErrors_696_ = crate::leanh::lean_ctor_get(v_inst_692_, 3);
                v_logMessage_697_ = crate::leanh::lean_ctor_get(v_inst_692_, 4);
                v_isSharedCheck_709_ = (!crate::leanh::lean_is_exclusive(v_inst_692_)) as u8;
                if v_isSharedCheck_709_ == 0 {
                    v___x_699_ = v_inst_692_;
                    v_isShared_700_ = v_isSharedCheck_709_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_logMessage_697_);
                    crate::leanh::lean_inc(v_hasErrors_696_);
                    crate::leanh::lean_inc(v_getFileName_695_);
                    crate::leanh::lean_inc(v_getRef_694_);
                    crate::leanh::lean_inc(v_toMonadFileMap_693_);
                    crate::leanh::lean_dec(v_inst_692_);
                    v___x_699_ = crate::leanh::lean_box(0);
                    v_isShared_700_ = v_isSharedCheck_709_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_n(v_inst_691_, 4);
                v___f_701_ = crate::leanh::lean_alloc_closure(
                    l_Lean_instMonadLogOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_701_, 0, v_logMessage_697_);
                crate::leanh::lean_closure_set(v___f_701_, 1, v_inst_691_);
                v___x_702_ = crate::leanh::lean_apply_2(
                    v_inst_691_,
                    crate::leanh::lean_box(0),
                    v_toMonadFileMap_693_,
                );
                v___x_703_ = crate::leanh::lean_apply_2(
                    v_inst_691_,
                    crate::leanh::lean_box(0),
                    v_getRef_694_,
                );
                v___x_704_ = crate::leanh::lean_apply_2(
                    v_inst_691_,
                    crate::leanh::lean_box(0),
                    v_getFileName_695_,
                );
                v___x_705_ = crate::leanh::lean_apply_2(
                    v_inst_691_,
                    crate::leanh::lean_box(0),
                    v_hasErrors_696_,
                );
                if v_isShared_700_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_699_, 4, v___f_701_);
                    crate::leanh::lean_ctor_set(v___x_699_, 3, v___x_705_);
                    crate::leanh::lean_ctor_set(v___x_699_, 2, v___x_704_);
                    crate::leanh::lean_ctor_set(v___x_699_, 1, v___x_703_);
                    crate::leanh::lean_ctor_set(v___x_699_, 0, v___x_702_);
                    v___x_707_ = v___x_699_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_708_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_708_, 0, v___x_702_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_708_, 1, v___x_703_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_708_, 2, v___x_704_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_708_, 3, v___x_705_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_708_, 4, v___f_701_);
                    v___x_707_ = v_reuseFailAlloc_708_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_707_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instMonadLogOfMonadLift(
    mut v_m_710_: *mut crate::leanh::LeanObject,
    mut v_n_711_: *mut crate::leanh::LeanObject,
    mut v_inst_712_: *mut crate::leanh::LeanObject,
    mut v_inst_713_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_714_ = l_Lean_instMonadLogOfMonadLift___redArg(v_inst_712_, v_inst_713_);
    return v___x_714_;
}
pub unsafe fn l_Lean_getRefPos___redArg___lam__0(
    mut v_toPure_715_: *mut crate::leanh::LeanObject,
    mut v_ref_716_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_717_: u8 = 0;
    let mut v___x_718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_717_ = 0;
    v___x_718_ = l_Lean_Syntax_getPos_x3f(v_ref_716_, v___x_717_);
    if crate::leanh::lean_obj_tag(v___x_718_) == 0 {
        let mut v___x_719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_719_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_720_ =
            crate::leanh::lean_apply_2(v_toPure_715_, crate::leanh::lean_box(0), v___x_719_);
        return v___x_720_;
    } else {
        let mut v_val_721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_721_ = crate::leanh::lean_ctor_get(v___x_718_, 0);
        crate::leanh::lean_inc(v_val_721_);
        crate::leanh::lean_dec_ref_known(v___x_718_, 1);
        v___x_722_ =
            crate::leanh::lean_apply_2(v_toPure_715_, crate::leanh::lean_box(0), v_val_721_);
        return v___x_722_;
    }
}
pub unsafe fn l_Lean_getRefPos___redArg___lam__0___boxed(
    mut v_toPure_723_: *mut crate::leanh::LeanObject,
    mut v_ref_724_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_725_ = l_Lean_getRefPos___redArg___lam__0(v_toPure_723_, v_ref_724_);
    crate::leanh::lean_dec(v_ref_724_);
    return v_res_725_;
}
pub unsafe fn l_Lean_getRefPos___redArg(
    mut v_inst_726_: *mut crate::leanh::LeanObject,
    mut v_inst_727_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRef_730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_728_ = crate::leanh::lean_ctor_get(v_inst_726_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_728_);
    v_toBind_729_ = crate::leanh::lean_ctor_get(v_inst_726_, 1);
    crate::leanh::lean_inc(v_toBind_729_);
    crate::leanh::lean_dec_ref(v_inst_726_);
    v_getRef_730_ = crate::leanh::lean_ctor_get(v_inst_727_, 1);
    crate::leanh::lean_inc(v_getRef_730_);
    crate::leanh::lean_dec_ref(v_inst_727_);
    v_toPure_731_ = crate::leanh::lean_ctor_get(v_toApplicative_728_, 1);
    crate::leanh::lean_inc(v_toPure_731_);
    crate::leanh::lean_dec_ref(v_toApplicative_728_);
    v___f_732_ = crate::leanh::lean_alloc_closure(
        l_Lean_getRefPos___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_732_, 0, v_toPure_731_);
    v___x_733_ = crate::leanh::lean_apply_4(
        v_toBind_729_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getRef_730_,
        v___f_732_,
    );
    return v___x_733_;
}
pub unsafe fn l_Lean_getRefPos(
    mut v_m_734_: *mut crate::leanh::LeanObject,
    mut v_inst_735_: *mut crate::leanh::LeanObject,
    mut v_inst_736_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_737_ = l_Lean_getRefPos___redArg(v_inst_735_, v_inst_736_);
    return v___x_737_;
}
pub unsafe fn l_Lean_getRefPosition___redArg___lam__0(
    mut v_fileMap_738_: *mut crate::leanh::LeanObject,
    mut v_toPure_739_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_740_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_741_ = l_Lean_FileMap_toPosition(v_fileMap_738_, v_____do__lift_740_);
    v___x_742_ = crate::leanh::lean_apply_2(v_toPure_739_, crate::leanh::lean_box(0), v___x_741_);
    return v___x_742_;
}
pub unsafe fn l_Lean_getRefPosition___redArg___lam__0___boxed(
    mut v_fileMap_743_: *mut crate::leanh::LeanObject,
    mut v_toPure_744_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_745_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_746_ =
        l_Lean_getRefPosition___redArg___lam__0(v_fileMap_743_, v_toPure_744_, v_____do__lift_745_);
    crate::leanh::lean_dec(v_____do__lift_745_);
    return v_res_746_;
}
pub unsafe fn l_Lean_getRefPosition___redArg___lam__1(
    mut v_toPure_747_: *mut crate::leanh::LeanObject,
    mut v_inst_748_: *mut crate::leanh::LeanObject,
    mut v_inst_749_: *mut crate::leanh::LeanObject,
    mut v_toBind_750_: *mut crate::leanh::LeanObject,
    mut v_fileMap_751_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_752_ = crate::leanh::lean_alloc_closure(
        l_Lean_getRefPosition___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_752_, 0, v_fileMap_751_);
    crate::leanh::lean_closure_set(v___f_752_, 1, v_toPure_747_);
    v___x_753_ = l_Lean_getRefPos___redArg(v_inst_748_, v_inst_749_);
    v___x_754_ = crate::leanh::lean_apply_4(
        v_toBind_750_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_753_,
        v___f_752_,
    );
    return v___x_754_;
}
pub unsafe fn l_Lean_getRefPosition___redArg(
    mut v_inst_755_: *mut crate::leanh::LeanObject,
    mut v_inst_756_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toMonadFileMap_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_757_ = crate::leanh::lean_ctor_get(v_inst_755_, 0);
    v_toBind_758_ = crate::leanh::lean_ctor_get(v_inst_755_, 1);
    crate::leanh::lean_inc_n(v_toBind_758_, 2);
    v_toMonadFileMap_759_ = crate::leanh::lean_ctor_get(v_inst_756_, 0);
    crate::leanh::lean_inc(v_toMonadFileMap_759_);
    v_toPure_760_ = crate::leanh::lean_ctor_get(v_toApplicative_757_, 1);
    crate::leanh::lean_inc(v_toPure_760_);
    v___f_761_ = crate::leanh::lean_alloc_closure(
        l_Lean_getRefPosition___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_761_, 0, v_toPure_760_);
    crate::leanh::lean_closure_set(v___f_761_, 1, v_inst_755_);
    crate::leanh::lean_closure_set(v___f_761_, 2, v_inst_756_);
    crate::leanh::lean_closure_set(v___f_761_, 3, v_toBind_758_);
    v___x_762_ = crate::leanh::lean_apply_4(
        v_toBind_758_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_toMonadFileMap_759_,
        v___f_761_,
    );
    return v___x_762_;
}
pub unsafe fn l_Lean_getRefPosition(
    mut v_m_763_: *mut crate::leanh::LeanObject,
    mut v_inst_764_: *mut crate::leanh::LeanObject,
    mut v_inst_765_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_766_ = l_Lean_getRefPosition___redArg(v_inst_764_, v_inst_765_);
    return v___x_766_;
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Log_0__Lean_initFn_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__spec__0(
    mut v_name_767_: *mut crate::leanh::LeanObject,
    mut v_decl_768_: *mut crate::leanh::LeanObject,
    mut v_ref_769_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_defValue_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_775_: u8 = 0;
    let mut v___x_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_780_: u8 = 0;
    let mut v___x_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_785_: u8 = 0;
    let mut v_unused_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_790_: u8 = 0;
    let mut v___x_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_794_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_771_ = crate::leanh::lean_ctor_get(v_decl_768_, 0);
                v_descr_772_ = crate::leanh::lean_ctor_get(v_decl_768_, 1);
                v_deprecation_x3f_773_ = crate::leanh::lean_ctor_get(v_decl_768_, 2);
                v___x_774_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
                v___x_775_ = (crate::leanh::lean_unbox(v_defValue_771_) as u8);
                crate::leanh::lean_ctor_set_uint8(v___x_774_, 0 as u32, v___x_775_);
                crate::leanh::lean_inc(v_deprecation_x3f_773_);
                crate::leanh::lean_inc_ref(v_descr_772_);
                crate::leanh::lean_inc_n(v_name_767_, 2);
                v___x_776_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_776_, 0, v_name_767_);
                crate::leanh::lean_ctor_set(v___x_776_, 1, v_ref_769_);
                crate::leanh::lean_ctor_set(v___x_776_, 2, v___x_774_);
                crate::leanh::lean_ctor_set(v___x_776_, 3, v_descr_772_);
                crate::leanh::lean_ctor_set(v___x_776_, 4, v_deprecation_x3f_773_);
                v___x_777_ = lean_register_option(v_name_767_, v___x_776_);
                if crate::leanh::lean_obj_tag(v___x_777_) == 0 {
                    v_isSharedCheck_785_ = (!crate::leanh::lean_is_exclusive(v___x_777_)) as u8;
                    if v_isSharedCheck_785_ == 0 {
                        v_unused_786_ = crate::leanh::lean_ctor_get(v___x_777_, 0);
                        crate::leanh::lean_dec(v_unused_786_);
                        v___x_779_ = v___x_777_;
                        v_isShared_780_ = v_isSharedCheck_785_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_777_);
                        v___x_779_ = crate::leanh::lean_box(0);
                        v_isShared_780_ = v_isSharedCheck_785_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_name_767_);
                    v_a_787_ = crate::leanh::lean_ctor_get(v___x_777_, 0);
                    v_isSharedCheck_794_ = (!crate::leanh::lean_is_exclusive(v___x_777_)) as u8;
                    if v_isSharedCheck_794_ == 0 {
                        v___x_789_ = v___x_777_;
                        v_isShared_790_ = v_isSharedCheck_794_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_787_);
                        crate::leanh::lean_dec(v___x_777_);
                        v___x_789_ = crate::leanh::lean_box(0);
                        v_isShared_790_ = v_isSharedCheck_794_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_defValue_771_);
                v___x_781_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_781_, 0, v_name_767_);
                crate::leanh::lean_ctor_set(v___x_781_, 1, v_defValue_771_);
                if v_isShared_780_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_779_, 0, v___x_781_);
                    v___x_783_ = v___x_779_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_784_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_784_, 0, v___x_781_);
                    v___x_783_ = v_reuseFailAlloc_784_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_783_;
            }
            3 => {
                if v_isShared_790_ == 0 {
                    v___x_792_ = v___x_789_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_793_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_793_, 0, v_a_787_);
                    v___x_792_ = v_reuseFailAlloc_793_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_792_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Log_0__Lean_initFn_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_795_: *mut crate::leanh::LeanObject,
    mut v_decl_796_: *mut crate::leanh::LeanObject,
    mut v_ref_797_: *mut crate::leanh::LeanObject,
    mut v_a_798_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_799_ = l_Lean_Option_register___at___00__private_Lean_Log_0__Lean_initFn_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__spec__0(v_name_795_, v_decl_796_, v_ref_797_);
    crate::leanh::lean_dec_ref(v_decl_796_);
    return v_res_799_;
}
pub unsafe fn l___private_Lean_Log_0__Lean_initFn_00___x40_Lean_Log_3265821404____hygCtx___hyg_4_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_814_ = l___private_Lean_Log_0__Lean_initFn___closed__1_00___x40_Lean_Log_3265821404____hygCtx___hyg_4_;
    v___x_815_ = l___private_Lean_Log_0__Lean_initFn___closed__3_00___x40_Lean_Log_3265821404____hygCtx___hyg_4_;
    v___x_816_ = l___private_Lean_Log_0__Lean_initFn___closed__5_00___x40_Lean_Log_3265821404____hygCtx___hyg_4_;
    v___x_817_ = l_Lean_Option_register___at___00__private_Lean_Log_0__Lean_initFn_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__spec__0(v___x_814_, v___x_815_, v___x_816_);
    return v___x_817_;
}
pub unsafe fn l___private_Lean_Log_0__Lean_initFn_00___x40_Lean_Log_3265821404____hygCtx___hyg_4____boxed(
    mut v_a_818_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_819_ =
        l___private_Lean_Log_0__Lean_initFn_00___x40_Lean_Log_3265821404____hygCtx___hyg_4_();
    return v_res_819_;
}
pub unsafe fn _init_l_Lean_errorDescriptionWidget___closed__1() -> u64 {
    let mut v___x_821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_822_: u64 = 0;
    v___x_821_ = l_Lean_errorDescriptionWidget___closed__0;
    v___x_822_ = lean_string_hash(v___x_821_);
    return v___x_822_;
}
pub unsafe fn _init_l_Lean_errorDescriptionWidget___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_823_: u64 = 0;
    let mut v___x_824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_823_ = crate::leanh::lean_uint64_once(
        core::ptr::addr_of_mut!(l_Lean_errorDescriptionWidget___closed__1),
        core::ptr::addr_of_mut!(l_Lean_errorDescriptionWidget___closed__1_once),
        _init_l_Lean_errorDescriptionWidget___closed__1,
    );
    v___x_824_ = l_Lean_errorDescriptionWidget___closed__0;
    v___x_825_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
    crate::leanh::lean_ctor_set(v___x_825_, 0, v___x_824_);
    crate::leanh::lean_ctor_set_uint64(
        v___x_825_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_823_,
    );
    return v___x_825_;
}
pub unsafe fn _init_l_Lean_errorDescriptionWidget() -> *mut crate::leanh::LeanObject {
    let mut v___x_826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_826_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_errorDescriptionWidget___closed__2),
        core::ptr::addr_of_mut!(l_Lean_errorDescriptionWidget___closed__2_once),
        _init_l_Lean_errorDescriptionWidget___closed__2,
    );
    return v___x_826_;
}
pub unsafe fn l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___lam__0(
    mut v___x_827_: *mut crate::leanh::LeanObject,
    mut v___y_828_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_829_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_829_, 0, v___x_827_);
    crate::leanh::lean_ctor_set(v___x_829_, 1, v___y_828_);
    return v___x_829_;
}
pub unsafe fn _init_l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_831_ = l_Lean_errorExplanationManualDomain;
    v___x_832_ =
        l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__0;
    v___x_833_ = lean_string_append(v___x_832_, v___x_831_);
    return v___x_833_;
}
pub unsafe fn _init_l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_835_ =
        l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__2;
    v___x_836_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__1_once), _init_l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__1);
    v___x_837_ = lean_string_append(v___x_836_, v___x_835_);
    return v___x_837_;
}
pub unsafe fn l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
    mut v_msg_844_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_850_: u8 = 0;
    let mut v___x_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_javascriptHash_852_: u64 = 0;
    let mut v___x_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_855_: u8 = 0;
    let mut v___x_856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_url_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inst_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_877_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_msg_844_);
                v___x_845_ = l_Lean_MessageData_stripNestedTags(v_msg_844_);
                v___x_846_ = l_Lean_MessageData_errorName_x3f(v___x_845_);
                crate::leanh::lean_dec_ref(v___x_845_);
                if crate::leanh::lean_obj_tag(v___x_846_) == 0 {
                    return v_msg_844_;
                } else {
                    v_val_847_ = crate::leanh::lean_ctor_get(v___x_846_, 0);
                    v_isSharedCheck_877_ = (!crate::leanh::lean_is_exclusive(v___x_846_)) as u8;
                    if v_isSharedCheck_877_ == 0 {
                        v___x_849_ = v___x_846_;
                        v_isShared_850_ = v_isSharedCheck_877_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_847_);
                        crate::leanh::lean_dec(v___x_846_);
                        v___x_849_ = crate::leanh::lean_box(0);
                        v_isShared_850_ = v_isSharedCheck_877_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_851_ = l_Lean_errorDescriptionWidget;
                v_javascriptHash_852_ = crate::leanh::lean_ctor_get_uint64(
                    v___x_851_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v___x_853_ = l_Lean_manualRoot;
                v___x_854_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__3_once), _init_l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__3);
                v___x_855_ = 1;
                v___x_856_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_val_847_, v___x_855_,
                );
                v___x_857_ = lean_string_append(v___x_854_, v___x_856_);
                v_url_858_ = lean_string_append(v___x_853_, v___x_857_);
                crate::leanh::lean_dec_ref(v___x_857_);
                v___x_859_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__5;
                v___x_860_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__6;
                if v_isShared_850_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_849_, 3);
                    crate::leanh::lean_ctor_set(v___x_849_, 0, v___x_856_);
                    v___x_862_ = v___x_849_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_876_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_876_, 0, v___x_856_);
                    v___x_862_ = v_reuseFailAlloc_876_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_863_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_863_, 0, v___x_860_);
                crate::leanh::lean_ctor_set(v___x_863_, 1, v___x_862_);
                v___x_864_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__7;
                v___x_865_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_865_, 0, v_url_858_);
                v___x_866_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_866_, 0, v___x_864_);
                crate::leanh::lean_ctor_set(v___x_866_, 1, v___x_865_);
                v___x_867_ = crate::leanh::lean_box(0);
                v___x_868_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_868_, 0, v___x_866_);
                crate::leanh::lean_ctor_set(v___x_868_, 1, v___x_867_);
                v___x_869_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_869_, 0, v___x_863_);
                crate::leanh::lean_ctor_set(v___x_869_, 1, v___x_868_);
                v___x_870_ = l_Lean_Json_mkObj(v___x_869_);
                crate::leanh::lean_dec_ref_known(v___x_869_, 2);
                v___f_871_ = crate::leanh::lean_alloc_closure(
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___lam__0
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_871_, 0, v___x_870_);
                v_inst_872_ = crate::leanh::lean_alloc_ctor(0, 2, (8) as u32);
                crate::leanh::lean_ctor_set(v_inst_872_, 0, v___x_859_);
                crate::leanh::lean_ctor_set(v_inst_872_, 1, v___f_871_);
                crate::leanh::lean_ctor_set_uint64(
                    v_inst_872_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v_javascriptHash_852_,
                );
                v___x_873_ = l_Lean_MessageData_nil;
                v___x_874_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_874_, 0, v_inst_872_);
                crate::leanh::lean_ctor_set(v___x_874_, 1, v___x_873_);
                v___x_875_ = l_Lean_MessageData_composePreservingKind(v_msg_844_, v___x_874_);
                return v___x_875_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___redArg___lam__0(
    mut v_fileMap_879_: *mut crate::leanh::LeanObject,
    mut v___y_880_: *mut crate::leanh::LeanObject,
    mut v___y_881_: *mut crate::leanh::LeanObject,
    mut v___y_882_: u8,
    mut v___y_883_: u8,
    mut v_isSilent_884_: u8,
    mut v_msgData_885_: *mut crate::leanh::LeanObject,
    mut v_logMessage_886_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_887_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_fileMap_879_);
    v___x_888_ = l_Lean_FileMap_toPosition(v_fileMap_879_, v___y_880_);
    v___x_889_ = l_Lean_FileMap_toPosition(v_fileMap_879_, v___y_881_);
    v___x_890_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_890_, 0, v___x_889_);
    v___x_891_ = l_Lean_logAt___redArg___lam__0___closed__0;
    v___x_892_ = crate::leanh::lean_alloc_ctor(0, 5, (3) as u32);
    crate::leanh::lean_ctor_set(v___x_892_, 0, v_____do__lift_887_);
    crate::leanh::lean_ctor_set(v___x_892_, 1, v___x_888_);
    crate::leanh::lean_ctor_set(v___x_892_, 2, v___x_890_);
    crate::leanh::lean_ctor_set(v___x_892_, 3, v___x_891_);
    crate::leanh::lean_ctor_set(v___x_892_, 4, v_msgData_885_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_892_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
        v___y_882_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_892_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
        v___y_883_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_892_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 2) as u32,
        v_isSilent_884_,
    );
    v___x_893_ = crate::leanh::lean_apply_1(v_logMessage_886_, v___x_892_);
    return v___x_893_;
}
pub unsafe fn l_Lean_logAt___redArg___lam__0___boxed(
    mut v_fileMap_894_: *mut crate::leanh::LeanObject,
    mut v___y_895_: *mut crate::leanh::LeanObject,
    mut v___y_896_: *mut crate::leanh::LeanObject,
    mut v___y_897_: *mut crate::leanh::LeanObject,
    mut v___y_898_: *mut crate::leanh::LeanObject,
    mut v_isSilent_899_: *mut crate::leanh::LeanObject,
    mut v_msgData_900_: *mut crate::leanh::LeanObject,
    mut v_logMessage_901_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_902_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_375__boxed_903_: u8 = 0;
    let mut v___y_376__boxed_904_: u8 = 0;
    let mut v_isSilent_boxed_905_: u8 = 0;
    let mut v_res_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_375__boxed_903_ = (crate::leanh::lean_unbox(v___y_897_) as u8);
    v___y_376__boxed_904_ = (crate::leanh::lean_unbox(v___y_898_) as u8);
    v_isSilent_boxed_905_ = (crate::leanh::lean_unbox(v_isSilent_899_) as u8);
    v_res_906_ = l_Lean_logAt___redArg___lam__0(
        v_fileMap_894_,
        v___y_895_,
        v___y_896_,
        v___y_375__boxed_903_,
        v___y_376__boxed_904_,
        v_isSilent_boxed_905_,
        v_msgData_900_,
        v_logMessage_901_,
        v_____do__lift_902_,
    );
    crate::leanh::lean_dec(v___y_896_);
    crate::leanh::lean_dec(v___y_895_);
    return v_res_906_;
}
pub unsafe fn l_Lean_logAt___redArg___lam__1(
    mut v_fileMap_907_: *mut crate::leanh::LeanObject,
    mut v___y_908_: *mut crate::leanh::LeanObject,
    mut v___y_909_: *mut crate::leanh::LeanObject,
    mut v___y_910_: u8,
    mut v___y_911_: u8,
    mut v_isSilent_912_: u8,
    mut v_logMessage_913_: *mut crate::leanh::LeanObject,
    mut v_toBind_914_: *mut crate::leanh::LeanObject,
    mut v_getFileName_915_: *mut crate::leanh::LeanObject,
    mut v_msgData_916_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_917_ = crate::leanh::lean_box((v___y_910_) as usize);
    v___x_918_ = crate::leanh::lean_box((v___y_911_) as usize);
    v___x_919_ = crate::leanh::lean_box((v_isSilent_912_) as usize);
    v___f_920_ = crate::leanh::lean_alloc_closure(
        l_Lean_logAt___redArg___lam__0___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    crate::leanh::lean_closure_set(v___f_920_, 0, v_fileMap_907_);
    crate::leanh::lean_closure_set(v___f_920_, 1, v___y_908_);
    crate::leanh::lean_closure_set(v___f_920_, 2, v___y_909_);
    crate::leanh::lean_closure_set(v___f_920_, 3, v___x_917_);
    crate::leanh::lean_closure_set(v___f_920_, 4, v___x_918_);
    crate::leanh::lean_closure_set(v___f_920_, 5, v___x_919_);
    crate::leanh::lean_closure_set(v___f_920_, 6, v_msgData_916_);
    crate::leanh::lean_closure_set(v___f_920_, 7, v_logMessage_913_);
    v___x_921_ = crate::leanh::lean_apply_4(
        v_toBind_914_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getFileName_915_,
        v___f_920_,
    );
    return v___x_921_;
}
pub unsafe fn l_Lean_logAt___redArg___lam__1___boxed(
    mut v_fileMap_922_: *mut crate::leanh::LeanObject,
    mut v___y_923_: *mut crate::leanh::LeanObject,
    mut v___y_924_: *mut crate::leanh::LeanObject,
    mut v___y_925_: *mut crate::leanh::LeanObject,
    mut v___y_926_: *mut crate::leanh::LeanObject,
    mut v_isSilent_927_: *mut crate::leanh::LeanObject,
    mut v_logMessage_928_: *mut crate::leanh::LeanObject,
    mut v_toBind_929_: *mut crate::leanh::LeanObject,
    mut v_getFileName_930_: *mut crate::leanh::LeanObject,
    mut v_msgData_931_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_403__boxed_932_: u8 = 0;
    let mut v___y_404__boxed_933_: u8 = 0;
    let mut v_isSilent_boxed_934_: u8 = 0;
    let mut v_res_935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_403__boxed_932_ = (crate::leanh::lean_unbox(v___y_925_) as u8);
    v___y_404__boxed_933_ = (crate::leanh::lean_unbox(v___y_926_) as u8);
    v_isSilent_boxed_934_ = (crate::leanh::lean_unbox(v_isSilent_927_) as u8);
    v_res_935_ = l_Lean_logAt___redArg___lam__1(
        v_fileMap_922_,
        v___y_923_,
        v___y_924_,
        v___y_403__boxed_932_,
        v___y_404__boxed_933_,
        v_isSilent_boxed_934_,
        v_logMessage_928_,
        v_toBind_929_,
        v_getFileName_930_,
        v_msgData_931_,
    );
    return v_res_935_;
}
pub unsafe fn l_Lean_logAt___redArg___lam__2(
    mut v___y_936_: *mut crate::leanh::LeanObject,
    mut v___y_937_: *mut crate::leanh::LeanObject,
    mut v___y_938_: u8,
    mut v___y_939_: u8,
    mut v_isSilent_940_: u8,
    mut v_logMessage_941_: *mut crate::leanh::LeanObject,
    mut v_toBind_942_: *mut crate::leanh::LeanObject,
    mut v_getFileName_943_: *mut crate::leanh::LeanObject,
    mut v_msgData_944_: *mut crate::leanh::LeanObject,
    mut v_inst_945_: *mut crate::leanh::LeanObject,
    mut v_fileMap_946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_947_ = crate::leanh::lean_box((v___y_938_) as usize);
    v___x_948_ = crate::leanh::lean_box((v___y_939_) as usize);
    v___x_949_ = crate::leanh::lean_box((v_isSilent_940_) as usize);
    crate::leanh::lean_inc(v_toBind_942_);
    v___f_950_ = crate::leanh::lean_alloc_closure(
        l_Lean_logAt___redArg___lam__1___boxed as *mut core::ffi::c_void,
        10,
        9,
    );
    crate::leanh::lean_closure_set(v___f_950_, 0, v_fileMap_946_);
    crate::leanh::lean_closure_set(v___f_950_, 1, v___y_936_);
    crate::leanh::lean_closure_set(v___f_950_, 2, v___y_937_);
    crate::leanh::lean_closure_set(v___f_950_, 3, v___x_947_);
    crate::leanh::lean_closure_set(v___f_950_, 4, v___x_948_);
    crate::leanh::lean_closure_set(v___f_950_, 5, v___x_949_);
    crate::leanh::lean_closure_set(v___f_950_, 6, v_logMessage_941_);
    crate::leanh::lean_closure_set(v___f_950_, 7, v_toBind_942_);
    crate::leanh::lean_closure_set(v___f_950_, 8, v_getFileName_943_);
    v___x_951_ =
        l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_944_);
    v___x_952_ = crate::leanh::lean_apply_1(v_inst_945_, v___x_951_);
    v___x_953_ = crate::leanh::lean_apply_4(
        v_toBind_942_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_952_,
        v___f_950_,
    );
    return v___x_953_;
}
pub unsafe fn l_Lean_logAt___redArg___lam__2___boxed(
    mut v___y_954_: *mut crate::leanh::LeanObject,
    mut v___y_955_: *mut crate::leanh::LeanObject,
    mut v___y_956_: *mut crate::leanh::LeanObject,
    mut v___y_957_: *mut crate::leanh::LeanObject,
    mut v_isSilent_958_: *mut crate::leanh::LeanObject,
    mut v_logMessage_959_: *mut crate::leanh::LeanObject,
    mut v_toBind_960_: *mut crate::leanh::LeanObject,
    mut v_getFileName_961_: *mut crate::leanh::LeanObject,
    mut v_msgData_962_: *mut crate::leanh::LeanObject,
    mut v_inst_963_: *mut crate::leanh::LeanObject,
    mut v_fileMap_964_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_425__boxed_965_: u8 = 0;
    let mut v___y_426__boxed_966_: u8 = 0;
    let mut v_isSilent_boxed_967_: u8 = 0;
    let mut v_res_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_425__boxed_965_ = (crate::leanh::lean_unbox(v___y_956_) as u8);
    v___y_426__boxed_966_ = (crate::leanh::lean_unbox(v___y_957_) as u8);
    v_isSilent_boxed_967_ = (crate::leanh::lean_unbox(v_isSilent_958_) as u8);
    v_res_968_ = l_Lean_logAt___redArg___lam__2(
        v___y_954_,
        v___y_955_,
        v___y_425__boxed_965_,
        v___y_426__boxed_966_,
        v_isSilent_boxed_967_,
        v_logMessage_959_,
        v_toBind_960_,
        v_getFileName_961_,
        v_msgData_962_,
        v_inst_963_,
        v_fileMap_964_,
    );
    return v_res_968_;
}
pub unsafe fn l_Lean_logAt___redArg___lam__3(
    mut v_ref_969_: *mut crate::leanh::LeanObject,
    mut v___y_970_: u8,
    mut v___y_971_: u8,
    mut v_isSilent_972_: u8,
    mut v_logMessage_973_: *mut crate::leanh::LeanObject,
    mut v_toBind_974_: *mut crate::leanh::LeanObject,
    mut v_getFileName_975_: *mut crate::leanh::LeanObject,
    mut v_msgData_976_: *mut crate::leanh::LeanObject,
    mut v_inst_977_: *mut crate::leanh::LeanObject,
    mut v_toMonadFileMap_978_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_979_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_988_ = l_Lean_replaceRef(v_ref_969_, v_____do__lift_979_);
                v___x_993_ = l_Lean_Syntax_getPos_x3f(v_ref_988_, v___y_970_);
                if crate::leanh::lean_obj_tag(v___x_993_) == 0 {
                    v___x_994_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_990_ = v___x_994_;
                    state = 2;
                    continue;
                } else {
                    v_val_995_ = crate::leanh::lean_ctor_get(v___x_993_, 0);
                    crate::leanh::lean_inc(v_val_995_);
                    crate::leanh::lean_dec_ref_known(v___x_993_, 1);
                    v___y_990_ = v_val_995_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_983_ = crate::leanh::lean_box((v___y_970_) as usize);
                v___x_984_ = crate::leanh::lean_box((v___y_971_) as usize);
                v___x_985_ = crate::leanh::lean_box((v_isSilent_972_) as usize);
                crate::leanh::lean_inc(v_toBind_974_);
                v___f_986_ = crate::leanh::lean_alloc_closure(
                    l_Lean_logAt___redArg___lam__2___boxed as *mut core::ffi::c_void,
                    11,
                    10,
                );
                crate::leanh::lean_closure_set(v___f_986_, 0, v___y_981_);
                crate::leanh::lean_closure_set(v___f_986_, 1, v___y_982_);
                crate::leanh::lean_closure_set(v___f_986_, 2, v___x_983_);
                crate::leanh::lean_closure_set(v___f_986_, 3, v___x_984_);
                crate::leanh::lean_closure_set(v___f_986_, 4, v___x_985_);
                crate::leanh::lean_closure_set(v___f_986_, 5, v_logMessage_973_);
                crate::leanh::lean_closure_set(v___f_986_, 6, v_toBind_974_);
                crate::leanh::lean_closure_set(v___f_986_, 7, v_getFileName_975_);
                crate::leanh::lean_closure_set(v___f_986_, 8, v_msgData_976_);
                crate::leanh::lean_closure_set(v___f_986_, 9, v_inst_977_);
                v___x_987_ = crate::leanh::lean_apply_4(
                    v_toBind_974_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v_toMonadFileMap_978_,
                    v___f_986_,
                );
                return v___x_987_;
            }
            2 => {
                v___x_991_ = l_Lean_Syntax_getTailPos_x3f(v_ref_988_, v___y_970_);
                crate::leanh::lean_dec(v_ref_988_);
                if crate::leanh::lean_obj_tag(v___x_991_) == 0 {
                    crate::leanh::lean_inc(v___y_990_);
                    v___y_981_ = v___y_990_;
                    v___y_982_ = v___y_990_;
                    state = 1;
                    continue;
                } else {
                    v_val_992_ = crate::leanh::lean_ctor_get(v___x_991_, 0);
                    crate::leanh::lean_inc(v_val_992_);
                    crate::leanh::lean_dec_ref_known(v___x_991_, 1);
                    v___y_981_ = v___y_990_;
                    v___y_982_ = v_val_992_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___redArg___lam__3___boxed(
    mut v_ref_996_: *mut crate::leanh::LeanObject,
    mut v___y_997_: *mut crate::leanh::LeanObject,
    mut v___y_998_: *mut crate::leanh::LeanObject,
    mut v_isSilent_999_: *mut crate::leanh::LeanObject,
    mut v_logMessage_1000_: *mut crate::leanh::LeanObject,
    mut v_toBind_1001_: *mut crate::leanh::LeanObject,
    mut v_getFileName_1002_: *mut crate::leanh::LeanObject,
    mut v_msgData_1003_: *mut crate::leanh::LeanObject,
    mut v_inst_1004_: *mut crate::leanh::LeanObject,
    mut v_toMonadFileMap_1005_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1006_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_453__boxed_1007_: u8 = 0;
    let mut v___y_454__boxed_1008_: u8 = 0;
    let mut v_isSilent_boxed_1009_: u8 = 0;
    let mut v_res_1010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_453__boxed_1007_ = (crate::leanh::lean_unbox(v___y_997_) as u8);
    v___y_454__boxed_1008_ = (crate::leanh::lean_unbox(v___y_998_) as u8);
    v_isSilent_boxed_1009_ = (crate::leanh::lean_unbox(v_isSilent_999_) as u8);
    v_res_1010_ = l_Lean_logAt___redArg___lam__3(
        v_ref_996_,
        v___y_453__boxed_1007_,
        v___y_454__boxed_1008_,
        v_isSilent_boxed_1009_,
        v_logMessage_1000_,
        v_toBind_1001_,
        v_getFileName_1002_,
        v_msgData_1003_,
        v_inst_1004_,
        v_toMonadFileMap_1005_,
        v_____do__lift_1006_,
    );
    crate::leanh::lean_dec(v_____do__lift_1006_);
    crate::leanh::lean_dec(v_ref_996_);
    return v_res_1010_;
}
pub unsafe fn l_Lean_logAt___redArg___lam__4(
    mut v_inst_1011_: *mut crate::leanh::LeanObject,
    mut v_ref_1012_: *mut crate::leanh::LeanObject,
    mut v___y_1013_: u8,
    mut v_isSilent_1014_: u8,
    mut v_toBind_1015_: *mut crate::leanh::LeanObject,
    mut v_msgData_1016_: *mut crate::leanh::LeanObject,
    mut v_inst_1017_: *mut crate::leanh::LeanObject,
    mut v_severity_1018_: u8,
    mut v___x_1019_: u8,
    mut v_____do__lift_1020_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1022_: u8 = 0;
    let mut v_toMonadFileMap_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRef_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getFileName_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_logMessage_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1033_: u8 = 0;
    let mut v___x_1034_: u8 = 0;
    let mut v___x_1035_: u8 = 0;
    let mut v___x_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1034_ = 1;
                v___x_1035_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1018_, v___x_1034_);
                if v___x_1035_ == 0 {
                    v___y_1033_ = v___x_1035_;
                    state = 2;
                    continue;
                } else {
                    v___x_1036_ = l_Lean_KVMap_instValueBool;
                    v___x_1037_ = l_Lean_warningAsError;
                    v___x_1038_ =
                        l_Lean_Option_get___redArg(v___x_1036_, v_____do__lift_1020_, v___x_1037_);
                    v___x_1039_ = (crate::leanh::lean_unbox(v___x_1038_) as u8);
                    crate::leanh::lean_dec(v___x_1038_);
                    v___y_1033_ = v___x_1039_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v_toMonadFileMap_1023_ = crate::leanh::lean_ctor_get(v_inst_1011_, 0);
                crate::leanh::lean_inc(v_toMonadFileMap_1023_);
                v_getRef_1024_ = crate::leanh::lean_ctor_get(v_inst_1011_, 1);
                crate::leanh::lean_inc(v_getRef_1024_);
                v_getFileName_1025_ = crate::leanh::lean_ctor_get(v_inst_1011_, 2);
                crate::leanh::lean_inc(v_getFileName_1025_);
                v_logMessage_1026_ = crate::leanh::lean_ctor_get(v_inst_1011_, 4);
                crate::leanh::lean_inc(v_logMessage_1026_);
                crate::leanh::lean_dec_ref(v_inst_1011_);
                v___x_1027_ = crate::leanh::lean_box((v___y_1013_) as usize);
                v___x_1028_ = crate::leanh::lean_box((v___y_1022_) as usize);
                v___x_1029_ = crate::leanh::lean_box((v_isSilent_1014_) as usize);
                crate::leanh::lean_inc(v_toBind_1015_);
                v___f_1030_ = crate::leanh::lean_alloc_closure(
                    l_Lean_logAt___redArg___lam__3___boxed as *mut core::ffi::c_void,
                    11,
                    10,
                );
                crate::leanh::lean_closure_set(v___f_1030_, 0, v_ref_1012_);
                crate::leanh::lean_closure_set(v___f_1030_, 1, v___x_1027_);
                crate::leanh::lean_closure_set(v___f_1030_, 2, v___x_1028_);
                crate::leanh::lean_closure_set(v___f_1030_, 3, v___x_1029_);
                crate::leanh::lean_closure_set(v___f_1030_, 4, v_logMessage_1026_);
                crate::leanh::lean_closure_set(v___f_1030_, 5, v_toBind_1015_);
                crate::leanh::lean_closure_set(v___f_1030_, 6, v_getFileName_1025_);
                crate::leanh::lean_closure_set(v___f_1030_, 7, v_msgData_1016_);
                crate::leanh::lean_closure_set(v___f_1030_, 8, v_inst_1017_);
                crate::leanh::lean_closure_set(v___f_1030_, 9, v_toMonadFileMap_1023_);
                v___x_1031_ = crate::leanh::lean_apply_4(
                    v_toBind_1015_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v_getRef_1024_,
                    v___f_1030_,
                );
                return v___x_1031_;
            }
            2 => {
                if v___y_1033_ == 0 {
                    v___y_1022_ = v_severity_1018_;
                    state = 1;
                    continue;
                } else {
                    v___y_1022_ = v___x_1019_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___redArg___lam__4___boxed(
    mut v_inst_1040_: *mut crate::leanh::LeanObject,
    mut v_ref_1041_: *mut crate::leanh::LeanObject,
    mut v___y_1042_: *mut crate::leanh::LeanObject,
    mut v_isSilent_1043_: *mut crate::leanh::LeanObject,
    mut v_toBind_1044_: *mut crate::leanh::LeanObject,
    mut v_msgData_1045_: *mut crate::leanh::LeanObject,
    mut v_inst_1046_: *mut crate::leanh::LeanObject,
    mut v_severity_1047_: *mut crate::leanh::LeanObject,
    mut v___x_1048_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1049_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_496__boxed_1050_: u8 = 0;
    let mut v_isSilent_boxed_1051_: u8 = 0;
    let mut v_severity_boxed_1052_: u8 = 0;
    let mut v___x_498__boxed_1053_: u8 = 0;
    let mut v_res_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_496__boxed_1050_ = (crate::leanh::lean_unbox(v___y_1042_) as u8);
    v_isSilent_boxed_1051_ = (crate::leanh::lean_unbox(v_isSilent_1043_) as u8);
    v_severity_boxed_1052_ = (crate::leanh::lean_unbox(v_severity_1047_) as u8);
    v___x_498__boxed_1053_ = (crate::leanh::lean_unbox(v___x_1048_) as u8);
    v_res_1054_ = l_Lean_logAt___redArg___lam__4(
        v_inst_1040_,
        v_ref_1041_,
        v___y_496__boxed_1050_,
        v_isSilent_boxed_1051_,
        v_toBind_1044_,
        v_msgData_1045_,
        v_inst_1046_,
        v_severity_boxed_1052_,
        v___x_498__boxed_1053_,
        v_____do__lift_1049_,
    );
    crate::leanh::lean_dec_ref(v_____do__lift_1049_);
    return v_res_1054_;
}
pub unsafe fn l_Lean_logAt___redArg(
    mut v_inst_1055_: *mut crate::leanh::LeanObject,
    mut v_inst_1056_: *mut crate::leanh::LeanObject,
    mut v_inst_1057_: *mut crate::leanh::LeanObject,
    mut v_inst_1058_: *mut crate::leanh::LeanObject,
    mut v_ref_1059_: *mut crate::leanh::LeanObject,
    mut v_msgData_1060_: *mut crate::leanh::LeanObject,
    mut v_severity_1061_: u8,
    mut v_isSilent_1062_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1063_: u8 = 0;
    let mut v___y_1065_: u8 = 0;
    let mut v_toBind_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: u8 = 0;
    let mut v___x_1078_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1063_ = 2;
                v___x_1077_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1061_, v___x_1063_);
                if v___x_1077_ == 0 {
                    v___y_1065_ = v___x_1077_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_msgData_1060_);
                    v___x_1078_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1060_);
                    v___y_1065_ = v___x_1078_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_1065_ == 0 {
                    v_toBind_1066_ = crate::leanh::lean_ctor_get(v_inst_1055_, 1);
                    crate::leanh::lean_inc_n(v_toBind_1066_, 2);
                    crate::leanh::lean_dec_ref(v_inst_1055_);
                    v___x_1067_ = crate::leanh::lean_box((v___y_1065_) as usize);
                    v___x_1068_ = crate::leanh::lean_box((v_isSilent_1062_) as usize);
                    v___x_1069_ = crate::leanh::lean_box((v_severity_1061_) as usize);
                    v___x_1070_ = crate::leanh::lean_box((v___x_1063_) as usize);
                    v___f_1071_ = crate::leanh::lean_alloc_closure(
                        l_Lean_logAt___redArg___lam__4___boxed as *mut core::ffi::c_void,
                        10,
                        9,
                    );
                    crate::leanh::lean_closure_set(v___f_1071_, 0, v_inst_1056_);
                    crate::leanh::lean_closure_set(v___f_1071_, 1, v_ref_1059_);
                    crate::leanh::lean_closure_set(v___f_1071_, 2, v___x_1067_);
                    crate::leanh::lean_closure_set(v___f_1071_, 3, v___x_1068_);
                    crate::leanh::lean_closure_set(v___f_1071_, 4, v_toBind_1066_);
                    crate::leanh::lean_closure_set(v___f_1071_, 5, v_msgData_1060_);
                    crate::leanh::lean_closure_set(v___f_1071_, 6, v_inst_1057_);
                    crate::leanh::lean_closure_set(v___f_1071_, 7, v___x_1069_);
                    crate::leanh::lean_closure_set(v___f_1071_, 8, v___x_1070_);
                    v___x_1072_ = crate::leanh::lean_apply_4(
                        v_toBind_1066_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v_inst_1058_,
                        v___f_1071_,
                    );
                    return v___x_1072_;
                } else {
                    crate::leanh::lean_dec_ref(v_msgData_1060_);
                    crate::leanh::lean_dec(v_ref_1059_);
                    crate::leanh::lean_dec(v_inst_1058_);
                    crate::leanh::lean_dec(v_inst_1057_);
                    crate::leanh::lean_dec_ref(v_inst_1056_);
                    v_toApplicative_1073_ = crate::leanh::lean_ctor_get(v_inst_1055_, 0);
                    crate::leanh::lean_inc_ref(v_toApplicative_1073_);
                    crate::leanh::lean_dec_ref(v_inst_1055_);
                    v_toPure_1074_ = crate::leanh::lean_ctor_get(v_toApplicative_1073_, 1);
                    crate::leanh::lean_inc(v_toPure_1074_);
                    crate::leanh::lean_dec_ref(v_toApplicative_1073_);
                    v___x_1075_ = crate::leanh::lean_box(0);
                    v___x_1076_ = crate::leanh::lean_apply_2(
                        v_toPure_1074_,
                        crate::leanh::lean_box(0),
                        v___x_1075_,
                    );
                    return v___x_1076_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___redArg___boxed(
    mut v_inst_1079_: *mut crate::leanh::LeanObject,
    mut v_inst_1080_: *mut crate::leanh::LeanObject,
    mut v_inst_1081_: *mut crate::leanh::LeanObject,
    mut v_inst_1082_: *mut crate::leanh::LeanObject,
    mut v_ref_1083_: *mut crate::leanh::LeanObject,
    mut v_msgData_1084_: *mut crate::leanh::LeanObject,
    mut v_severity_1085_: *mut crate::leanh::LeanObject,
    mut v_isSilent_1086_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_1087_: u8 = 0;
    let mut v_isSilent_boxed_1088_: u8 = 0;
    let mut v_res_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_1087_ = (crate::leanh::lean_unbox(v_severity_1085_) as u8);
    v_isSilent_boxed_1088_ = (crate::leanh::lean_unbox(v_isSilent_1086_) as u8);
    v_res_1089_ = l_Lean_logAt___redArg(
        v_inst_1079_,
        v_inst_1080_,
        v_inst_1081_,
        v_inst_1082_,
        v_ref_1083_,
        v_msgData_1084_,
        v_severity_boxed_1087_,
        v_isSilent_boxed_1088_,
    );
    return v_res_1089_;
}
pub unsafe fn l_Lean_logAt(
    mut v_m_1090_: *mut crate::leanh::LeanObject,
    mut v_inst_1091_: *mut crate::leanh::LeanObject,
    mut v_inst_1092_: *mut crate::leanh::LeanObject,
    mut v_inst_1093_: *mut crate::leanh::LeanObject,
    mut v_inst_1094_: *mut crate::leanh::LeanObject,
    mut v_ref_1095_: *mut crate::leanh::LeanObject,
    mut v_msgData_1096_: *mut crate::leanh::LeanObject,
    mut v_severity_1097_: u8,
    mut v_isSilent_1098_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1099_ = l_Lean_logAt___redArg(
        v_inst_1091_,
        v_inst_1092_,
        v_inst_1093_,
        v_inst_1094_,
        v_ref_1095_,
        v_msgData_1096_,
        v_severity_1097_,
        v_isSilent_1098_,
    );
    return v___x_1099_;
}
pub unsafe fn l_Lean_logAt___boxed(
    mut v_m_1100_: *mut crate::leanh::LeanObject,
    mut v_inst_1101_: *mut crate::leanh::LeanObject,
    mut v_inst_1102_: *mut crate::leanh::LeanObject,
    mut v_inst_1103_: *mut crate::leanh::LeanObject,
    mut v_inst_1104_: *mut crate::leanh::LeanObject,
    mut v_ref_1105_: *mut crate::leanh::LeanObject,
    mut v_msgData_1106_: *mut crate::leanh::LeanObject,
    mut v_severity_1107_: *mut crate::leanh::LeanObject,
    mut v_isSilent_1108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_1109_: u8 = 0;
    let mut v_isSilent_boxed_1110_: u8 = 0;
    let mut v_res_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_1109_ = (crate::leanh::lean_unbox(v_severity_1107_) as u8);
    v_isSilent_boxed_1110_ = (crate::leanh::lean_unbox(v_isSilent_1108_) as u8);
    v_res_1111_ = l_Lean_logAt(
        v_m_1100_,
        v_inst_1101_,
        v_inst_1102_,
        v_inst_1103_,
        v_inst_1104_,
        v_ref_1105_,
        v_msgData_1106_,
        v_severity_boxed_1109_,
        v_isSilent_boxed_1110_,
    );
    return v_res_1111_;
}
pub unsafe fn l_Lean_logErrorAt___redArg(
    mut v_inst_1112_: *mut crate::leanh::LeanObject,
    mut v_inst_1113_: *mut crate::leanh::LeanObject,
    mut v_inst_1114_: *mut crate::leanh::LeanObject,
    mut v_inst_1115_: *mut crate::leanh::LeanObject,
    mut v_ref_1116_: *mut crate::leanh::LeanObject,
    mut v_msgData_1117_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1118_: u8 = 0;
    let mut v___x_1119_: u8 = 0;
    let mut v___x_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1118_ = 2;
    v___x_1119_ = 0;
    v___x_1120_ = l_Lean_logAt___redArg(
        v_inst_1112_,
        v_inst_1113_,
        v_inst_1114_,
        v_inst_1115_,
        v_ref_1116_,
        v_msgData_1117_,
        v___x_1118_,
        v___x_1119_,
    );
    return v___x_1120_;
}
pub unsafe fn l_Lean_logErrorAt(
    mut v_m_1121_: *mut crate::leanh::LeanObject,
    mut v_inst_1122_: *mut crate::leanh::LeanObject,
    mut v_inst_1123_: *mut crate::leanh::LeanObject,
    mut v_inst_1124_: *mut crate::leanh::LeanObject,
    mut v_inst_1125_: *mut crate::leanh::LeanObject,
    mut v_ref_1126_: *mut crate::leanh::LeanObject,
    mut v_msgData_1127_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1128_ = l_Lean_logErrorAt___redArg(
        v_inst_1122_,
        v_inst_1123_,
        v_inst_1124_,
        v_inst_1125_,
        v_ref_1126_,
        v_msgData_1127_,
    );
    return v___x_1128_;
}
pub unsafe fn l_Lean_logNamedErrorAt___redArg(
    mut v_inst_1129_: *mut crate::leanh::LeanObject,
    mut v_inst_1130_: *mut crate::leanh::LeanObject,
    mut v_inst_1131_: *mut crate::leanh::LeanObject,
    mut v_inst_1132_: *mut crate::leanh::LeanObject,
    mut v_ref_1133_: *mut crate::leanh::LeanObject,
    mut v_name_1134_: *mut crate::leanh::LeanObject,
    mut v_msgData_1135_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: u8 = 0;
    let mut v___x_1138_: u8 = 0;
    let mut v___x_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1136_ = l_Lean_MessageData_tagWithErrorName(v_msgData_1135_, v_name_1134_);
    v___x_1137_ = 2;
    v___x_1138_ = 0;
    v___x_1139_ = l_Lean_logAt___redArg(
        v_inst_1129_,
        v_inst_1130_,
        v_inst_1131_,
        v_inst_1132_,
        v_ref_1133_,
        v___x_1136_,
        v___x_1137_,
        v___x_1138_,
    );
    return v___x_1139_;
}
pub unsafe fn l_Lean_logNamedErrorAt(
    mut v_m_1140_: *mut crate::leanh::LeanObject,
    mut v_inst_1141_: *mut crate::leanh::LeanObject,
    mut v_inst_1142_: *mut crate::leanh::LeanObject,
    mut v_inst_1143_: *mut crate::leanh::LeanObject,
    mut v_inst_1144_: *mut crate::leanh::LeanObject,
    mut v_ref_1145_: *mut crate::leanh::LeanObject,
    mut v_name_1146_: *mut crate::leanh::LeanObject,
    mut v_msgData_1147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1148_ = l_Lean_logNamedErrorAt___redArg(
        v_inst_1141_,
        v_inst_1142_,
        v_inst_1143_,
        v_inst_1144_,
        v_ref_1145_,
        v_name_1146_,
        v_msgData_1147_,
    );
    return v___x_1148_;
}
pub unsafe fn l_Lean_logWarningAt___redArg(
    mut v_inst_1149_: *mut crate::leanh::LeanObject,
    mut v_inst_1150_: *mut crate::leanh::LeanObject,
    mut v_inst_1151_: *mut crate::leanh::LeanObject,
    mut v_inst_1152_: *mut crate::leanh::LeanObject,
    mut v_ref_1153_: *mut crate::leanh::LeanObject,
    mut v_msgData_1154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1155_: u8 = 0;
    let mut v___x_1156_: u8 = 0;
    let mut v___x_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1155_ = 1;
    v___x_1156_ = 0;
    v___x_1157_ = l_Lean_logAt___redArg(
        v_inst_1149_,
        v_inst_1150_,
        v_inst_1151_,
        v_inst_1152_,
        v_ref_1153_,
        v_msgData_1154_,
        v___x_1155_,
        v___x_1156_,
    );
    return v___x_1157_;
}
pub unsafe fn l_Lean_logWarningAt(
    mut v_m_1158_: *mut crate::leanh::LeanObject,
    mut v_inst_1159_: *mut crate::leanh::LeanObject,
    mut v_inst_1160_: *mut crate::leanh::LeanObject,
    mut v_inst_1161_: *mut crate::leanh::LeanObject,
    mut v_inst_1162_: *mut crate::leanh::LeanObject,
    mut v_ref_1163_: *mut crate::leanh::LeanObject,
    mut v_msgData_1164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1165_ = l_Lean_logWarningAt___redArg(
        v_inst_1159_,
        v_inst_1160_,
        v_inst_1161_,
        v_inst_1162_,
        v_ref_1163_,
        v_msgData_1164_,
    );
    return v___x_1165_;
}
pub unsafe fn l_Lean_logNamedWarningAt___redArg(
    mut v_inst_1166_: *mut crate::leanh::LeanObject,
    mut v_inst_1167_: *mut crate::leanh::LeanObject,
    mut v_inst_1168_: *mut crate::leanh::LeanObject,
    mut v_inst_1169_: *mut crate::leanh::LeanObject,
    mut v_ref_1170_: *mut crate::leanh::LeanObject,
    mut v_name_1171_: *mut crate::leanh::LeanObject,
    mut v_msgData_1172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: u8 = 0;
    let mut v___x_1175_: u8 = 0;
    let mut v___x_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1173_ = l_Lean_MessageData_tagWithErrorName(v_msgData_1172_, v_name_1171_);
    v___x_1174_ = 1;
    v___x_1175_ = 0;
    v___x_1176_ = l_Lean_logAt___redArg(
        v_inst_1166_,
        v_inst_1167_,
        v_inst_1168_,
        v_inst_1169_,
        v_ref_1170_,
        v___x_1173_,
        v___x_1174_,
        v___x_1175_,
    );
    return v___x_1176_;
}
pub unsafe fn l_Lean_logNamedWarningAt(
    mut v_m_1177_: *mut crate::leanh::LeanObject,
    mut v_inst_1178_: *mut crate::leanh::LeanObject,
    mut v_inst_1179_: *mut crate::leanh::LeanObject,
    mut v_inst_1180_: *mut crate::leanh::LeanObject,
    mut v_inst_1181_: *mut crate::leanh::LeanObject,
    mut v_ref_1182_: *mut crate::leanh::LeanObject,
    mut v_name_1183_: *mut crate::leanh::LeanObject,
    mut v_msgData_1184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1185_ = l_Lean_logNamedWarningAt___redArg(
        v_inst_1178_,
        v_inst_1179_,
        v_inst_1180_,
        v_inst_1181_,
        v_ref_1182_,
        v_name_1183_,
        v_msgData_1184_,
    );
    return v___x_1185_;
}
pub unsafe fn l_Lean_logInfoAt___redArg(
    mut v_inst_1186_: *mut crate::leanh::LeanObject,
    mut v_inst_1187_: *mut crate::leanh::LeanObject,
    mut v_inst_1188_: *mut crate::leanh::LeanObject,
    mut v_inst_1189_: *mut crate::leanh::LeanObject,
    mut v_ref_1190_: *mut crate::leanh::LeanObject,
    mut v_msgData_1191_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1192_: u8 = 0;
    let mut v___x_1193_: u8 = 0;
    let mut v___x_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1192_ = 0;
    v___x_1193_ = 0;
    v___x_1194_ = l_Lean_logAt___redArg(
        v_inst_1186_,
        v_inst_1187_,
        v_inst_1188_,
        v_inst_1189_,
        v_ref_1190_,
        v_msgData_1191_,
        v___x_1192_,
        v___x_1193_,
    );
    return v___x_1194_;
}
pub unsafe fn l_Lean_logInfoAt(
    mut v_m_1195_: *mut crate::leanh::LeanObject,
    mut v_inst_1196_: *mut crate::leanh::LeanObject,
    mut v_inst_1197_: *mut crate::leanh::LeanObject,
    mut v_inst_1198_: *mut crate::leanh::LeanObject,
    mut v_inst_1199_: *mut crate::leanh::LeanObject,
    mut v_ref_1200_: *mut crate::leanh::LeanObject,
    mut v_msgData_1201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1202_ = l_Lean_logInfoAt___redArg(
        v_inst_1196_,
        v_inst_1197_,
        v_inst_1198_,
        v_inst_1199_,
        v_ref_1200_,
        v_msgData_1201_,
    );
    return v___x_1202_;
}
pub unsafe fn l_Lean_log___redArg___lam__0(
    mut v_inst_1203_: *mut crate::leanh::LeanObject,
    mut v_inst_1204_: *mut crate::leanh::LeanObject,
    mut v_inst_1205_: *mut crate::leanh::LeanObject,
    mut v_inst_1206_: *mut crate::leanh::LeanObject,
    mut v_msgData_1207_: *mut crate::leanh::LeanObject,
    mut v_severity_1208_: u8,
    mut v_isSilent_1209_: u8,
    mut v_ref_1210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1211_ = l_Lean_logAt___redArg(
        v_inst_1203_,
        v_inst_1204_,
        v_inst_1205_,
        v_inst_1206_,
        v_ref_1210_,
        v_msgData_1207_,
        v_severity_1208_,
        v_isSilent_1209_,
    );
    return v___x_1211_;
}
pub unsafe fn l_Lean_log___redArg___lam__0___boxed(
    mut v_inst_1212_: *mut crate::leanh::LeanObject,
    mut v_inst_1213_: *mut crate::leanh::LeanObject,
    mut v_inst_1214_: *mut crate::leanh::LeanObject,
    mut v_inst_1215_: *mut crate::leanh::LeanObject,
    mut v_msgData_1216_: *mut crate::leanh::LeanObject,
    mut v_severity_1217_: *mut crate::leanh::LeanObject,
    mut v_isSilent_1218_: *mut crate::leanh::LeanObject,
    mut v_ref_1219_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_1220_: u8 = 0;
    let mut v_isSilent_boxed_1221_: u8 = 0;
    let mut v_res_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_1220_ = (crate::leanh::lean_unbox(v_severity_1217_) as u8);
    v_isSilent_boxed_1221_ = (crate::leanh::lean_unbox(v_isSilent_1218_) as u8);
    v_res_1222_ = l_Lean_log___redArg___lam__0(
        v_inst_1212_,
        v_inst_1213_,
        v_inst_1214_,
        v_inst_1215_,
        v_msgData_1216_,
        v_severity_boxed_1220_,
        v_isSilent_boxed_1221_,
        v_ref_1219_,
    );
    return v_res_1222_;
}
pub unsafe fn l_Lean_log___redArg(
    mut v_inst_1223_: *mut crate::leanh::LeanObject,
    mut v_inst_1224_: *mut crate::leanh::LeanObject,
    mut v_inst_1225_: *mut crate::leanh::LeanObject,
    mut v_inst_1226_: *mut crate::leanh::LeanObject,
    mut v_msgData_1227_: *mut crate::leanh::LeanObject,
    mut v_severity_1228_: u8,
    mut v_isSilent_1229_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRef_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_1230_ = crate::leanh::lean_ctor_get(v_inst_1223_, 1);
    crate::leanh::lean_inc(v_toBind_1230_);
    v_getRef_1231_ = crate::leanh::lean_ctor_get(v_inst_1224_, 1);
    crate::leanh::lean_inc(v_getRef_1231_);
    v___x_1232_ = crate::leanh::lean_box((v_severity_1228_) as usize);
    v___x_1233_ = crate::leanh::lean_box((v_isSilent_1229_) as usize);
    v___f_1234_ = crate::leanh::lean_alloc_closure(
        l_Lean_log___redArg___lam__0___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    crate::leanh::lean_closure_set(v___f_1234_, 0, v_inst_1223_);
    crate::leanh::lean_closure_set(v___f_1234_, 1, v_inst_1224_);
    crate::leanh::lean_closure_set(v___f_1234_, 2, v_inst_1225_);
    crate::leanh::lean_closure_set(v___f_1234_, 3, v_inst_1226_);
    crate::leanh::lean_closure_set(v___f_1234_, 4, v_msgData_1227_);
    crate::leanh::lean_closure_set(v___f_1234_, 5, v___x_1232_);
    crate::leanh::lean_closure_set(v___f_1234_, 6, v___x_1233_);
    v___x_1235_ = crate::leanh::lean_apply_4(
        v_toBind_1230_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getRef_1231_,
        v___f_1234_,
    );
    return v___x_1235_;
}
pub unsafe fn l_Lean_log___redArg___boxed(
    mut v_inst_1236_: *mut crate::leanh::LeanObject,
    mut v_inst_1237_: *mut crate::leanh::LeanObject,
    mut v_inst_1238_: *mut crate::leanh::LeanObject,
    mut v_inst_1239_: *mut crate::leanh::LeanObject,
    mut v_msgData_1240_: *mut crate::leanh::LeanObject,
    mut v_severity_1241_: *mut crate::leanh::LeanObject,
    mut v_isSilent_1242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_1243_: u8 = 0;
    let mut v_isSilent_boxed_1244_: u8 = 0;
    let mut v_res_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_1243_ = (crate::leanh::lean_unbox(v_severity_1241_) as u8);
    v_isSilent_boxed_1244_ = (crate::leanh::lean_unbox(v_isSilent_1242_) as u8);
    v_res_1245_ = l_Lean_log___redArg(
        v_inst_1236_,
        v_inst_1237_,
        v_inst_1238_,
        v_inst_1239_,
        v_msgData_1240_,
        v_severity_boxed_1243_,
        v_isSilent_boxed_1244_,
    );
    return v_res_1245_;
}
pub unsafe fn l_Lean_log(
    mut v_m_1246_: *mut crate::leanh::LeanObject,
    mut v_inst_1247_: *mut crate::leanh::LeanObject,
    mut v_inst_1248_: *mut crate::leanh::LeanObject,
    mut v_inst_1249_: *mut crate::leanh::LeanObject,
    mut v_inst_1250_: *mut crate::leanh::LeanObject,
    mut v_msgData_1251_: *mut crate::leanh::LeanObject,
    mut v_severity_1252_: u8,
    mut v_isSilent_1253_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1254_ = l_Lean_log___redArg(
        v_inst_1247_,
        v_inst_1248_,
        v_inst_1249_,
        v_inst_1250_,
        v_msgData_1251_,
        v_severity_1252_,
        v_isSilent_1253_,
    );
    return v___x_1254_;
}
pub unsafe fn l_Lean_log___boxed(
    mut v_m_1255_: *mut crate::leanh::LeanObject,
    mut v_inst_1256_: *mut crate::leanh::LeanObject,
    mut v_inst_1257_: *mut crate::leanh::LeanObject,
    mut v_inst_1258_: *mut crate::leanh::LeanObject,
    mut v_inst_1259_: *mut crate::leanh::LeanObject,
    mut v_msgData_1260_: *mut crate::leanh::LeanObject,
    mut v_severity_1261_: *mut crate::leanh::LeanObject,
    mut v_isSilent_1262_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_1263_: u8 = 0;
    let mut v_isSilent_boxed_1264_: u8 = 0;
    let mut v_res_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_1263_ = (crate::leanh::lean_unbox(v_severity_1261_) as u8);
    v_isSilent_boxed_1264_ = (crate::leanh::lean_unbox(v_isSilent_1262_) as u8);
    v_res_1265_ = l_Lean_log(
        v_m_1255_,
        v_inst_1256_,
        v_inst_1257_,
        v_inst_1258_,
        v_inst_1259_,
        v_msgData_1260_,
        v_severity_boxed_1263_,
        v_isSilent_boxed_1264_,
    );
    return v_res_1265_;
}
pub unsafe fn l_Lean_logError___redArg(
    mut v_inst_1266_: *mut crate::leanh::LeanObject,
    mut v_inst_1267_: *mut crate::leanh::LeanObject,
    mut v_inst_1268_: *mut crate::leanh::LeanObject,
    mut v_inst_1269_: *mut crate::leanh::LeanObject,
    mut v_msgData_1270_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1271_: u8 = 0;
    let mut v___x_1272_: u8 = 0;
    let mut v___x_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1271_ = 2;
    v___x_1272_ = 0;
    v___x_1273_ = l_Lean_log___redArg(
        v_inst_1266_,
        v_inst_1267_,
        v_inst_1268_,
        v_inst_1269_,
        v_msgData_1270_,
        v___x_1271_,
        v___x_1272_,
    );
    return v___x_1273_;
}
pub unsafe fn l_Lean_logError(
    mut v_m_1274_: *mut crate::leanh::LeanObject,
    mut v_inst_1275_: *mut crate::leanh::LeanObject,
    mut v_inst_1276_: *mut crate::leanh::LeanObject,
    mut v_inst_1277_: *mut crate::leanh::LeanObject,
    mut v_inst_1278_: *mut crate::leanh::LeanObject,
    mut v_msgData_1279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1280_ = l_Lean_logError___redArg(
        v_inst_1275_,
        v_inst_1276_,
        v_inst_1277_,
        v_inst_1278_,
        v_msgData_1279_,
    );
    return v___x_1280_;
}
pub unsafe fn l_Lean_logNamedError___redArg(
    mut v_inst_1281_: *mut crate::leanh::LeanObject,
    mut v_inst_1282_: *mut crate::leanh::LeanObject,
    mut v_inst_1283_: *mut crate::leanh::LeanObject,
    mut v_inst_1284_: *mut crate::leanh::LeanObject,
    mut v_name_1285_: *mut crate::leanh::LeanObject,
    mut v_msgData_1286_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: u8 = 0;
    let mut v___x_1289_: u8 = 0;
    let mut v___x_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1287_ = l_Lean_MessageData_tagWithErrorName(v_msgData_1286_, v_name_1285_);
    v___x_1288_ = 2;
    v___x_1289_ = 0;
    v___x_1290_ = l_Lean_log___redArg(
        v_inst_1281_,
        v_inst_1282_,
        v_inst_1283_,
        v_inst_1284_,
        v___x_1287_,
        v___x_1288_,
        v___x_1289_,
    );
    return v___x_1290_;
}
pub unsafe fn l_Lean_logNamedError(
    mut v_m_1291_: *mut crate::leanh::LeanObject,
    mut v_inst_1292_: *mut crate::leanh::LeanObject,
    mut v_inst_1293_: *mut crate::leanh::LeanObject,
    mut v_inst_1294_: *mut crate::leanh::LeanObject,
    mut v_inst_1295_: *mut crate::leanh::LeanObject,
    mut v_name_1296_: *mut crate::leanh::LeanObject,
    mut v_msgData_1297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1298_ = l_Lean_logNamedError___redArg(
        v_inst_1292_,
        v_inst_1293_,
        v_inst_1294_,
        v_inst_1295_,
        v_name_1296_,
        v_msgData_1297_,
    );
    return v___x_1298_;
}
pub unsafe fn l_Lean_logWarning___redArg(
    mut v_inst_1299_: *mut crate::leanh::LeanObject,
    mut v_inst_1300_: *mut crate::leanh::LeanObject,
    mut v_inst_1301_: *mut crate::leanh::LeanObject,
    mut v_inst_1302_: *mut crate::leanh::LeanObject,
    mut v_msgData_1303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1304_: u8 = 0;
    let mut v___x_1305_: u8 = 0;
    let mut v___x_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1304_ = 1;
    v___x_1305_ = 0;
    v___x_1306_ = l_Lean_log___redArg(
        v_inst_1299_,
        v_inst_1300_,
        v_inst_1301_,
        v_inst_1302_,
        v_msgData_1303_,
        v___x_1304_,
        v___x_1305_,
    );
    return v___x_1306_;
}
pub unsafe fn l_Lean_logWarning(
    mut v_m_1307_: *mut crate::leanh::LeanObject,
    mut v_inst_1308_: *mut crate::leanh::LeanObject,
    mut v_inst_1309_: *mut crate::leanh::LeanObject,
    mut v_inst_1310_: *mut crate::leanh::LeanObject,
    mut v_inst_1311_: *mut crate::leanh::LeanObject,
    mut v_msgData_1312_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1313_ = l_Lean_logWarning___redArg(
        v_inst_1308_,
        v_inst_1309_,
        v_inst_1310_,
        v_inst_1311_,
        v_msgData_1312_,
    );
    return v___x_1313_;
}
pub unsafe fn l_Lean_logNamedWarning___redArg(
    mut v_inst_1314_: *mut crate::leanh::LeanObject,
    mut v_inst_1315_: *mut crate::leanh::LeanObject,
    mut v_inst_1316_: *mut crate::leanh::LeanObject,
    mut v_inst_1317_: *mut crate::leanh::LeanObject,
    mut v_name_1318_: *mut crate::leanh::LeanObject,
    mut v_msgData_1319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: u8 = 0;
    let mut v___x_1322_: u8 = 0;
    let mut v___x_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1320_ = l_Lean_MessageData_tagWithErrorName(v_msgData_1319_, v_name_1318_);
    v___x_1321_ = 1;
    v___x_1322_ = 0;
    v___x_1323_ = l_Lean_log___redArg(
        v_inst_1314_,
        v_inst_1315_,
        v_inst_1316_,
        v_inst_1317_,
        v___x_1320_,
        v___x_1321_,
        v___x_1322_,
    );
    return v___x_1323_;
}
pub unsafe fn l_Lean_logNamedWarning(
    mut v_m_1324_: *mut crate::leanh::LeanObject,
    mut v_inst_1325_: *mut crate::leanh::LeanObject,
    mut v_inst_1326_: *mut crate::leanh::LeanObject,
    mut v_inst_1327_: *mut crate::leanh::LeanObject,
    mut v_inst_1328_: *mut crate::leanh::LeanObject,
    mut v_name_1329_: *mut crate::leanh::LeanObject,
    mut v_msgData_1330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1331_ = l_Lean_logNamedWarning___redArg(
        v_inst_1325_,
        v_inst_1326_,
        v_inst_1327_,
        v_inst_1328_,
        v_name_1329_,
        v_msgData_1330_,
    );
    return v___x_1331_;
}
pub unsafe fn l_Lean_logInfo___redArg(
    mut v_inst_1332_: *mut crate::leanh::LeanObject,
    mut v_inst_1333_: *mut crate::leanh::LeanObject,
    mut v_inst_1334_: *mut crate::leanh::LeanObject,
    mut v_inst_1335_: *mut crate::leanh::LeanObject,
    mut v_msgData_1336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1337_: u8 = 0;
    let mut v___x_1338_: u8 = 0;
    let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1337_ = 0;
    v___x_1338_ = 0;
    v___x_1339_ = l_Lean_log___redArg(
        v_inst_1332_,
        v_inst_1333_,
        v_inst_1334_,
        v_inst_1335_,
        v_msgData_1336_,
        v___x_1337_,
        v___x_1338_,
    );
    return v___x_1339_;
}
pub unsafe fn l_Lean_logInfo(
    mut v_m_1340_: *mut crate::leanh::LeanObject,
    mut v_inst_1341_: *mut crate::leanh::LeanObject,
    mut v_inst_1342_: *mut crate::leanh::LeanObject,
    mut v_inst_1343_: *mut crate::leanh::LeanObject,
    mut v_inst_1344_: *mut crate::leanh::LeanObject,
    mut v_msgData_1345_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1346_ = l_Lean_logInfo___redArg(
        v_inst_1341_,
        v_inst_1342_,
        v_inst_1343_,
        v_inst_1344_,
        v_msgData_1345_,
    );
    return v___x_1346_;
}
pub unsafe fn _init_l_Lean_logUnknownDecl___redArg___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1348_ = l_Lean_logUnknownDecl___redArg___closed__0;
    v___x_1349_ = l_Lean_stringToMessageData(v___x_1348_);
    return v___x_1349_;
}
pub unsafe fn _init_l_Lean_logUnknownDecl___redArg___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1351_ = l_Lean_logUnknownDecl___redArg___closed__2;
    v___x_1352_ = l_Lean_stringToMessageData(v___x_1351_);
    return v___x_1352_;
}
pub unsafe fn l_Lean_logUnknownDecl___redArg(
    mut v_inst_1353_: *mut crate::leanh::LeanObject,
    mut v_inst_1354_: *mut crate::leanh::LeanObject,
    mut v_inst_1355_: *mut crate::leanh::LeanObject,
    mut v_inst_1356_: *mut crate::leanh::LeanObject,
    mut v_declName_1357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1358_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_logUnknownDecl___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_logUnknownDecl___redArg___closed__1_once),
        _init_l_Lean_logUnknownDecl___redArg___closed__1,
    );
    v___x_1359_ = l_Lean_MessageData_ofName(v_declName_1357_);
    v___x_1360_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1360_, 0, v___x_1358_);
    crate::leanh::lean_ctor_set(v___x_1360_, 1, v___x_1359_);
    v___x_1361_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_logUnknownDecl___redArg___closed__3),
        core::ptr::addr_of_mut!(l_Lean_logUnknownDecl___redArg___closed__3_once),
        _init_l_Lean_logUnknownDecl___redArg___closed__3,
    );
    v___x_1362_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1362_, 0, v___x_1360_);
    crate::leanh::lean_ctor_set(v___x_1362_, 1, v___x_1361_);
    v___x_1363_ = l_Lean_logError___redArg(
        v_inst_1353_,
        v_inst_1354_,
        v_inst_1355_,
        v_inst_1356_,
        v___x_1362_,
    );
    return v___x_1363_;
}
pub unsafe fn l_Lean_logUnknownDecl(
    mut v_m_1364_: *mut crate::leanh::LeanObject,
    mut v_inst_1365_: *mut crate::leanh::LeanObject,
    mut v_inst_1366_: *mut crate::leanh::LeanObject,
    mut v_inst_1367_: *mut crate::leanh::LeanObject,
    mut v_inst_1368_: *mut crate::leanh::LeanObject,
    mut v_declName_1369_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1370_ = l_Lean_logUnknownDecl___redArg(
        v_inst_1365_,
        v_inst_1366_,
        v_inst_1367_,
        v_inst_1368_,
        v_declName_1369_,
    );
    return v___x_1370_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Log(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_ErrorExplanation(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Log_0__Lean_initFn_00___x40_Lean_Log_3265821404____hygCtx___hyg_4_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_warningAsError = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_warningAsError);
    crate::leanh::lean_dec_ref(res);
    l_Lean_errorDescriptionWidget = _init_l_Lean_errorDescriptionWidget();
    crate::leanh::lean_mark_persistent(l_Lean_errorDescriptionWidget);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Log(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Log(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_ErrorExplanation(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Log(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Log(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Log(builtin);
}
