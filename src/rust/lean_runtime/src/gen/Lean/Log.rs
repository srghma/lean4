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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint64,
    lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8, lean_ctor_set_uint64, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_n, lean_inc_ref, lean_io_result_get_value,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent,
    lean_obj_once, lean_obj_tag, lean_uint64_once, lean_unbox, lean_unsigned_to_nat,
};
pub static l___private_Lean_Log_0__Lean_initFn___closed__0_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [119, 97, 114, 110, 105, 110, 103, 65, 115, 69, 114, 114, 111, 114, 0]};
static mut l___private_Lean_Log_0__Lean_initFn___closed__0_00___x40_Lean_Log_3265821404____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Log_0__Lean_initFn___closed__0_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Log_0__Lean_initFn___closed__1_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Log_0__Lean_initFn___closed__0_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value) as *mut LeanObject,5238986158861308483 as *mut LeanObject] };
static mut l___private_Lean_Log_0__Lean_initFn___closed__1_00___x40_Lean_Log_3265821404____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Log_0__Lean_initFn___closed__1_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Log_0__Lean_initFn___closed__2_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value: LeanStringObject<25> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [116, 114, 101, 97, 116, 32, 119, 97, 114, 110, 105, 110, 103, 115, 32, 97, 115, 32, 101, 114, 114, 111, 114, 115, 0]};
static mut l___private_Lean_Log_0__Lean_initFn___closed__2_00___x40_Lean_Log_3265821404____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Log_0__Lean_initFn___closed__2_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Log_0__Lean_initFn___closed__3_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Log_0__Lean_initFn___closed__2_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Log_0__Lean_initFn___closed__3_00___x40_Lean_Log_3265821404____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Log_0__Lean_initFn___closed__3_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Log_0__Lean_initFn___closed__4_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Log_0__Lean_initFn___closed__4_00___x40_Lean_Log_3265821404____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Log_0__Lean_initFn___closed__4_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Log_0__Lean_initFn___closed__5_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Log_0__Lean_initFn___closed__4_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l___private_Lean_Log_0__Lean_initFn___closed__5_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Log_0__Lean_initFn___closed__5_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Log_0__Lean_initFn___closed__0_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value) as *mut LeanObject,9646326620821618514 as *mut LeanObject] };
static mut l___private_Lean_Log_0__Lean_initFn___closed__5_00___x40_Lean_Log_3265821404____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Log_0__Lean_initFn___closed__5_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l_Lean_errorDescriptionWidget___closed__0_value: LeanStringObject<623> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_errorDescriptionWidget___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_errorDescriptionWidget___closed__0_value) as *mut LeanObject;
static mut l_Lean_errorDescriptionWidget___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_errorDescriptionWidget___closed__1: u64 = 0;
static mut l_Lean_errorDescriptionWidget___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_errorDescriptionWidget___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_errorDescriptionWidget: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__0_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [102, 105, 110, 100, 47, 63, 100, 111, 109, 97, 105, 110, 61, 0]};
static mut l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__0_value
) as *mut LeanObject;
static mut l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__2_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [38, 110, 97, 109, 101, 61, 0]};
static mut l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__2_value
) as *mut LeanObject;
static mut l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__3:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__4_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [101, 114, 114, 111, 114, 68, 101, 115, 99, 114, 105, 112, 116, 105, 111, 110, 87, 105, 100, 103, 101, 116, 0]};
static mut l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__4_value
) as *mut LeanObject;
static l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Log_0__Lean_initFn___closed__4_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__4_value) as *mut LeanObject,11821295174094476641 as *mut LeanObject] };
static mut l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__5_value
) as *mut LeanObject;
pub static l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__6_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [99, 111, 100, 101, 0]};
static mut l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__6_value
) as *mut LeanObject;
pub static l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__7_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [101, 120, 112, 108, 97, 110, 97, 116, 105, 111, 110, 85, 114, 108, 0]};
static mut l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__7_value
) as *mut LeanObject;
pub static l_Lean_logAt___redArg___lam__0___closed__0_value: LeanStringObject<1> =
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
static mut l_Lean_logAt___redArg___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_logAt___redArg___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_logUnknownDecl___redArg___closed__0_value: LeanStringObject<22> =
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
            117, 110, 107, 110, 111, 119, 110, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111,
            110, 32, 39, 0,
        ],
    };
static mut l_Lean_logUnknownDecl___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_logUnknownDecl___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_logUnknownDecl___redArg___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_logUnknownDecl___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_logUnknownDecl___redArg___closed__2_value: LeanStringObject<2> =
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
static mut l_Lean_logUnknownDecl___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_logUnknownDecl___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_logUnknownDecl___redArg___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_logUnknownDecl___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_instMonadLogOfMonadLift___redArg___lam__0(
    mut v_logMessage_686_: *mut LeanObject,
    mut v_inst_687_: *mut LeanObject,
    mut v_msg_688_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut LeanObject = core::ptr::null_mut();
    v___x_689_ = lean_apply_1(v_logMessage_686_, v_msg_688_);
    v___x_690_ = lean_apply_2(v_inst_687_, lean_box(0), v___x_689_);
    return v___x_690_;
}
pub unsafe fn l_Lean_instMonadLogOfMonadLift___redArg(
    mut v_inst_691_: *mut LeanObject,
    mut v_inst_692_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toMonadFileMap_693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getRef_694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getFileName_695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasErrors_696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_logMessage_697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_700_: u8 = 0;
    let mut v___f_701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_709_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toMonadFileMap_693_ = lean_ctor_get(v_inst_692_, 0);
                v_getRef_694_ = lean_ctor_get(v_inst_692_, 1);
                v_getFileName_695_ = lean_ctor_get(v_inst_692_, 2);
                v_hasErrors_696_ = lean_ctor_get(v_inst_692_, 3);
                v_logMessage_697_ = lean_ctor_get(v_inst_692_, 4);
                v_isSharedCheck_709_ = (!lean_is_exclusive(v_inst_692_)) as u8;
                if v_isSharedCheck_709_ == 0 {
                    v___x_699_ = v_inst_692_;
                    v_isShared_700_ = v_isSharedCheck_709_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_logMessage_697_);
                    lean_inc(v_hasErrors_696_);
                    lean_inc(v_getFileName_695_);
                    lean_inc(v_getRef_694_);
                    lean_inc(v_toMonadFileMap_693_);
                    lean_dec(v_inst_692_);
                    v___x_699_ = lean_box(0);
                    v_isShared_700_ = v_isSharedCheck_709_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc_n(v_inst_691_, 4);
                v___f_701_ = lean_alloc_closure(
                    l_Lean_instMonadLogOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_701_, 0, v_logMessage_697_);
                lean_closure_set(v___f_701_, 1, v_inst_691_);
                v___x_702_ = lean_apply_2(v_inst_691_, lean_box(0), v_toMonadFileMap_693_);
                v___x_703_ = lean_apply_2(v_inst_691_, lean_box(0), v_getRef_694_);
                v___x_704_ = lean_apply_2(v_inst_691_, lean_box(0), v_getFileName_695_);
                v___x_705_ = lean_apply_2(v_inst_691_, lean_box(0), v_hasErrors_696_);
                if v_isShared_700_ == 0 {
                    lean_ctor_set(v___x_699_, 4, v___f_701_);
                    lean_ctor_set(v___x_699_, 3, v___x_705_);
                    lean_ctor_set(v___x_699_, 2, v___x_704_);
                    lean_ctor_set(v___x_699_, 1, v___x_703_);
                    lean_ctor_set(v___x_699_, 0, v___x_702_);
                    v___x_707_ = v___x_699_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_708_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_708_, 0, v___x_702_);
                    lean_ctor_set(v_reuseFailAlloc_708_, 1, v___x_703_);
                    lean_ctor_set(v_reuseFailAlloc_708_, 2, v___x_704_);
                    lean_ctor_set(v_reuseFailAlloc_708_, 3, v___x_705_);
                    lean_ctor_set(v_reuseFailAlloc_708_, 4, v___f_701_);
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
    mut v_m_710_: *mut LeanObject,
    mut v_n_711_: *mut LeanObject,
    mut v_inst_712_: *mut LeanObject,
    mut v_inst_713_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_714_: *mut LeanObject = core::ptr::null_mut();
    v___x_714_ = l_Lean_instMonadLogOfMonadLift___redArg(v_inst_712_, v_inst_713_);
    return v___x_714_;
}
pub unsafe fn l_Lean_getRefPos___redArg___lam__0(
    mut v_toPure_715_: *mut LeanObject,
    mut v_ref_716_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_717_: u8 = 0;
    let mut v___x_718_: *mut LeanObject = core::ptr::null_mut();
    v___x_717_ = 0;
    v___x_718_ = l_Lean_Syntax_getPos_x3f(v_ref_716_, v___x_717_);
    if lean_obj_tag(v___x_718_) == 0 {
        let mut v___x_719_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_720_: *mut LeanObject = core::ptr::null_mut();
        v___x_719_ = lean_unsigned_to_nat(0);
        v___x_720_ = lean_apply_2(v_toPure_715_, lean_box(0), v___x_719_);
        return v___x_720_;
    } else {
        let mut v_val_721_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_722_: *mut LeanObject = core::ptr::null_mut();
        v_val_721_ = lean_ctor_get(v___x_718_, 0);
        lean_inc(v_val_721_);
        lean_dec_ref_known(v___x_718_, 1);
        v___x_722_ = lean_apply_2(v_toPure_715_, lean_box(0), v_val_721_);
        return v___x_722_;
    }
}
pub unsafe fn l_Lean_getRefPos___redArg___lam__0___boxed(
    mut v_toPure_723_: *mut LeanObject,
    mut v_ref_724_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_725_: *mut LeanObject = core::ptr::null_mut();
    v_res_725_ = l_Lean_getRefPos___redArg___lam__0(v_toPure_723_, v_ref_724_);
    lean_dec(v_ref_724_);
    return v_res_725_;
}
pub unsafe fn l_Lean_getRefPos___redArg(
    mut v_inst_726_: *mut LeanObject,
    mut v_inst_727_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getRef_730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_733_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_728_ = lean_ctor_get(v_inst_726_, 0);
    lean_inc_ref(v_toApplicative_728_);
    v_toBind_729_ = lean_ctor_get(v_inst_726_, 1);
    lean_inc(v_toBind_729_);
    lean_dec_ref(v_inst_726_);
    v_getRef_730_ = lean_ctor_get(v_inst_727_, 1);
    lean_inc(v_getRef_730_);
    lean_dec_ref(v_inst_727_);
    v_toPure_731_ = lean_ctor_get(v_toApplicative_728_, 1);
    lean_inc(v_toPure_731_);
    lean_dec_ref(v_toApplicative_728_);
    v___f_732_ = lean_alloc_closure(
        l_Lean_getRefPos___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_732_, 0, v_toPure_731_);
    v___x_733_ = lean_apply_4(
        v_toBind_729_,
        lean_box(0),
        lean_box(0),
        v_getRef_730_,
        v___f_732_,
    );
    return v___x_733_;
}
pub unsafe fn l_Lean_getRefPos(
    mut v_m_734_: *mut LeanObject,
    mut v_inst_735_: *mut LeanObject,
    mut v_inst_736_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_737_: *mut LeanObject = core::ptr::null_mut();
    v___x_737_ = l_Lean_getRefPos___redArg(v_inst_735_, v_inst_736_);
    return v___x_737_;
}
pub unsafe fn l_Lean_getRefPosition___redArg___lam__0(
    mut v_fileMap_738_: *mut LeanObject,
    mut v_toPure_739_: *mut LeanObject,
    mut v_____do__lift_740_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_742_: *mut LeanObject = core::ptr::null_mut();
    v___x_741_ = l_Lean_FileMap_toPosition(v_fileMap_738_, v_____do__lift_740_);
    v___x_742_ = lean_apply_2(v_toPure_739_, lean_box(0), v___x_741_);
    return v___x_742_;
}
pub unsafe fn l_Lean_getRefPosition___redArg___lam__0___boxed(
    mut v_fileMap_743_: *mut LeanObject,
    mut v_toPure_744_: *mut LeanObject,
    mut v_____do__lift_745_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_746_: *mut LeanObject = core::ptr::null_mut();
    v_res_746_ =
        l_Lean_getRefPosition___redArg___lam__0(v_fileMap_743_, v_toPure_744_, v_____do__lift_745_);
    lean_dec(v_____do__lift_745_);
    return v_res_746_;
}
pub unsafe fn l_Lean_getRefPosition___redArg___lam__1(
    mut v_toPure_747_: *mut LeanObject,
    mut v_inst_748_: *mut LeanObject,
    mut v_inst_749_: *mut LeanObject,
    mut v_toBind_750_: *mut LeanObject,
    mut v_fileMap_751_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_754_: *mut LeanObject = core::ptr::null_mut();
    v___f_752_ = lean_alloc_closure(
        l_Lean_getRefPosition___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_752_, 0, v_fileMap_751_);
    lean_closure_set(v___f_752_, 1, v_toPure_747_);
    v___x_753_ = l_Lean_getRefPos___redArg(v_inst_748_, v_inst_749_);
    v___x_754_ = lean_apply_4(
        v_toBind_750_,
        lean_box(0),
        lean_box(0),
        v___x_753_,
        v___f_752_,
    );
    return v___x_754_;
}
pub unsafe fn l_Lean_getRefPosition___redArg(
    mut v_inst_755_: *mut LeanObject,
    mut v_inst_756_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toMonadFileMap_759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_762_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_757_ = lean_ctor_get(v_inst_755_, 0);
    v_toBind_758_ = lean_ctor_get(v_inst_755_, 1);
    lean_inc_n(v_toBind_758_, 2);
    v_toMonadFileMap_759_ = lean_ctor_get(v_inst_756_, 0);
    lean_inc(v_toMonadFileMap_759_);
    v_toPure_760_ = lean_ctor_get(v_toApplicative_757_, 1);
    lean_inc(v_toPure_760_);
    v___f_761_ = lean_alloc_closure(
        l_Lean_getRefPosition___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_761_, 0, v_toPure_760_);
    lean_closure_set(v___f_761_, 1, v_inst_755_);
    lean_closure_set(v___f_761_, 2, v_inst_756_);
    lean_closure_set(v___f_761_, 3, v_toBind_758_);
    v___x_762_ = lean_apply_4(
        v_toBind_758_,
        lean_box(0),
        lean_box(0),
        v_toMonadFileMap_759_,
        v___f_761_,
    );
    return v___x_762_;
}
pub unsafe fn l_Lean_getRefPosition(
    mut v_m_763_: *mut LeanObject,
    mut v_inst_764_: *mut LeanObject,
    mut v_inst_765_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_766_: *mut LeanObject = core::ptr::null_mut();
    v___x_766_ = l_Lean_getRefPosition___redArg(v_inst_764_, v_inst_765_);
    return v___x_766_;
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Log_0__Lean_initFn_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__spec__0(
    mut v_name_767_: *mut LeanObject,
    mut v_decl_768_: *mut LeanObject,
    mut v_ref_769_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_defValue_771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_descr_772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_775_: u8 = 0;
    let mut v___x_776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_780_: u8 = 0;
    let mut v___x_781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_785_: u8 = 0;
    let mut v_unused_786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_790_: u8 = 0;
    let mut v___x_792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_794_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_771_ = lean_ctor_get(v_decl_768_, 0);
                v_descr_772_ = lean_ctor_get(v_decl_768_, 1);
                v_deprecation_x3f_773_ = lean_ctor_get(v_decl_768_, 2);
                v___x_774_ = lean_alloc_ctor(1, 0, (1) as u32);
                v___x_775_ = (lean_unbox(v_defValue_771_) as u8);
                lean_ctor_set_uint8(v___x_774_, 0 as u32, v___x_775_);
                lean_inc(v_deprecation_x3f_773_);
                lean_inc_ref(v_descr_772_);
                lean_inc_n(v_name_767_, 2);
                v___x_776_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_776_, 0, v_name_767_);
                lean_ctor_set(v___x_776_, 1, v_ref_769_);
                lean_ctor_set(v___x_776_, 2, v___x_774_);
                lean_ctor_set(v___x_776_, 3, v_descr_772_);
                lean_ctor_set(v___x_776_, 4, v_deprecation_x3f_773_);
                v___x_777_ = lean_register_option(v_name_767_, v___x_776_);
                if lean_obj_tag(v___x_777_) == 0 {
                    v_isSharedCheck_785_ = (!lean_is_exclusive(v___x_777_)) as u8;
                    if v_isSharedCheck_785_ == 0 {
                        v_unused_786_ = lean_ctor_get(v___x_777_, 0);
                        lean_dec(v_unused_786_);
                        v___x_779_ = v___x_777_;
                        v_isShared_780_ = v_isSharedCheck_785_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_777_);
                        v___x_779_ = lean_box(0);
                        v_isShared_780_ = v_isSharedCheck_785_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_name_767_);
                    v_a_787_ = lean_ctor_get(v___x_777_, 0);
                    v_isSharedCheck_794_ = (!lean_is_exclusive(v___x_777_)) as u8;
                    if v_isSharedCheck_794_ == 0 {
                        v___x_789_ = v___x_777_;
                        v_isShared_790_ = v_isSharedCheck_794_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_787_);
                        lean_dec(v___x_777_);
                        v___x_789_ = lean_box(0);
                        v_isShared_790_ = v_isSharedCheck_794_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_defValue_771_);
                v___x_781_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_781_, 0, v_name_767_);
                lean_ctor_set(v___x_781_, 1, v_defValue_771_);
                if v_isShared_780_ == 0 {
                    lean_ctor_set(v___x_779_, 0, v___x_781_);
                    v___x_783_ = v___x_779_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_784_, 0, v___x_781_);
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
                    v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_793_, 0, v_a_787_);
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
    mut v_name_795_: *mut LeanObject,
    mut v_decl_796_: *mut LeanObject,
    mut v_ref_797_: *mut LeanObject,
    mut v_a_798_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_799_: *mut LeanObject = core::ptr::null_mut();
    v_res_799_ = l_Lean_Option_register___at___00__private_Lean_Log_0__Lean_initFn_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__spec__0(v_name_795_, v_decl_796_, v_ref_797_);
    lean_dec_ref(v_decl_796_);
    return v_res_799_;
}
pub unsafe fn l___private_Lean_Log_0__Lean_initFn_00___x40_Lean_Log_3265821404____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_817_: *mut LeanObject = core::ptr::null_mut();
    v___x_814_ = l___private_Lean_Log_0__Lean_initFn___closed__1_00___x40_Lean_Log_3265821404____hygCtx___hyg_4_;
    v___x_815_ = l___private_Lean_Log_0__Lean_initFn___closed__3_00___x40_Lean_Log_3265821404____hygCtx___hyg_4_;
    v___x_816_ = l___private_Lean_Log_0__Lean_initFn___closed__5_00___x40_Lean_Log_3265821404____hygCtx___hyg_4_;
    v___x_817_ = l_Lean_Option_register___at___00__private_Lean_Log_0__Lean_initFn_00___x40_Lean_Log_3265821404____hygCtx___hyg_4__spec__0(v___x_814_, v___x_815_, v___x_816_);
    return v___x_817_;
}
pub unsafe fn l___private_Lean_Log_0__Lean_initFn_00___x40_Lean_Log_3265821404____hygCtx___hyg_4____boxed(
    mut v_a_818_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_819_: *mut LeanObject = core::ptr::null_mut();
    v_res_819_ =
        l___private_Lean_Log_0__Lean_initFn_00___x40_Lean_Log_3265821404____hygCtx___hyg_4_();
    return v_res_819_;
}
pub unsafe fn _init_l_Lean_errorDescriptionWidget___closed__1() -> u64 {
    let mut v___x_821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_822_: u64 = 0;
    v___x_821_ = l_Lean_errorDescriptionWidget___closed__0;
    v___x_822_ = lean_string_hash(v___x_821_);
    return v___x_822_;
}
pub unsafe fn _init_l_Lean_errorDescriptionWidget___closed__2() -> *mut LeanObject {
    let mut v___x_823_: u64 = 0;
    let mut v___x_824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut LeanObject = core::ptr::null_mut();
    v___x_823_ = lean_uint64_once(
        core::ptr::addr_of_mut!(l_Lean_errorDescriptionWidget___closed__1),
        core::ptr::addr_of_mut!(l_Lean_errorDescriptionWidget___closed__1_once),
        _init_l_Lean_errorDescriptionWidget___closed__1,
    );
    v___x_824_ = l_Lean_errorDescriptionWidget___closed__0;
    v___x_825_ = lean_alloc_ctor(0, 1, (8) as u32);
    lean_ctor_set(v___x_825_, 0, v___x_824_);
    lean_ctor_set_uint64(
        v___x_825_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_823_,
    );
    return v___x_825_;
}
pub unsafe fn _init_l_Lean_errorDescriptionWidget() -> *mut LeanObject {
    let mut v___x_826_: *mut LeanObject = core::ptr::null_mut();
    v___x_826_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_errorDescriptionWidget___closed__2),
        core::ptr::addr_of_mut!(l_Lean_errorDescriptionWidget___closed__2_once),
        _init_l_Lean_errorDescriptionWidget___closed__2,
    );
    return v___x_826_;
}
pub unsafe fn l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___lam__0(
    mut v___x_827_: *mut LeanObject,
    mut v___y_828_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_829_: *mut LeanObject = core::ptr::null_mut();
    v___x_829_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_829_, 0, v___x_827_);
    lean_ctor_set(v___x_829_, 1, v___y_828_);
    return v___x_829_;
}
pub unsafe fn _init_l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__1()
-> *mut LeanObject {
    let mut v___x_831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_833_: *mut LeanObject = core::ptr::null_mut();
    v___x_831_ = l_Lean_errorExplanationManualDomain;
    v___x_832_ =
        l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__0;
    v___x_833_ = lean_string_append(v___x_832_, v___x_831_);
    return v___x_833_;
}
pub unsafe fn _init_l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__3()
-> *mut LeanObject {
    let mut v___x_835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_837_: *mut LeanObject = core::ptr::null_mut();
    v___x_835_ =
        l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__2;
    v___x_836_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__1_once), _init_l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__1);
    v___x_837_ = lean_string_append(v___x_836_, v___x_835_);
    return v___x_837_;
}
pub unsafe fn l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
    mut v_msg_844_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_850_: u8 = 0;
    let mut v___x_851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_javascriptHash_852_: u64 = 0;
    let mut v___x_853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_855_: u8 = 0;
    let mut v___x_856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_url_858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inst_872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_877_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_msg_844_);
                v___x_845_ = l_Lean_MessageData_stripNestedTags(v_msg_844_);
                v___x_846_ = l_Lean_MessageData_errorName_x3f(v___x_845_);
                lean_dec_ref(v___x_845_);
                if lean_obj_tag(v___x_846_) == 0 {
                    return v_msg_844_;
                } else {
                    v_val_847_ = lean_ctor_get(v___x_846_, 0);
                    v_isSharedCheck_877_ = (!lean_is_exclusive(v___x_846_)) as u8;
                    if v_isSharedCheck_877_ == 0 {
                        v___x_849_ = v___x_846_;
                        v_isShared_850_ = v_isSharedCheck_877_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_847_);
                        lean_dec(v___x_846_);
                        v___x_849_ = lean_box(0);
                        v_isShared_850_ = v_isSharedCheck_877_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_851_ = l_Lean_errorDescriptionWidget;
                v_javascriptHash_852_ = lean_ctor_get_uint64(
                    v___x_851_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v___x_853_ = l_Lean_manualRoot;
                v___x_854_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__3_once), _init_l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__3);
                v___x_855_ = 1;
                v___x_856_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_val_847_, v___x_855_,
                );
                v___x_857_ = lean_string_append(v___x_854_, v___x_856_);
                v_url_858_ = lean_string_append(v___x_853_, v___x_857_);
                lean_dec_ref(v___x_857_);
                v___x_859_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__5;
                v___x_860_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__6;
                if v_isShared_850_ == 0 {
                    lean_ctor_set_tag(v___x_849_, 3);
                    lean_ctor_set(v___x_849_, 0, v___x_856_);
                    v___x_862_ = v___x_849_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_876_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_876_, 0, v___x_856_);
                    v___x_862_ = v_reuseFailAlloc_876_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_863_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_863_, 0, v___x_860_);
                lean_ctor_set(v___x_863_, 1, v___x_862_);
                v___x_864_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__7;
                v___x_865_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_865_, 0, v_url_858_);
                v___x_866_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_866_, 0, v___x_864_);
                lean_ctor_set(v___x_866_, 1, v___x_865_);
                v___x_867_ = lean_box(0);
                v___x_868_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_868_, 0, v___x_866_);
                lean_ctor_set(v___x_868_, 1, v___x_867_);
                v___x_869_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_869_, 0, v___x_863_);
                lean_ctor_set(v___x_869_, 1, v___x_868_);
                v___x_870_ = l_Lean_Json_mkObj(v___x_869_);
                lean_dec_ref_known(v___x_869_, 2);
                v___f_871_ = lean_alloc_closure(
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___lam__0
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_871_, 0, v___x_870_);
                v_inst_872_ = lean_alloc_ctor(0, 2, (8) as u32);
                lean_ctor_set(v_inst_872_, 0, v___x_859_);
                lean_ctor_set(v_inst_872_, 1, v___f_871_);
                lean_ctor_set_uint64(
                    v_inst_872_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v_javascriptHash_852_,
                );
                v___x_873_ = l_Lean_MessageData_nil;
                v___x_874_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_874_, 0, v_inst_872_);
                lean_ctor_set(v___x_874_, 1, v___x_873_);
                v___x_875_ = l_Lean_MessageData_composePreservingKind(v_msg_844_, v___x_874_);
                return v___x_875_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___redArg___lam__0(
    mut v_fileMap_879_: *mut LeanObject,
    mut v___y_880_: *mut LeanObject,
    mut v___y_881_: *mut LeanObject,
    mut v___y_882_: u8,
    mut v___y_883_: u8,
    mut v_isSilent_884_: u8,
    mut v_msgData_885_: *mut LeanObject,
    mut v_logMessage_886_: *mut LeanObject,
    mut v_____do__lift_887_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_893_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_fileMap_879_);
    v___x_888_ = l_Lean_FileMap_toPosition(v_fileMap_879_, v___y_880_);
    v___x_889_ = l_Lean_FileMap_toPosition(v_fileMap_879_, v___y_881_);
    v___x_890_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_890_, 0, v___x_889_);
    v___x_891_ = l_Lean_logAt___redArg___lam__0___closed__0;
    v___x_892_ = lean_alloc_ctor(0, 5, (3) as u32);
    lean_ctor_set(v___x_892_, 0, v_____do__lift_887_);
    lean_ctor_set(v___x_892_, 1, v___x_888_);
    lean_ctor_set(v___x_892_, 2, v___x_890_);
    lean_ctor_set(v___x_892_, 3, v___x_891_);
    lean_ctor_set(v___x_892_, 4, v_msgData_885_);
    lean_ctor_set_uint8(
        v___x_892_,
        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
        v___y_882_,
    );
    lean_ctor_set_uint8(
        v___x_892_,
        (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
        v___y_883_,
    );
    lean_ctor_set_uint8(
        v___x_892_,
        (core::mem::size_of::<*mut LeanObject>() * 5 + 2) as u32,
        v_isSilent_884_,
    );
    v___x_893_ = lean_apply_1(v_logMessage_886_, v___x_892_);
    return v___x_893_;
}
pub unsafe fn l_Lean_logAt___redArg___lam__0___boxed(
    mut v_fileMap_894_: *mut LeanObject,
    mut v___y_895_: *mut LeanObject,
    mut v___y_896_: *mut LeanObject,
    mut v___y_897_: *mut LeanObject,
    mut v___y_898_: *mut LeanObject,
    mut v_isSilent_899_: *mut LeanObject,
    mut v_msgData_900_: *mut LeanObject,
    mut v_logMessage_901_: *mut LeanObject,
    mut v_____do__lift_902_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_375__boxed_903_: u8 = 0;
    let mut v___y_376__boxed_904_: u8 = 0;
    let mut v_isSilent_boxed_905_: u8 = 0;
    let mut v_res_906_: *mut LeanObject = core::ptr::null_mut();
    v___y_375__boxed_903_ = (lean_unbox(v___y_897_) as u8);
    v___y_376__boxed_904_ = (lean_unbox(v___y_898_) as u8);
    v_isSilent_boxed_905_ = (lean_unbox(v_isSilent_899_) as u8);
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
    lean_dec(v___y_896_);
    lean_dec(v___y_895_);
    return v_res_906_;
}
pub unsafe fn l_Lean_logAt___redArg___lam__1(
    mut v_fileMap_907_: *mut LeanObject,
    mut v___y_908_: *mut LeanObject,
    mut v___y_909_: *mut LeanObject,
    mut v___y_910_: u8,
    mut v___y_911_: u8,
    mut v_isSilent_912_: u8,
    mut v_logMessage_913_: *mut LeanObject,
    mut v_toBind_914_: *mut LeanObject,
    mut v_getFileName_915_: *mut LeanObject,
    mut v_msgData_916_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut LeanObject = core::ptr::null_mut();
    v___x_917_ = lean_box((v___y_910_) as usize);
    v___x_918_ = lean_box((v___y_911_) as usize);
    v___x_919_ = lean_box((v_isSilent_912_) as usize);
    v___f_920_ = lean_alloc_closure(
        l_Lean_logAt___redArg___lam__0___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    lean_closure_set(v___f_920_, 0, v_fileMap_907_);
    lean_closure_set(v___f_920_, 1, v___y_908_);
    lean_closure_set(v___f_920_, 2, v___y_909_);
    lean_closure_set(v___f_920_, 3, v___x_917_);
    lean_closure_set(v___f_920_, 4, v___x_918_);
    lean_closure_set(v___f_920_, 5, v___x_919_);
    lean_closure_set(v___f_920_, 6, v_msgData_916_);
    lean_closure_set(v___f_920_, 7, v_logMessage_913_);
    v___x_921_ = lean_apply_4(
        v_toBind_914_,
        lean_box(0),
        lean_box(0),
        v_getFileName_915_,
        v___f_920_,
    );
    return v___x_921_;
}
pub unsafe fn l_Lean_logAt___redArg___lam__1___boxed(
    mut v_fileMap_922_: *mut LeanObject,
    mut v___y_923_: *mut LeanObject,
    mut v___y_924_: *mut LeanObject,
    mut v___y_925_: *mut LeanObject,
    mut v___y_926_: *mut LeanObject,
    mut v_isSilent_927_: *mut LeanObject,
    mut v_logMessage_928_: *mut LeanObject,
    mut v_toBind_929_: *mut LeanObject,
    mut v_getFileName_930_: *mut LeanObject,
    mut v_msgData_931_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_403__boxed_932_: u8 = 0;
    let mut v___y_404__boxed_933_: u8 = 0;
    let mut v_isSilent_boxed_934_: u8 = 0;
    let mut v_res_935_: *mut LeanObject = core::ptr::null_mut();
    v___y_403__boxed_932_ = (lean_unbox(v___y_925_) as u8);
    v___y_404__boxed_933_ = (lean_unbox(v___y_926_) as u8);
    v_isSilent_boxed_934_ = (lean_unbox(v_isSilent_927_) as u8);
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
    mut v___y_936_: *mut LeanObject,
    mut v___y_937_: *mut LeanObject,
    mut v___y_938_: u8,
    mut v___y_939_: u8,
    mut v_isSilent_940_: u8,
    mut v_logMessage_941_: *mut LeanObject,
    mut v_toBind_942_: *mut LeanObject,
    mut v_getFileName_943_: *mut LeanObject,
    mut v_msgData_944_: *mut LeanObject,
    mut v_inst_945_: *mut LeanObject,
    mut v_fileMap_946_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_953_: *mut LeanObject = core::ptr::null_mut();
    v___x_947_ = lean_box((v___y_938_) as usize);
    v___x_948_ = lean_box((v___y_939_) as usize);
    v___x_949_ = lean_box((v_isSilent_940_) as usize);
    lean_inc(v_toBind_942_);
    v___f_950_ = lean_alloc_closure(
        l_Lean_logAt___redArg___lam__1___boxed as *mut core::ffi::c_void,
        10,
        9,
    );
    lean_closure_set(v___f_950_, 0, v_fileMap_946_);
    lean_closure_set(v___f_950_, 1, v___y_936_);
    lean_closure_set(v___f_950_, 2, v___y_937_);
    lean_closure_set(v___f_950_, 3, v___x_947_);
    lean_closure_set(v___f_950_, 4, v___x_948_);
    lean_closure_set(v___f_950_, 5, v___x_949_);
    lean_closure_set(v___f_950_, 6, v_logMessage_941_);
    lean_closure_set(v___f_950_, 7, v_toBind_942_);
    lean_closure_set(v___f_950_, 8, v_getFileName_943_);
    v___x_951_ =
        l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_944_);
    v___x_952_ = lean_apply_1(v_inst_945_, v___x_951_);
    v___x_953_ = lean_apply_4(
        v_toBind_942_,
        lean_box(0),
        lean_box(0),
        v___x_952_,
        v___f_950_,
    );
    return v___x_953_;
}
pub unsafe fn l_Lean_logAt___redArg___lam__2___boxed(
    mut v___y_954_: *mut LeanObject,
    mut v___y_955_: *mut LeanObject,
    mut v___y_956_: *mut LeanObject,
    mut v___y_957_: *mut LeanObject,
    mut v_isSilent_958_: *mut LeanObject,
    mut v_logMessage_959_: *mut LeanObject,
    mut v_toBind_960_: *mut LeanObject,
    mut v_getFileName_961_: *mut LeanObject,
    mut v_msgData_962_: *mut LeanObject,
    mut v_inst_963_: *mut LeanObject,
    mut v_fileMap_964_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_425__boxed_965_: u8 = 0;
    let mut v___y_426__boxed_966_: u8 = 0;
    let mut v_isSilent_boxed_967_: u8 = 0;
    let mut v_res_968_: *mut LeanObject = core::ptr::null_mut();
    v___y_425__boxed_965_ = (lean_unbox(v___y_956_) as u8);
    v___y_426__boxed_966_ = (lean_unbox(v___y_957_) as u8);
    v_isSilent_boxed_967_ = (lean_unbox(v_isSilent_958_) as u8);
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
    mut v_ref_969_: *mut LeanObject,
    mut v___y_970_: u8,
    mut v___y_971_: u8,
    mut v_isSilent_972_: u8,
    mut v_logMessage_973_: *mut LeanObject,
    mut v_toBind_974_: *mut LeanObject,
    mut v_getFileName_975_: *mut LeanObject,
    mut v_msgData_976_: *mut LeanObject,
    mut v_inst_977_: *mut LeanObject,
    mut v_toMonadFileMap_978_: *mut LeanObject,
    mut v_____do__lift_979_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_995_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_988_ = l_Lean_replaceRef(v_ref_969_, v_____do__lift_979_);
                v___x_993_ = l_Lean_Syntax_getPos_x3f(v_ref_988_, v___y_970_);
                if lean_obj_tag(v___x_993_) == 0 {
                    v___x_994_ = lean_unsigned_to_nat(0);
                    v___y_990_ = v___x_994_;
                    state = 2;
                    continue;
                } else {
                    v_val_995_ = lean_ctor_get(v___x_993_, 0);
                    lean_inc(v_val_995_);
                    lean_dec_ref_known(v___x_993_, 1);
                    v___y_990_ = v_val_995_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_983_ = lean_box((v___y_970_) as usize);
                v___x_984_ = lean_box((v___y_971_) as usize);
                v___x_985_ = lean_box((v_isSilent_972_) as usize);
                lean_inc(v_toBind_974_);
                v___f_986_ = lean_alloc_closure(
                    l_Lean_logAt___redArg___lam__2___boxed as *mut core::ffi::c_void,
                    11,
                    10,
                );
                lean_closure_set(v___f_986_, 0, v___y_981_);
                lean_closure_set(v___f_986_, 1, v___y_982_);
                lean_closure_set(v___f_986_, 2, v___x_983_);
                lean_closure_set(v___f_986_, 3, v___x_984_);
                lean_closure_set(v___f_986_, 4, v___x_985_);
                lean_closure_set(v___f_986_, 5, v_logMessage_973_);
                lean_closure_set(v___f_986_, 6, v_toBind_974_);
                lean_closure_set(v___f_986_, 7, v_getFileName_975_);
                lean_closure_set(v___f_986_, 8, v_msgData_976_);
                lean_closure_set(v___f_986_, 9, v_inst_977_);
                v___x_987_ = lean_apply_4(
                    v_toBind_974_,
                    lean_box(0),
                    lean_box(0),
                    v_toMonadFileMap_978_,
                    v___f_986_,
                );
                return v___x_987_;
            }
            2 => {
                v___x_991_ = l_Lean_Syntax_getTailPos_x3f(v_ref_988_, v___y_970_);
                lean_dec(v_ref_988_);
                if lean_obj_tag(v___x_991_) == 0 {
                    lean_inc(v___y_990_);
                    v___y_981_ = v___y_990_;
                    v___y_982_ = v___y_990_;
                    state = 1;
                    continue;
                } else {
                    v_val_992_ = lean_ctor_get(v___x_991_, 0);
                    lean_inc(v_val_992_);
                    lean_dec_ref_known(v___x_991_, 1);
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
    mut v_ref_996_: *mut LeanObject,
    mut v___y_997_: *mut LeanObject,
    mut v___y_998_: *mut LeanObject,
    mut v_isSilent_999_: *mut LeanObject,
    mut v_logMessage_1000_: *mut LeanObject,
    mut v_toBind_1001_: *mut LeanObject,
    mut v_getFileName_1002_: *mut LeanObject,
    mut v_msgData_1003_: *mut LeanObject,
    mut v_inst_1004_: *mut LeanObject,
    mut v_toMonadFileMap_1005_: *mut LeanObject,
    mut v_____do__lift_1006_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_453__boxed_1007_: u8 = 0;
    let mut v___y_454__boxed_1008_: u8 = 0;
    let mut v_isSilent_boxed_1009_: u8 = 0;
    let mut v_res_1010_: *mut LeanObject = core::ptr::null_mut();
    v___y_453__boxed_1007_ = (lean_unbox(v___y_997_) as u8);
    v___y_454__boxed_1008_ = (lean_unbox(v___y_998_) as u8);
    v_isSilent_boxed_1009_ = (lean_unbox(v_isSilent_999_) as u8);
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
    lean_dec(v_____do__lift_1006_);
    lean_dec(v_ref_996_);
    return v_res_1010_;
}
pub unsafe fn l_Lean_logAt___redArg___lam__4(
    mut v_inst_1011_: *mut LeanObject,
    mut v_ref_1012_: *mut LeanObject,
    mut v___y_1013_: u8,
    mut v_isSilent_1014_: u8,
    mut v_toBind_1015_: *mut LeanObject,
    mut v_msgData_1016_: *mut LeanObject,
    mut v_inst_1017_: *mut LeanObject,
    mut v_severity_1018_: u8,
    mut v___x_1019_: u8,
    mut v_____do__lift_1020_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1022_: u8 = 0;
    let mut v_toMonadFileMap_1023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getRef_1024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getFileName_1025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_logMessage_1026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1033_: u8 = 0;
    let mut v___x_1034_: u8 = 0;
    let mut v___x_1035_: u8 = 0;
    let mut v___x_1036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut LeanObject = core::ptr::null_mut();
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
                    v___x_1039_ = (lean_unbox(v___x_1038_) as u8);
                    lean_dec(v___x_1038_);
                    v___y_1033_ = v___x_1039_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v_toMonadFileMap_1023_ = lean_ctor_get(v_inst_1011_, 0);
                lean_inc(v_toMonadFileMap_1023_);
                v_getRef_1024_ = lean_ctor_get(v_inst_1011_, 1);
                lean_inc(v_getRef_1024_);
                v_getFileName_1025_ = lean_ctor_get(v_inst_1011_, 2);
                lean_inc(v_getFileName_1025_);
                v_logMessage_1026_ = lean_ctor_get(v_inst_1011_, 4);
                lean_inc(v_logMessage_1026_);
                lean_dec_ref(v_inst_1011_);
                v___x_1027_ = lean_box((v___y_1013_) as usize);
                v___x_1028_ = lean_box((v___y_1022_) as usize);
                v___x_1029_ = lean_box((v_isSilent_1014_) as usize);
                lean_inc(v_toBind_1015_);
                v___f_1030_ = lean_alloc_closure(
                    l_Lean_logAt___redArg___lam__3___boxed as *mut core::ffi::c_void,
                    11,
                    10,
                );
                lean_closure_set(v___f_1030_, 0, v_ref_1012_);
                lean_closure_set(v___f_1030_, 1, v___x_1027_);
                lean_closure_set(v___f_1030_, 2, v___x_1028_);
                lean_closure_set(v___f_1030_, 3, v___x_1029_);
                lean_closure_set(v___f_1030_, 4, v_logMessage_1026_);
                lean_closure_set(v___f_1030_, 5, v_toBind_1015_);
                lean_closure_set(v___f_1030_, 6, v_getFileName_1025_);
                lean_closure_set(v___f_1030_, 7, v_msgData_1016_);
                lean_closure_set(v___f_1030_, 8, v_inst_1017_);
                lean_closure_set(v___f_1030_, 9, v_toMonadFileMap_1023_);
                v___x_1031_ = lean_apply_4(
                    v_toBind_1015_,
                    lean_box(0),
                    lean_box(0),
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
    mut v_inst_1040_: *mut LeanObject,
    mut v_ref_1041_: *mut LeanObject,
    mut v___y_1042_: *mut LeanObject,
    mut v_isSilent_1043_: *mut LeanObject,
    mut v_toBind_1044_: *mut LeanObject,
    mut v_msgData_1045_: *mut LeanObject,
    mut v_inst_1046_: *mut LeanObject,
    mut v_severity_1047_: *mut LeanObject,
    mut v___x_1048_: *mut LeanObject,
    mut v_____do__lift_1049_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_496__boxed_1050_: u8 = 0;
    let mut v_isSilent_boxed_1051_: u8 = 0;
    let mut v_severity_boxed_1052_: u8 = 0;
    let mut v___x_498__boxed_1053_: u8 = 0;
    let mut v_res_1054_: *mut LeanObject = core::ptr::null_mut();
    v___y_496__boxed_1050_ = (lean_unbox(v___y_1042_) as u8);
    v_isSilent_boxed_1051_ = (lean_unbox(v_isSilent_1043_) as u8);
    v_severity_boxed_1052_ = (lean_unbox(v_severity_1047_) as u8);
    v___x_498__boxed_1053_ = (lean_unbox(v___x_1048_) as u8);
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
    lean_dec_ref(v_____do__lift_1049_);
    return v_res_1054_;
}
pub unsafe fn l_Lean_logAt___redArg(
    mut v_inst_1055_: *mut LeanObject,
    mut v_inst_1056_: *mut LeanObject,
    mut v_inst_1057_: *mut LeanObject,
    mut v_inst_1058_: *mut LeanObject,
    mut v_ref_1059_: *mut LeanObject,
    mut v_msgData_1060_: *mut LeanObject,
    mut v_severity_1061_: u8,
    mut v_isSilent_1062_: u8,
) -> *mut LeanObject {
    let mut v___x_1063_: u8 = 0;
    let mut v___y_1065_: u8 = 0;
    let mut v_toBind_1066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut LeanObject = core::ptr::null_mut();
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
                    lean_inc_ref(v_msgData_1060_);
                    v___x_1078_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1060_);
                    v___y_1065_ = v___x_1078_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_1065_ == 0 {
                    v_toBind_1066_ = lean_ctor_get(v_inst_1055_, 1);
                    lean_inc_n(v_toBind_1066_, 2);
                    lean_dec_ref(v_inst_1055_);
                    v___x_1067_ = lean_box((v___y_1065_) as usize);
                    v___x_1068_ = lean_box((v_isSilent_1062_) as usize);
                    v___x_1069_ = lean_box((v_severity_1061_) as usize);
                    v___x_1070_ = lean_box((v___x_1063_) as usize);
                    v___f_1071_ = lean_alloc_closure(
                        l_Lean_logAt___redArg___lam__4___boxed as *mut core::ffi::c_void,
                        10,
                        9,
                    );
                    lean_closure_set(v___f_1071_, 0, v_inst_1056_);
                    lean_closure_set(v___f_1071_, 1, v_ref_1059_);
                    lean_closure_set(v___f_1071_, 2, v___x_1067_);
                    lean_closure_set(v___f_1071_, 3, v___x_1068_);
                    lean_closure_set(v___f_1071_, 4, v_toBind_1066_);
                    lean_closure_set(v___f_1071_, 5, v_msgData_1060_);
                    lean_closure_set(v___f_1071_, 6, v_inst_1057_);
                    lean_closure_set(v___f_1071_, 7, v___x_1069_);
                    lean_closure_set(v___f_1071_, 8, v___x_1070_);
                    v___x_1072_ = lean_apply_4(
                        v_toBind_1066_,
                        lean_box(0),
                        lean_box(0),
                        v_inst_1058_,
                        v___f_1071_,
                    );
                    return v___x_1072_;
                } else {
                    lean_dec_ref(v_msgData_1060_);
                    lean_dec(v_ref_1059_);
                    lean_dec(v_inst_1058_);
                    lean_dec(v_inst_1057_);
                    lean_dec_ref(v_inst_1056_);
                    v_toApplicative_1073_ = lean_ctor_get(v_inst_1055_, 0);
                    lean_inc_ref(v_toApplicative_1073_);
                    lean_dec_ref(v_inst_1055_);
                    v_toPure_1074_ = lean_ctor_get(v_toApplicative_1073_, 1);
                    lean_inc(v_toPure_1074_);
                    lean_dec_ref(v_toApplicative_1073_);
                    v___x_1075_ = lean_box(0);
                    v___x_1076_ = lean_apply_2(v_toPure_1074_, lean_box(0), v___x_1075_);
                    return v___x_1076_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___redArg___boxed(
    mut v_inst_1079_: *mut LeanObject,
    mut v_inst_1080_: *mut LeanObject,
    mut v_inst_1081_: *mut LeanObject,
    mut v_inst_1082_: *mut LeanObject,
    mut v_ref_1083_: *mut LeanObject,
    mut v_msgData_1084_: *mut LeanObject,
    mut v_severity_1085_: *mut LeanObject,
    mut v_isSilent_1086_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_1087_: u8 = 0;
    let mut v_isSilent_boxed_1088_: u8 = 0;
    let mut v_res_1089_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_1087_ = (lean_unbox(v_severity_1085_) as u8);
    v_isSilent_boxed_1088_ = (lean_unbox(v_isSilent_1086_) as u8);
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
    mut v_m_1090_: *mut LeanObject,
    mut v_inst_1091_: *mut LeanObject,
    mut v_inst_1092_: *mut LeanObject,
    mut v_inst_1093_: *mut LeanObject,
    mut v_inst_1094_: *mut LeanObject,
    mut v_ref_1095_: *mut LeanObject,
    mut v_msgData_1096_: *mut LeanObject,
    mut v_severity_1097_: u8,
    mut v_isSilent_1098_: u8,
) -> *mut LeanObject {
    let mut v___x_1099_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_m_1100_: *mut LeanObject,
    mut v_inst_1101_: *mut LeanObject,
    mut v_inst_1102_: *mut LeanObject,
    mut v_inst_1103_: *mut LeanObject,
    mut v_inst_1104_: *mut LeanObject,
    mut v_ref_1105_: *mut LeanObject,
    mut v_msgData_1106_: *mut LeanObject,
    mut v_severity_1107_: *mut LeanObject,
    mut v_isSilent_1108_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_1109_: u8 = 0;
    let mut v_isSilent_boxed_1110_: u8 = 0;
    let mut v_res_1111_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_1109_ = (lean_unbox(v_severity_1107_) as u8);
    v_isSilent_boxed_1110_ = (lean_unbox(v_isSilent_1108_) as u8);
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
    mut v_inst_1112_: *mut LeanObject,
    mut v_inst_1113_: *mut LeanObject,
    mut v_inst_1114_: *mut LeanObject,
    mut v_inst_1115_: *mut LeanObject,
    mut v_ref_1116_: *mut LeanObject,
    mut v_msgData_1117_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1118_: u8 = 0;
    let mut v___x_1119_: u8 = 0;
    let mut v___x_1120_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_m_1121_: *mut LeanObject,
    mut v_inst_1122_: *mut LeanObject,
    mut v_inst_1123_: *mut LeanObject,
    mut v_inst_1124_: *mut LeanObject,
    mut v_inst_1125_: *mut LeanObject,
    mut v_ref_1126_: *mut LeanObject,
    mut v_msgData_1127_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1128_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_inst_1129_: *mut LeanObject,
    mut v_inst_1130_: *mut LeanObject,
    mut v_inst_1131_: *mut LeanObject,
    mut v_inst_1132_: *mut LeanObject,
    mut v_ref_1133_: *mut LeanObject,
    mut v_name_1134_: *mut LeanObject,
    mut v_msgData_1135_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: u8 = 0;
    let mut v___x_1138_: u8 = 0;
    let mut v___x_1139_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_m_1140_: *mut LeanObject,
    mut v_inst_1141_: *mut LeanObject,
    mut v_inst_1142_: *mut LeanObject,
    mut v_inst_1143_: *mut LeanObject,
    mut v_inst_1144_: *mut LeanObject,
    mut v_ref_1145_: *mut LeanObject,
    mut v_name_1146_: *mut LeanObject,
    mut v_msgData_1147_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1148_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_inst_1149_: *mut LeanObject,
    mut v_inst_1150_: *mut LeanObject,
    mut v_inst_1151_: *mut LeanObject,
    mut v_inst_1152_: *mut LeanObject,
    mut v_ref_1153_: *mut LeanObject,
    mut v_msgData_1154_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1155_: u8 = 0;
    let mut v___x_1156_: u8 = 0;
    let mut v___x_1157_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_m_1158_: *mut LeanObject,
    mut v_inst_1159_: *mut LeanObject,
    mut v_inst_1160_: *mut LeanObject,
    mut v_inst_1161_: *mut LeanObject,
    mut v_inst_1162_: *mut LeanObject,
    mut v_ref_1163_: *mut LeanObject,
    mut v_msgData_1164_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1165_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_inst_1166_: *mut LeanObject,
    mut v_inst_1167_: *mut LeanObject,
    mut v_inst_1168_: *mut LeanObject,
    mut v_inst_1169_: *mut LeanObject,
    mut v_ref_1170_: *mut LeanObject,
    mut v_name_1171_: *mut LeanObject,
    mut v_msgData_1172_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: u8 = 0;
    let mut v___x_1175_: u8 = 0;
    let mut v___x_1176_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_m_1177_: *mut LeanObject,
    mut v_inst_1178_: *mut LeanObject,
    mut v_inst_1179_: *mut LeanObject,
    mut v_inst_1180_: *mut LeanObject,
    mut v_inst_1181_: *mut LeanObject,
    mut v_ref_1182_: *mut LeanObject,
    mut v_name_1183_: *mut LeanObject,
    mut v_msgData_1184_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1185_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_inst_1186_: *mut LeanObject,
    mut v_inst_1187_: *mut LeanObject,
    mut v_inst_1188_: *mut LeanObject,
    mut v_inst_1189_: *mut LeanObject,
    mut v_ref_1190_: *mut LeanObject,
    mut v_msgData_1191_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1192_: u8 = 0;
    let mut v___x_1193_: u8 = 0;
    let mut v___x_1194_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_m_1195_: *mut LeanObject,
    mut v_inst_1196_: *mut LeanObject,
    mut v_inst_1197_: *mut LeanObject,
    mut v_inst_1198_: *mut LeanObject,
    mut v_inst_1199_: *mut LeanObject,
    mut v_ref_1200_: *mut LeanObject,
    mut v_msgData_1201_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1202_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_inst_1203_: *mut LeanObject,
    mut v_inst_1204_: *mut LeanObject,
    mut v_inst_1205_: *mut LeanObject,
    mut v_inst_1206_: *mut LeanObject,
    mut v_msgData_1207_: *mut LeanObject,
    mut v_severity_1208_: u8,
    mut v_isSilent_1209_: u8,
    mut v_ref_1210_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1211_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_inst_1212_: *mut LeanObject,
    mut v_inst_1213_: *mut LeanObject,
    mut v_inst_1214_: *mut LeanObject,
    mut v_inst_1215_: *mut LeanObject,
    mut v_msgData_1216_: *mut LeanObject,
    mut v_severity_1217_: *mut LeanObject,
    mut v_isSilent_1218_: *mut LeanObject,
    mut v_ref_1219_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_1220_: u8 = 0;
    let mut v_isSilent_boxed_1221_: u8 = 0;
    let mut v_res_1222_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_1220_ = (lean_unbox(v_severity_1217_) as u8);
    v_isSilent_boxed_1221_ = (lean_unbox(v_isSilent_1218_) as u8);
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
    mut v_inst_1223_: *mut LeanObject,
    mut v_inst_1224_: *mut LeanObject,
    mut v_inst_1225_: *mut LeanObject,
    mut v_inst_1226_: *mut LeanObject,
    mut v_msgData_1227_: *mut LeanObject,
    mut v_severity_1228_: u8,
    mut v_isSilent_1229_: u8,
) -> *mut LeanObject {
    let mut v_toBind_1230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getRef_1231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_1230_ = lean_ctor_get(v_inst_1223_, 1);
    lean_inc(v_toBind_1230_);
    v_getRef_1231_ = lean_ctor_get(v_inst_1224_, 1);
    lean_inc(v_getRef_1231_);
    v___x_1232_ = lean_box((v_severity_1228_) as usize);
    v___x_1233_ = lean_box((v_isSilent_1229_) as usize);
    v___f_1234_ = lean_alloc_closure(
        l_Lean_log___redArg___lam__0___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    lean_closure_set(v___f_1234_, 0, v_inst_1223_);
    lean_closure_set(v___f_1234_, 1, v_inst_1224_);
    lean_closure_set(v___f_1234_, 2, v_inst_1225_);
    lean_closure_set(v___f_1234_, 3, v_inst_1226_);
    lean_closure_set(v___f_1234_, 4, v_msgData_1227_);
    lean_closure_set(v___f_1234_, 5, v___x_1232_);
    lean_closure_set(v___f_1234_, 6, v___x_1233_);
    v___x_1235_ = lean_apply_4(
        v_toBind_1230_,
        lean_box(0),
        lean_box(0),
        v_getRef_1231_,
        v___f_1234_,
    );
    return v___x_1235_;
}
pub unsafe fn l_Lean_log___redArg___boxed(
    mut v_inst_1236_: *mut LeanObject,
    mut v_inst_1237_: *mut LeanObject,
    mut v_inst_1238_: *mut LeanObject,
    mut v_inst_1239_: *mut LeanObject,
    mut v_msgData_1240_: *mut LeanObject,
    mut v_severity_1241_: *mut LeanObject,
    mut v_isSilent_1242_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_1243_: u8 = 0;
    let mut v_isSilent_boxed_1244_: u8 = 0;
    let mut v_res_1245_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_1243_ = (lean_unbox(v_severity_1241_) as u8);
    v_isSilent_boxed_1244_ = (lean_unbox(v_isSilent_1242_) as u8);
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
    mut v_m_1246_: *mut LeanObject,
    mut v_inst_1247_: *mut LeanObject,
    mut v_inst_1248_: *mut LeanObject,
    mut v_inst_1249_: *mut LeanObject,
    mut v_inst_1250_: *mut LeanObject,
    mut v_msgData_1251_: *mut LeanObject,
    mut v_severity_1252_: u8,
    mut v_isSilent_1253_: u8,
) -> *mut LeanObject {
    let mut v___x_1254_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_m_1255_: *mut LeanObject,
    mut v_inst_1256_: *mut LeanObject,
    mut v_inst_1257_: *mut LeanObject,
    mut v_inst_1258_: *mut LeanObject,
    mut v_inst_1259_: *mut LeanObject,
    mut v_msgData_1260_: *mut LeanObject,
    mut v_severity_1261_: *mut LeanObject,
    mut v_isSilent_1262_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_1263_: u8 = 0;
    let mut v_isSilent_boxed_1264_: u8 = 0;
    let mut v_res_1265_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_1263_ = (lean_unbox(v_severity_1261_) as u8);
    v_isSilent_boxed_1264_ = (lean_unbox(v_isSilent_1262_) as u8);
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
    mut v_inst_1266_: *mut LeanObject,
    mut v_inst_1267_: *mut LeanObject,
    mut v_inst_1268_: *mut LeanObject,
    mut v_inst_1269_: *mut LeanObject,
    mut v_msgData_1270_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1271_: u8 = 0;
    let mut v___x_1272_: u8 = 0;
    let mut v___x_1273_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_m_1274_: *mut LeanObject,
    mut v_inst_1275_: *mut LeanObject,
    mut v_inst_1276_: *mut LeanObject,
    mut v_inst_1277_: *mut LeanObject,
    mut v_inst_1278_: *mut LeanObject,
    mut v_msgData_1279_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1280_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_inst_1281_: *mut LeanObject,
    mut v_inst_1282_: *mut LeanObject,
    mut v_inst_1283_: *mut LeanObject,
    mut v_inst_1284_: *mut LeanObject,
    mut v_name_1285_: *mut LeanObject,
    mut v_msgData_1286_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: u8 = 0;
    let mut v___x_1289_: u8 = 0;
    let mut v___x_1290_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_m_1291_: *mut LeanObject,
    mut v_inst_1292_: *mut LeanObject,
    mut v_inst_1293_: *mut LeanObject,
    mut v_inst_1294_: *mut LeanObject,
    mut v_inst_1295_: *mut LeanObject,
    mut v_name_1296_: *mut LeanObject,
    mut v_msgData_1297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1298_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_inst_1299_: *mut LeanObject,
    mut v_inst_1300_: *mut LeanObject,
    mut v_inst_1301_: *mut LeanObject,
    mut v_inst_1302_: *mut LeanObject,
    mut v_msgData_1303_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1304_: u8 = 0;
    let mut v___x_1305_: u8 = 0;
    let mut v___x_1306_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_m_1307_: *mut LeanObject,
    mut v_inst_1308_: *mut LeanObject,
    mut v_inst_1309_: *mut LeanObject,
    mut v_inst_1310_: *mut LeanObject,
    mut v_inst_1311_: *mut LeanObject,
    mut v_msgData_1312_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1313_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_inst_1314_: *mut LeanObject,
    mut v_inst_1315_: *mut LeanObject,
    mut v_inst_1316_: *mut LeanObject,
    mut v_inst_1317_: *mut LeanObject,
    mut v_name_1318_: *mut LeanObject,
    mut v_msgData_1319_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: u8 = 0;
    let mut v___x_1322_: u8 = 0;
    let mut v___x_1323_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_m_1324_: *mut LeanObject,
    mut v_inst_1325_: *mut LeanObject,
    mut v_inst_1326_: *mut LeanObject,
    mut v_inst_1327_: *mut LeanObject,
    mut v_inst_1328_: *mut LeanObject,
    mut v_name_1329_: *mut LeanObject,
    mut v_msgData_1330_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1331_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_inst_1332_: *mut LeanObject,
    mut v_inst_1333_: *mut LeanObject,
    mut v_inst_1334_: *mut LeanObject,
    mut v_inst_1335_: *mut LeanObject,
    mut v_msgData_1336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1337_: u8 = 0;
    let mut v___x_1338_: u8 = 0;
    let mut v___x_1339_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_m_1340_: *mut LeanObject,
    mut v_inst_1341_: *mut LeanObject,
    mut v_inst_1342_: *mut LeanObject,
    mut v_inst_1343_: *mut LeanObject,
    mut v_inst_1344_: *mut LeanObject,
    mut v_msgData_1345_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1346_: *mut LeanObject = core::ptr::null_mut();
    v___x_1346_ = l_Lean_logInfo___redArg(
        v_inst_1341_,
        v_inst_1342_,
        v_inst_1343_,
        v_inst_1344_,
        v_msgData_1345_,
    );
    return v___x_1346_;
}
pub unsafe fn _init_l_Lean_logUnknownDecl___redArg___closed__1() -> *mut LeanObject {
    let mut v___x_1348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut LeanObject = core::ptr::null_mut();
    v___x_1348_ = l_Lean_logUnknownDecl___redArg___closed__0;
    v___x_1349_ = l_Lean_stringToMessageData(v___x_1348_);
    return v___x_1349_;
}
pub unsafe fn _init_l_Lean_logUnknownDecl___redArg___closed__3() -> *mut LeanObject {
    let mut v___x_1351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut LeanObject = core::ptr::null_mut();
    v___x_1351_ = l_Lean_logUnknownDecl___redArg___closed__2;
    v___x_1352_ = l_Lean_stringToMessageData(v___x_1351_);
    return v___x_1352_;
}
pub unsafe fn l_Lean_logUnknownDecl___redArg(
    mut v_inst_1353_: *mut LeanObject,
    mut v_inst_1354_: *mut LeanObject,
    mut v_inst_1355_: *mut LeanObject,
    mut v_inst_1356_: *mut LeanObject,
    mut v_declName_1357_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut LeanObject = core::ptr::null_mut();
    v___x_1358_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_logUnknownDecl___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_logUnknownDecl___redArg___closed__1_once),
        _init_l_Lean_logUnknownDecl___redArg___closed__1,
    );
    v___x_1359_ = l_Lean_MessageData_ofName(v_declName_1357_);
    v___x_1360_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_1360_, 0, v___x_1358_);
    lean_ctor_set(v___x_1360_, 1, v___x_1359_);
    v___x_1361_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_logUnknownDecl___redArg___closed__3),
        core::ptr::addr_of_mut!(l_Lean_logUnknownDecl___redArg___closed__3_once),
        _init_l_Lean_logUnknownDecl___redArg___closed__3,
    );
    v___x_1362_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_1362_, 0, v___x_1360_);
    lean_ctor_set(v___x_1362_, 1, v___x_1361_);
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
    mut v_m_1364_: *mut LeanObject,
    mut v_inst_1365_: *mut LeanObject,
    mut v_inst_1366_: *mut LeanObject,
    mut v_inst_1367_: *mut LeanObject,
    mut v_inst_1368_: *mut LeanObject,
    mut v_declName_1369_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1370_: *mut LeanObject = core::ptr::null_mut();
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
pub unsafe fn runtime_initialize_Lean_Log(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_ErrorExplanation(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Log_0__Lean_initFn_00___x40_Lean_Log_3265821404____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_warningAsError = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_warningAsError);
    lean_dec_ref(res);
    l_Lean_errorDescriptionWidget = _init_l_Lean_errorDescriptionWidget();
    lean_mark_persistent(l_Lean_errorDescriptionWidget);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Log(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Log(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_ErrorExplanation(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Log(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Log(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Log(builtin);
}
