// Lean compiler output
// Module: Lean.Exception
// Imports: Lean.InternalExceptionId Lean.ErrorExplanation
use crate::ffi::{
    lean_array_get, lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add, lean_nat_dec_eq,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind, l_Lean_Syntax_node1,
    l_Lean_Syntax_node2, l_Lean_Syntax_node3, l_Lean_addMacroScope, l_Lean_maxRecDepthErrorMessage,
    l_Lean_replaceRef, l_String_toRawSubstring_x27,
};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
};
use crate::r#gen::Lean::ErrorExplanation::{
    initialize_Lean_ErrorExplanation, runtime_initialize_Lean_ErrorExplanation,
};
use crate::r#gen::Lean::InternalExceptionId::{
    initialize_Lean_InternalExceptionId, l_Lean_InternalExceptionId_toString,
    l_Lean_instBEqInternalExceptionId_beq, l_Lean_registerInternalExceptionId,
    runtime_initialize_Lean_InternalExceptionId,
};
use crate::r#gen::Lean::Message::{
    l_Lean_Kernel_Exception_toMessageData, l_Lean_MessageData_hasSyntheticSorry,
    l_Lean_MessageData_kind, l_Lean_MessageData_note, l_Lean_MessageData_ofConstName,
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName, l_Lean_MessageData_stripNestedTags,
    l_Lean_MessageData_tagWithErrorName, l_Lean_instInhabitedMessageData_default,
    l_Lean_kindOfErrorName, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
static mut l_Lean_instInhabitedException___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instInhabitedException___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedException: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_unknownIdentifierMessageTag___closed__0_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [108, 101, 97, 110, 0],
    };
static mut l_Lean_unknownIdentifierMessageTag___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_unknownIdentifierMessageTag___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_unknownIdentifierMessageTag___closed__1_value: leanh::LeanStringObject<
    18,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 18,
    m_capacity: 18,
    m_length: 17,
    m_data: [
        117, 110, 107, 110, 111, 119, 110, 73, 100, 101, 110, 116, 105, 102, 105, 101, 114, 0,
    ],
};
static mut l_Lean_unknownIdentifierMessageTag___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_unknownIdentifierMessageTag___closed__1_value)
        as *mut leanh::LeanObject;
static l_Lean_unknownIdentifierMessageTag___closed__2_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_unknownIdentifierMessageTag___closed__0_value)
                as *mut leanh::LeanObject,
            9199928461212983083 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_unknownIdentifierMessageTag___closed__2_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_unknownIdentifierMessageTag___closed__2_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_unknownIdentifierMessageTag___closed__1_value)
                as *mut leanh::LeanObject,
            12904620932282659916 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_unknownIdentifierMessageTag___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_unknownIdentifierMessageTag___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_unknownIdentifierMessageTag___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_unknownIdentifierMessageTag___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_unknownIdentifierMessageTag: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__6_value:
    leanh::LeanStringObject<24> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105,
        111, 110, 32, 96, 0,
    ],
};
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__8_value:
    leanh::LeanStringObject<79> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 79,
    m_capacity: 79,
    m_length: 78,
    m_data: [
        96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116,
        32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116,
        32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112,
        117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101,
        46, 0,
    ],
};
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__8_value)
        as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__9_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__9:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__10_value:
    leanh::LeanStringObject<23> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110,
        32, 96, 0,
    ],
};
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__10_value)
        as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__11_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__11:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__12_value:
    leanh::LeanStringObject<68> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 68,
    m_capacity: 68,
    m_length: 67,
    m_data: [
        96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112,
        111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111,
        110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108,
        105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0,
    ],
};
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__12:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__12_value)
        as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__13_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__13:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__14_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [96, 46, 0],
};
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__14:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__14_value)
        as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__15_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__15:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__16_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0],
};
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__16:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__16_value)
        as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__17_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__17:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__18_value:
    leanh::LeanStringObject<54> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 54,
    m_capacity: 54,
    m_length: 53,
    m_data: [
        96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100,
        32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116,
        111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0,
    ],
};
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__18:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__18_value)
        as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__19_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__19:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___redArg___closed__0_value:
    leanh::LeanStringObject<19> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0,
    ],
};
static mut l_Lean_throwUnknownConstantAt___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___redArg___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_throwUnknownConstantAt___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___redArg___closed__2_value:
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
    m_data: [96, 0],
};
static mut l_Lean_throwUnknownConstantAt___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___redArg___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___redArg___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_throwUnknownConstantAt___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Exception_0__Lean_initFn___closed__0_00___x40_Lean_Exception_2633972168____hygCtx___hyg_2__value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [105, 110, 116, 101, 114, 114, 117, 112, 116, 0]};
static mut l___private_Lean_Exception_0__Lean_initFn___closed__0_00___x40_Lean_Exception_2633972168____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Exception_0__Lean_initFn___closed__0_00___x40_Lean_Exception_2633972168____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Exception_0__Lean_initFn___closed__1_00___x40_Lean_Exception_2633972168____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Exception_0__Lean_initFn___closed__0_00___x40_Lean_Exception_2633972168____hygCtx___hyg_2__value) as *mut leanh::LeanObject,13194118745300296762 as *mut leanh::LeanObject] };
static mut l___private_Lean_Exception_0__Lean_initFn___closed__1_00___x40_Lean_Exception_2633972168____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Exception_0__Lean_initFn___closed__1_00___x40_Lean_Exception_2633972168____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static mut l_Lean_interruptExceptionId: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwInterruptException___redArg___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_throwInterruptException___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_throwMaxRecDepthAt___redArg___closed__0_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [114, 117, 110, 116, 105, 109, 101, 0],
    };
static mut l_Lean_throwMaxRecDepthAt___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_throwMaxRecDepthAt___redArg___closed__1_value: leanh::LeanStringObject<
    12,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 0],
};
static mut l_Lean_throwMaxRecDepthAt___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___redArg___closed__1_value)
        as *mut leanh::LeanObject;
static l_Lean_throwMaxRecDepthAt___redArg___closed__2_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___redArg___closed__0_value)
                as *mut leanh::LeanObject,
            7310567555909517314 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_throwMaxRecDepthAt___redArg___closed__2_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___redArg___closed__2_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___redArg___closed__1_value)
                as *mut leanh::LeanObject,
            273128857561458264 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_throwMaxRecDepthAt___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___redArg___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_throwMaxRecDepthAt___redArg___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_throwMaxRecDepthAt___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___redArg___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_throwMaxRecDepthAt___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___redArg___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_throwMaxRecDepthAt___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_termThrowError_____00__closed__0_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [76, 101, 97, 110, 0],
    };
static mut l_Lean_termThrowError_____00__closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_termThrowError_____00__closed__1_value: leanh::LeanStringObject<17> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 17,
        m_capacity: 17,
        m_length: 16,
        m_data: [
            116, 101, 114, 109, 84, 104, 114, 111, 119, 69, 114, 114, 111, 114, 95, 95, 0,
        ],
    };
static mut l_Lean_termThrowError_____00__closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__1_value)
        as *mut leanh::LeanObject;
static l_Lean_termThrowError_____00__closed__2_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_termThrowError_____00__closed__2_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__2_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__1_value)
                as *mut leanh::LeanObject,
            3344210737276464609 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_termThrowError_____00__closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_termThrowError_____00__closed__3_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [97, 110, 100, 116, 104, 101, 110, 0],
    };
static mut l_Lean_termThrowError_____00__closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_termThrowError_____00__closed__4_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__3_value)
                as *mut leanh::LeanObject,
            12571085391447129896 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_termThrowError_____00__closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_termThrowError_____00__closed__5_value: leanh::LeanStringObject<12> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [116, 104, 114, 111, 119, 69, 114, 114, 111, 114, 32, 0],
    };
static mut l_Lean_termThrowError_____00__closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_termThrowError_____00__closed__6_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_termThrowError_____00__closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_termThrowError_____00__closed__7_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [111, 114, 101, 108, 115, 101, 0],
    };
static mut l_Lean_termThrowError_____00__closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_termThrowError_____00__closed__8_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__7_value)
                as *mut leanh::LeanObject,
            393173242845875278 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_termThrowError_____00__closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_termThrowError_____00__closed__9_value: leanh::LeanStringObject<16> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 16,
        m_capacity: 16,
        m_length: 15,
        m_data: [
            105, 110, 116, 101, 114, 112, 111, 108, 97, 116, 101, 100, 83, 116, 114, 0,
        ],
    };
static mut l_Lean_termThrowError_____00__closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_termThrowError_____00__closed__10_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__9_value)
                as *mut leanh::LeanObject,
            18163029821153688220 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_termThrowError_____00__closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_termThrowError_____00__closed__11_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [116, 101, 114, 109, 0],
    };
static mut l_Lean_termThrowError_____00__closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lean_termThrowError_____00__closed__12_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__11_value)
                as *mut leanh::LeanObject,
            8609355255726335675 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_termThrowError_____00__closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Lean_termThrowError_____00__closed__13_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 7,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__12_value)
                as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_termThrowError_____00__closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Lean_termThrowError_____00__closed__14_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__10_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__13_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_termThrowError_____00__closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Lean_termThrowError_____00__closed__15_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__8_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__14_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__13_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_termThrowError_____00__closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Lean_termThrowError_____00__closed__16_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__6_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__15_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_termThrowError_____00__closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Lean_termThrowError_____00__closed__17_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__2_value)
                as *mut leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__16_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_termThrowError_____00__closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__17_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_termThrowError____: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__17_value)
        as *mut leanh::LeanObject;
pub static l_Lean_termThrowErrorAt_________00__closed__0_value: leanh::LeanStringObject<21> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            116, 101, 114, 109, 84, 104, 114, 111, 119, 69, 114, 114, 111, 114, 65, 116, 95, 95,
            95, 95, 0,
        ],
    };
static mut l_Lean_termThrowErrorAt_________00__closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowErrorAt_________00__closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_termThrowErrorAt_________00__closed__1_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_termThrowErrorAt_________00__closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_termThrowErrorAt_________00__closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_termThrowErrorAt_________00__closed__0_value)
                as *mut leanh::LeanObject,
            4940719421648177115 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_termThrowErrorAt_________00__closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowErrorAt_________00__closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_termThrowErrorAt_________00__closed__2_value: leanh::LeanStringObject<14> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [
            116, 104, 114, 111, 119, 69, 114, 114, 111, 114, 65, 116, 32, 0,
        ],
    };
static mut l_Lean_termThrowErrorAt_________00__closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowErrorAt_________00__closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_termThrowErrorAt_________00__closed__3_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_termThrowErrorAt_________00__closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_termThrowErrorAt_________00__closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowErrorAt_________00__closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_termThrowErrorAt_________00__closed__4_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 7,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__12_value)
                as *mut leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_termThrowErrorAt_________00__closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowErrorAt_________00__closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_termThrowErrorAt_________00__closed__5_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_termThrowErrorAt_________00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_termThrowErrorAt_________00__closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_termThrowErrorAt_________00__closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowErrorAt_________00__closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_termThrowErrorAt_________00__closed__6_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [112, 112, 83, 112, 97, 99, 101, 0],
    };
static mut l_Lean_termThrowErrorAt_________00__closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowErrorAt_________00__closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_termThrowErrorAt_________00__closed__7_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_termThrowErrorAt_________00__closed__6_value)
                as *mut leanh::LeanObject,
            17761616517784022991 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_termThrowErrorAt_________00__closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowErrorAt_________00__closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_termThrowErrorAt_________00__closed__8_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_termThrowErrorAt_________00__closed__7_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_termThrowErrorAt_________00__closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowErrorAt_________00__closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_termThrowErrorAt_________00__closed__9_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_termThrowErrorAt_________00__closed__5_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_termThrowErrorAt_________00__closed__8_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_termThrowErrorAt_________00__closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowErrorAt_________00__closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_termThrowErrorAt_________00__closed__10_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_termThrowErrorAt_________00__closed__9_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__15_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_termThrowErrorAt_________00__closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowErrorAt_________00__closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_termThrowErrorAt_________00__closed__11_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_termThrowErrorAt_________00__closed__1_value)
                as *mut leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_termThrowErrorAt_________00__closed__10_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_termThrowErrorAt_________00__closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowErrorAt_________00__closed__11_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_termThrowErrorAt________: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowErrorAt_________00__closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__0_value: leanh::LeanStringObject<20> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 116, 101, 114, 112, 111, 108, 97, 116, 101, 100, 83, 116, 114, 75, 105, 110, 100, 0]};
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__0_value) as *mut leanh::LeanObject,14298422259736409839 as *mut leanh::LeanObject] };
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__2_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__3_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__4_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__4_value) as *mut leanh::LeanObject;
static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__2_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__3_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__4_value) as *mut leanh::LeanObject,12966880221525079621 as *mut leanh::LeanObject] };
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__6_value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [76, 101, 97, 110, 46, 116, 104, 114, 111, 119, 69, 114, 114, 111, 114, 0]};
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__6_value) as *mut leanh::LeanObject;
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__8_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [116, 104, 114, 111, 119, 69, 114, 114, 111, 114, 0]};
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__8_value) as *mut leanh::LeanObject;
static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__9_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__9_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__9_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__8_value) as *mut leanh::LeanObject,5078008955686056653 as *mut leanh::LeanObject] };
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__9_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__10_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__9_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__10_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__11_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__10_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__11_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__12_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__12_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__13_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__12_value) as *mut leanh::LeanObject,9855511589286918680 as *mut leanh::LeanObject] };
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__13_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__14_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [112, 97, 114, 101, 110, 0]};
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__14_value) as *mut leanh::LeanObject;
static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__15_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__15_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__15_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__2_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__15_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__15_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__3_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__15_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__15_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__14_value) as *mut leanh::LeanObject,7932075773091973500 as *mut leanh::LeanObject] };
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__15_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__16_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0]};
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__16_value) as *mut leanh::LeanObject;
static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__17_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__17_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__17_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__2_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__17_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__17_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__3_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__17_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__17_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__16_value) as *mut leanh::LeanObject,7306243862518720553 as *mut leanh::LeanObject] };
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__17: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__17_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__18_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__18_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__19_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0]};
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__19: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__19_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__20_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__19_value) as *mut leanh::LeanObject,9871775667037945883 as *mut leanh::LeanObject] };
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__20: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__20_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__21_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__21: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__21_value) as *mut leanh::LeanObject;
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__22_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__22: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__23_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__23: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__23_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__24_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__23_value) as *mut leanh::LeanObject] };
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__24: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__24_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__25_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__24_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__25: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__25_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__26_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [116, 101, 114, 109, 77, 33, 95, 0]};
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__26: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__26_value) as *mut leanh::LeanObject;
static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__27_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__27_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__27_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__26_value) as *mut leanh::LeanObject,13317951319906582257 as *mut leanh::LeanObject] };
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__27: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__27_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__28_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [109, 33, 0]};
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__28: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__28_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__29_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__29: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__29_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__0_value: leanh::LeanStringObject<18> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [76, 101, 97, 110, 46, 116, 104, 114, 111, 119, 69, 114, 114, 111, 114, 65, 116, 0]};
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__2_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [116, 104, 114, 111, 119, 69, 114, 114, 111, 114, 65, 116, 0]};
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__2_value) as *mut leanh::LeanObject;
static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__2_value) as *mut leanh::LeanObject,5209814932049838757 as *mut leanh::LeanObject] };
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__4_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__3_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__5_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__4_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__5_value) as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Exception_ctorIdx(
    mut v_x_1130_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1130_) == 0 {
        let mut v___x_1131_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1131_ = leanh::lean_unsigned_to_nat(0);
        return v___x_1131_;
    } else {
        let mut v___x_1132_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1132_ = leanh::lean_unsigned_to_nat(1);
        return v___x_1132_;
    }
}
pub unsafe fn l_Lean_Exception_ctorIdx___boxed(
    mut v_x_1133_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1134_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1134_ = l_Lean_Exception_ctorIdx(v_x_1133_);
    leanh::lean_dec_ref(v_x_1133_);
    return v_res_1134_;
}
pub unsafe fn l_Lean_Exception_ctorElim___redArg(
    mut v_t_1135_: *mut leanh::LeanObject,
    mut v_k_1136_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_1135_) == 0 {
        let mut v_ref_1137_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_msg_1138_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1139_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_ref_1137_ = leanh::lean_ctor_get(v_t_1135_, 0);
        leanh::lean_inc(v_ref_1137_);
        v_msg_1138_ = leanh::lean_ctor_get(v_t_1135_, 1);
        leanh::lean_inc_ref(v_msg_1138_);
        leanh::lean_dec_ref_known(v_t_1135_, 2);
        v___x_1139_ = leanh::lean_apply_2(v_k_1136_, v_ref_1137_, v_msg_1138_);
        return v___x_1139_;
    } else {
        let mut v_id_1140_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_extra_1141_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1142_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_id_1140_ = leanh::lean_ctor_get(v_t_1135_, 0);
        leanh::lean_inc(v_id_1140_);
        v_extra_1141_ = leanh::lean_ctor_get(v_t_1135_, 1);
        leanh::lean_inc(v_extra_1141_);
        leanh::lean_dec_ref_known(v_t_1135_, 2);
        v___x_1142_ = leanh::lean_apply_2(v_k_1136_, v_id_1140_, v_extra_1141_);
        return v___x_1142_;
    }
}
pub unsafe fn l_Lean_Exception_ctorElim(
    mut v_motive_1143_: *mut leanh::LeanObject,
    mut v_ctorIdx_1144_: *mut leanh::LeanObject,
    mut v_t_1145_: *mut leanh::LeanObject,
    mut v_h_1146_: *mut leanh::LeanObject,
    mut v_k_1147_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1148_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1148_ = l_Lean_Exception_ctorElim___redArg(v_t_1145_, v_k_1147_);
    return v___x_1148_;
}
pub unsafe fn l_Lean_Exception_ctorElim___boxed(
    mut v_motive_1149_: *mut leanh::LeanObject,
    mut v_ctorIdx_1150_: *mut leanh::LeanObject,
    mut v_t_1151_: *mut leanh::LeanObject,
    mut v_h_1152_: *mut leanh::LeanObject,
    mut v_k_1153_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1154_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1154_ = l_Lean_Exception_ctorElim(
        v_motive_1149_,
        v_ctorIdx_1150_,
        v_t_1151_,
        v_h_1152_,
        v_k_1153_,
    );
    leanh::lean_dec(v_ctorIdx_1150_);
    return v_res_1154_;
}
pub unsafe fn l_Lean_Exception_error_elim___redArg(
    mut v_t_1155_: *mut leanh::LeanObject,
    mut v_error_1156_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1157_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1157_ = l_Lean_Exception_ctorElim___redArg(v_t_1155_, v_error_1156_);
    return v___x_1157_;
}
pub unsafe fn l_Lean_Exception_error_elim(
    mut v_motive_1158_: *mut leanh::LeanObject,
    mut v_t_1159_: *mut leanh::LeanObject,
    mut v_h_1160_: *mut leanh::LeanObject,
    mut v_error_1161_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1162_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1162_ = l_Lean_Exception_ctorElim___redArg(v_t_1159_, v_error_1161_);
    return v___x_1162_;
}
pub unsafe fn l_Lean_Exception_internal_elim___redArg(
    mut v_t_1163_: *mut leanh::LeanObject,
    mut v_internal_1164_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1165_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1165_ = l_Lean_Exception_ctorElim___redArg(v_t_1163_, v_internal_1164_);
    return v___x_1165_;
}
pub unsafe fn l_Lean_Exception_internal_elim(
    mut v_motive_1166_: *mut leanh::LeanObject,
    mut v_t_1167_: *mut leanh::LeanObject,
    mut v_h_1168_: *mut leanh::LeanObject,
    mut v_internal_1169_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1170_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1170_ = l_Lean_Exception_ctorElim___redArg(v_t_1167_, v_internal_1169_);
    return v___x_1170_;
}
pub unsafe fn l_Lean_Exception_toMessageData(
    mut v_x_1171_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1171_) == 0 {
        let mut v_msg_1172_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_msg_1172_ = leanh::lean_ctor_get(v_x_1171_, 1);
        leanh::lean_inc_ref(v_msg_1172_);
        leanh::lean_dec_ref_known(v_x_1171_, 2);
        return v_msg_1172_;
    } else {
        let mut v_id_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1175_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1176_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_id_1173_ = leanh::lean_ctor_get(v_x_1171_, 0);
        leanh::lean_inc(v_id_1173_);
        leanh::lean_dec_ref_known(v_x_1171_, 2);
        v___x_1174_ = l_Lean_InternalExceptionId_toString(v_id_1173_);
        v___x_1175_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1175_, 0, v___x_1174_);
        v___x_1176_ = l_Lean_MessageData_ofFormat(v___x_1175_);
        return v___x_1176_;
    }
}
pub unsafe fn l_Lean_Exception_hasSyntheticSorry(
    mut v_x_1177_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_1177_) == 0 {
        let mut v_msg_1178_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1179_: u8 = 0;
        v_msg_1178_ = leanh::lean_ctor_get(v_x_1177_, 1);
        leanh::lean_inc_ref(v_msg_1178_);
        leanh::lean_dec_ref_known(v_x_1177_, 2);
        v___x_1179_ = l_Lean_MessageData_hasSyntheticSorry(v_msg_1178_);
        return v___x_1179_;
    } else {
        let mut v___x_1180_: u8 = 0;
        leanh::lean_dec_ref(v_x_1177_);
        v___x_1180_ = 0;
        return v___x_1180_;
    }
}
pub unsafe fn l_Lean_Exception_hasSyntheticSorry___boxed(
    mut v_x_1181_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1182_: u8 = 0;
    let mut v_r_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1182_ = l_Lean_Exception_hasSyntheticSorry(v_x_1181_);
    v_r_1183_ = leanh::lean_box((v_res_1182_) as usize);
    return v_r_1183_;
}
pub unsafe fn l_Lean_Exception_getRef(
    mut v_x_1184_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1184_) == 0 {
        let mut v_ref_1185_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_ref_1185_ = leanh::lean_ctor_get(v_x_1184_, 0);
        leanh::lean_inc(v_ref_1185_);
        return v_ref_1185_;
    } else {
        let mut v___x_1186_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1186_ = leanh::lean_box(0);
        return v___x_1186_;
    }
}
pub unsafe fn l_Lean_Exception_getRef___boxed(
    mut v_x_1187_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1188_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1188_ = l_Lean_Exception_getRef(v_x_1187_);
    leanh::lean_dec_ref(v_x_1187_);
    return v_res_1188_;
}
pub unsafe fn _init_l_Lean_instInhabitedException___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1191_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1189_ = l_Lean_instInhabitedMessageData_default;
    v___x_1190_ = leanh::lean_box(0);
    v___x_1191_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1191_, 0, v___x_1190_);
    leanh::lean_ctor_set(v___x_1191_, 1, v___x_1189_);
    return v___x_1191_;
}
pub unsafe fn _init_l_Lean_instInhabitedException() -> *mut leanh::LeanObject {
    let mut v___x_1192_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1192_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedException___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedException___closed__0_once),
        _init_l_Lean_instInhabitedException___closed__0,
    );
    return v___x_1192_;
}
pub unsafe fn l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg___lam__0(
    mut v_ref_1193_: *mut leanh::LeanObject,
    mut v_toPure_1194_: *mut leanh::LeanObject,
    mut v_msg_1195_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1196_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1196_, 0, v_ref_1193_);
    leanh::lean_ctor_set(v___x_1196_, 1, v_msg_1195_);
    v___x_1197_ =
        leanh::lean_apply_2(v_toPure_1194_, leanh::lean_box(0), v___x_1196_);
    return v___x_1197_;
}
pub unsafe fn l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg___lam__1(
    mut v_toPure_1198_: *mut leanh::LeanObject,
    mut v_inst_1199_: *mut leanh::LeanObject,
    mut v_toBind_1200_: *mut leanh::LeanObject,
    mut v_ref_1201_: *mut leanh::LeanObject,
    mut v_msg_1202_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1203_ = leanh::lean_alloc_closure(
        l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1203_, 0, v_ref_1201_);
    leanh::lean_closure_set(v___f_1203_, 1, v_toPure_1198_);
    v___x_1204_ = leanh::lean_apply_1(v_inst_1199_, v_msg_1202_);
    v___x_1205_ = leanh::lean_apply_4(
        v_toBind_1200_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1204_,
        v___f_1203_,
    );
    return v___x_1205_;
}
pub unsafe fn l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(
    mut v_inst_1206_: *mut leanh::LeanObject,
    mut v_inst_1207_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1208_ = leanh::lean_ctor_get(v_inst_1207_, 0);
    leanh::lean_inc_ref(v_toApplicative_1208_);
    v_toBind_1209_ = leanh::lean_ctor_get(v_inst_1207_, 1);
    leanh::lean_inc(v_toBind_1209_);
    leanh::lean_dec_ref(v_inst_1207_);
    v_toPure_1210_ = leanh::lean_ctor_get(v_toApplicative_1208_, 1);
    leanh::lean_inc(v_toPure_1210_);
    leanh::lean_dec_ref(v_toApplicative_1208_);
    v___f_1211_ = leanh::lean_alloc_closure(
        l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg___lam__1
            as *mut core::ffi::c_void,
        5,
        3,
    );
    leanh::lean_closure_set(v___f_1211_, 0, v_toPure_1210_);
    leanh::lean_closure_set(v___f_1211_, 1, v_inst_1206_);
    leanh::lean_closure_set(v___f_1211_, 2, v_toBind_1209_);
    return v___f_1211_;
}
pub unsafe fn l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad(
    mut v_m_1212_: *mut leanh::LeanObject,
    mut v_inst_1213_: *mut leanh::LeanObject,
    mut v_inst_1214_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1215_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1215_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(
        v_inst_1213_,
        v_inst_1214_,
    );
    return v___x_1215_;
}
pub unsafe fn l_Lean_throwError___redArg___lam__0(
    mut v_toMonadExceptOf_1216_: *mut leanh::LeanObject,
    mut v_____x_1217_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_throw_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1223_: u8 = 0;
    let mut v___x_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1228_: u8 = 0;
    let mut v_unused_1229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1218_ = leanh::lean_ctor_get(v_____x_1217_, 0);
                v_snd_1219_ = leanh::lean_ctor_get(v_____x_1217_, 1);
                v_throw_1220_ = leanh::lean_ctor_get(v_toMonadExceptOf_1216_, 0);
                v_isSharedCheck_1228_ =
                    (!leanh::lean_is_exclusive(v_toMonadExceptOf_1216_)) as u8;
                if v_isSharedCheck_1228_ == 0 {
                    v_unused_1229_ = leanh::lean_ctor_get(v_toMonadExceptOf_1216_, 1);
                    leanh::lean_dec(v_unused_1229_);
                    v___x_1222_ = v_toMonadExceptOf_1216_;
                    v_isShared_1223_ = v_isSharedCheck_1228_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_throw_1220_);
                    leanh::lean_dec(v_toMonadExceptOf_1216_);
                    v___x_1222_ = leanh::lean_box(0);
                    v_isShared_1223_ = v_isSharedCheck_1228_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_snd_1219_);
                leanh::lean_inc(v_fst_1218_);
                if v_isShared_1223_ == 0 {
                    leanh::lean_ctor_set(v___x_1222_, 1, v_snd_1219_);
                    leanh::lean_ctor_set(v___x_1222_, 0, v_fst_1218_);
                    v___x_1225_ = v___x_1222_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1227_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_fst_1218_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1227_, 1, v_snd_1219_);
                    v___x_1225_ = v_reuseFailAlloc_1227_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1226_ = leanh::lean_apply_2(
                    v_throw_1220_,
                    leanh::lean_box(0),
                    v___x_1225_,
                );
                return v___x_1226_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___redArg___lam__0___boxed(
    mut v_toMonadExceptOf_1230_: *mut leanh::LeanObject,
    mut v_____x_1231_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1232_ = l_Lean_throwError___redArg___lam__0(v_toMonadExceptOf_1230_, v_____x_1231_);
    leanh::lean_dec_ref(v_____x_1231_);
    return v_res_1232_;
}
pub unsafe fn l_Lean_throwError___redArg___lam__1(
    mut v_toAddErrorMessageContext_1233_: *mut leanh::LeanObject,
    mut v_msg_1234_: *mut leanh::LeanObject,
    mut v_toBind_1235_: *mut leanh::LeanObject,
    mut v___f_1236_: *mut leanh::LeanObject,
    mut v_ref_1237_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1238_ =
        leanh::lean_apply_2(v_toAddErrorMessageContext_1233_, v_ref_1237_, v_msg_1234_);
    v___x_1239_ = leanh::lean_apply_4(
        v_toBind_1235_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1238_,
        v___f_1236_,
    );
    return v___x_1239_;
}
pub unsafe fn l_Lean_throwError___redArg(
    mut v_inst_1240_: *mut leanh::LeanObject,
    mut v_inst_1241_: *mut leanh::LeanObject,
    mut v_msg_1242_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toMonadRef_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toMonadExceptOf_1245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toAddErrorMessageContext_1246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRef_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toMonadRef_1243_ = leanh::lean_ctor_get(v_inst_1241_, 1);
    leanh::lean_inc_ref(v_toMonadRef_1243_);
    v_toBind_1244_ = leanh::lean_ctor_get(v_inst_1240_, 1);
    leanh::lean_inc_n(v_toBind_1244_, 2);
    leanh::lean_dec_ref(v_inst_1240_);
    v_toMonadExceptOf_1245_ = leanh::lean_ctor_get(v_inst_1241_, 0);
    leanh::lean_inc_ref(v_toMonadExceptOf_1245_);
    v_toAddErrorMessageContext_1246_ = leanh::lean_ctor_get(v_inst_1241_, 2);
    leanh::lean_inc(v_toAddErrorMessageContext_1246_);
    leanh::lean_dec_ref(v_inst_1241_);
    v_getRef_1247_ = leanh::lean_ctor_get(v_toMonadRef_1243_, 0);
    leanh::lean_inc(v_getRef_1247_);
    leanh::lean_dec_ref(v_toMonadRef_1243_);
    v___f_1248_ = leanh::lean_alloc_closure(
        l_Lean_throwError___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1248_, 0, v_toMonadExceptOf_1245_);
    v___f_1249_ = leanh::lean_alloc_closure(
        l_Lean_throwError___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_1249_, 0, v_toAddErrorMessageContext_1246_);
    leanh::lean_closure_set(v___f_1249_, 1, v_msg_1242_);
    leanh::lean_closure_set(v___f_1249_, 2, v_toBind_1244_);
    leanh::lean_closure_set(v___f_1249_, 3, v___f_1248_);
    v___x_1250_ = leanh::lean_apply_4(
        v_toBind_1244_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getRef_1247_,
        v___f_1249_,
    );
    return v___x_1250_;
}
pub unsafe fn l_Lean_throwError(
    mut v_m_1251_: *mut leanh::LeanObject,
    mut v_00_u03b1_1252_: *mut leanh::LeanObject,
    mut v_inst_1253_: *mut leanh::LeanObject,
    mut v_inst_1254_: *mut leanh::LeanObject,
    mut v_msg_1255_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1256_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1256_ = l_Lean_throwError___redArg(v_inst_1253_, v_inst_1254_, v_msg_1255_);
    return v___x_1256_;
}
pub unsafe fn _init_l_Lean_unknownIdentifierMessageTag___closed__3() -> *mut leanh::LeanObject
{
    let mut v___x_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1262_ = l_Lean_unknownIdentifierMessageTag___closed__2;
    v___x_1263_ = l_Lean_kindOfErrorName(v___x_1262_);
    return v___x_1263_;
}
pub unsafe fn _init_l_Lean_unknownIdentifierMessageTag() -> *mut leanh::LeanObject {
    let mut v___x_1264_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1264_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_unknownIdentifierMessageTag___closed__3),
        core::ptr::addr_of_mut!(l_Lean_unknownIdentifierMessageTag___closed__3_once),
        _init_l_Lean_unknownIdentifierMessageTag___closed__3,
    );
    return v___x_1264_;
}
pub unsafe fn l_Lean_throwErrorAt___redArg___lam__0(
    mut v_ref_1265_: *mut leanh::LeanObject,
    mut v_withRef_1266_: *mut leanh::LeanObject,
    mut v___x_1267_: *mut leanh::LeanObject,
    mut v_oldRef_1268_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_1269_ = l_Lean_replaceRef(v_ref_1265_, v_oldRef_1268_);
    v___x_1270_ = leanh::lean_apply_3(
        v_withRef_1266_,
        leanh::lean_box(0),
        v_ref_1269_,
        v___x_1267_,
    );
    return v___x_1270_;
}
pub unsafe fn l_Lean_throwErrorAt___redArg___lam__0___boxed(
    mut v_ref_1271_: *mut leanh::LeanObject,
    mut v_withRef_1272_: *mut leanh::LeanObject,
    mut v___x_1273_: *mut leanh::LeanObject,
    mut v_oldRef_1274_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1275_ = l_Lean_throwErrorAt___redArg___lam__0(
        v_ref_1271_,
        v_withRef_1272_,
        v___x_1273_,
        v_oldRef_1274_,
    );
    leanh::lean_dec(v_oldRef_1274_);
    leanh::lean_dec(v_ref_1271_);
    return v_res_1275_;
}
pub unsafe fn l_Lean_throwErrorAt___redArg(
    mut v_inst_1276_: *mut leanh::LeanObject,
    mut v_inst_1277_: *mut leanh::LeanObject,
    mut v_ref_1278_: *mut leanh::LeanObject,
    mut v_msg_1279_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toMonadRef_1280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRef_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_withRef_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toMonadRef_1280_ = leanh::lean_ctor_get(v_inst_1277_, 1);
    v_toBind_1281_ = leanh::lean_ctor_get(v_inst_1276_, 1);
    leanh::lean_inc(v_toBind_1281_);
    v_getRef_1282_ = leanh::lean_ctor_get(v_toMonadRef_1280_, 0);
    leanh::lean_inc(v_getRef_1282_);
    v_withRef_1283_ = leanh::lean_ctor_get(v_toMonadRef_1280_, 1);
    leanh::lean_inc(v_withRef_1283_);
    v___x_1284_ = l_Lean_throwError___redArg(v_inst_1276_, v_inst_1277_, v_msg_1279_);
    v___f_1285_ = leanh::lean_alloc_closure(
        l_Lean_throwErrorAt___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_1285_, 0, v_ref_1278_);
    leanh::lean_closure_set(v___f_1285_, 1, v_withRef_1283_);
    leanh::lean_closure_set(v___f_1285_, 2, v___x_1284_);
    v___x_1286_ = leanh::lean_apply_4(
        v_toBind_1281_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getRef_1282_,
        v___f_1285_,
    );
    return v___x_1286_;
}
pub unsafe fn l_Lean_throwErrorAt(
    mut v_m_1287_: *mut leanh::LeanObject,
    mut v_00_u03b1_1288_: *mut leanh::LeanObject,
    mut v_inst_1289_: *mut leanh::LeanObject,
    mut v_inst_1290_: *mut leanh::LeanObject,
    mut v_ref_1291_: *mut leanh::LeanObject,
    mut v_msg_1292_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1293_ =
        l_Lean_throwErrorAt___redArg(v_inst_1289_, v_inst_1290_, v_ref_1291_, v_msg_1292_);
    return v___x_1293_;
}
pub unsafe fn l_Lean_throwNamedError___redArg___lam__1(
    mut v_msg_1294_: *mut leanh::LeanObject,
    mut v_name_1295_: *mut leanh::LeanObject,
    mut v_toAddErrorMessageContext_1296_: *mut leanh::LeanObject,
    mut v_toBind_1297_: *mut leanh::LeanObject,
    mut v___f_1298_: *mut leanh::LeanObject,
    mut v_ref_1299_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_msg_1300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_msg_1300_ = l_Lean_MessageData_tagWithErrorName(v_msg_1294_, v_name_1295_);
    v___x_1301_ =
        leanh::lean_apply_2(v_toAddErrorMessageContext_1296_, v_ref_1299_, v_msg_1300_);
    v___x_1302_ = leanh::lean_apply_4(
        v_toBind_1297_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1301_,
        v___f_1298_,
    );
    return v___x_1302_;
}
pub unsafe fn l_Lean_throwNamedError___redArg(
    mut v_inst_1303_: *mut leanh::LeanObject,
    mut v_inst_1304_: *mut leanh::LeanObject,
    mut v_name_1305_: *mut leanh::LeanObject,
    mut v_msg_1306_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toMonadRef_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toMonadExceptOf_1309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toAddErrorMessageContext_1310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRef_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toMonadRef_1307_ = leanh::lean_ctor_get(v_inst_1304_, 1);
    leanh::lean_inc_ref(v_toMonadRef_1307_);
    v_toBind_1308_ = leanh::lean_ctor_get(v_inst_1303_, 1);
    leanh::lean_inc_n(v_toBind_1308_, 2);
    leanh::lean_dec_ref(v_inst_1303_);
    v_toMonadExceptOf_1309_ = leanh::lean_ctor_get(v_inst_1304_, 0);
    leanh::lean_inc_ref(v_toMonadExceptOf_1309_);
    v_toAddErrorMessageContext_1310_ = leanh::lean_ctor_get(v_inst_1304_, 2);
    leanh::lean_inc(v_toAddErrorMessageContext_1310_);
    leanh::lean_dec_ref(v_inst_1304_);
    v_getRef_1311_ = leanh::lean_ctor_get(v_toMonadRef_1307_, 0);
    leanh::lean_inc(v_getRef_1311_);
    leanh::lean_dec_ref(v_toMonadRef_1307_);
    v___f_1312_ = leanh::lean_alloc_closure(
        l_Lean_throwError___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1312_, 0, v_toMonadExceptOf_1309_);
    v___f_1313_ = leanh::lean_alloc_closure(
        l_Lean_throwNamedError___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___f_1313_, 0, v_msg_1306_);
    leanh::lean_closure_set(v___f_1313_, 1, v_name_1305_);
    leanh::lean_closure_set(v___f_1313_, 2, v_toAddErrorMessageContext_1310_);
    leanh::lean_closure_set(v___f_1313_, 3, v_toBind_1308_);
    leanh::lean_closure_set(v___f_1313_, 4, v___f_1312_);
    v___x_1314_ = leanh::lean_apply_4(
        v_toBind_1308_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getRef_1311_,
        v___f_1313_,
    );
    return v___x_1314_;
}
pub unsafe fn l_Lean_throwNamedError(
    mut v_m_1315_: *mut leanh::LeanObject,
    mut v_00_u03b1_1316_: *mut leanh::LeanObject,
    mut v_inst_1317_: *mut leanh::LeanObject,
    mut v_inst_1318_: *mut leanh::LeanObject,
    mut v_name_1319_: *mut leanh::LeanObject,
    mut v_msg_1320_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1321_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1321_ =
        l_Lean_throwNamedError___redArg(v_inst_1317_, v_inst_1318_, v_name_1319_, v_msg_1320_);
    return v___x_1321_;
}
pub unsafe fn l_Lean_throwNamedErrorAt___redArg(
    mut v_inst_1322_: *mut leanh::LeanObject,
    mut v_inst_1323_: *mut leanh::LeanObject,
    mut v_ref_1324_: *mut leanh::LeanObject,
    mut v_name_1325_: *mut leanh::LeanObject,
    mut v_msg_1326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toMonadRef_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRef_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_withRef_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toMonadRef_1327_ = leanh::lean_ctor_get(v_inst_1323_, 1);
    v_toBind_1328_ = leanh::lean_ctor_get(v_inst_1322_, 1);
    leanh::lean_inc(v_toBind_1328_);
    v_getRef_1329_ = leanh::lean_ctor_get(v_toMonadRef_1327_, 0);
    leanh::lean_inc(v_getRef_1329_);
    v_withRef_1330_ = leanh::lean_ctor_get(v_toMonadRef_1327_, 1);
    leanh::lean_inc(v_withRef_1330_);
    v___x_1331_ =
        l_Lean_throwNamedError___redArg(v_inst_1322_, v_inst_1323_, v_name_1325_, v_msg_1326_);
    v___f_1332_ = leanh::lean_alloc_closure(
        l_Lean_throwErrorAt___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_1332_, 0, v_ref_1324_);
    leanh::lean_closure_set(v___f_1332_, 1, v_withRef_1330_);
    leanh::lean_closure_set(v___f_1332_, 2, v___x_1331_);
    v___x_1333_ = leanh::lean_apply_4(
        v_toBind_1328_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getRef_1329_,
        v___f_1332_,
    );
    return v___x_1333_;
}
pub unsafe fn l_Lean_throwNamedErrorAt(
    mut v_m_1334_: *mut leanh::LeanObject,
    mut v_00_u03b1_1335_: *mut leanh::LeanObject,
    mut v_inst_1336_: *mut leanh::LeanObject,
    mut v_inst_1337_: *mut leanh::LeanObject,
    mut v_ref_1338_: *mut leanh::LeanObject,
    mut v_name_1339_: *mut leanh::LeanObject,
    mut v_msg_1340_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1341_ = l_Lean_throwNamedErrorAt___redArg(
        v_inst_1336_,
        v_inst_1337_,
        v_ref_1338_,
        v_name_1339_,
        v_msg_1340_,
    );
    return v___x_1341_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1342_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1342_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1343_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__0_once
        ),
        _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__0,
    );
    v___x_1344_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1344_, 0, v___x_1343_);
    return v___x_1344_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1345_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__1_once
        ),
        _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__1,
    );
    v___x_1346_ = leanh::lean_unsigned_to_nat(0);
    v___x_1347_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_1347_, 0, v___x_1346_);
    leanh::lean_ctor_set(v___x_1347_, 1, v___x_1346_);
    leanh::lean_ctor_set(v___x_1347_, 2, v___x_1346_);
    leanh::lean_ctor_set(v___x_1347_, 3, v___x_1346_);
    leanh::lean_ctor_set(v___x_1347_, 4, v___x_1345_);
    leanh::lean_ctor_set(v___x_1347_, 5, v___x_1345_);
    leanh::lean_ctor_set(v___x_1347_, 6, v___x_1345_);
    leanh::lean_ctor_set(v___x_1347_, 7, v___x_1345_);
    leanh::lean_ctor_set(v___x_1347_, 8, v___x_1345_);
    leanh::lean_ctor_set(v___x_1347_, 9, v___x_1345_);
    return v___x_1347_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1348_ = leanh::lean_unsigned_to_nat(32);
    v___x_1349_ = lean_mk_empty_array_with_capacity(v___x_1348_);
    v___x_1350_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1350_, 0, v___x_1349_);
    return v___x_1350_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1351_: usize = 0;
    let mut v___x_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1351_ = 5usize;
    v___x_1352_ = leanh::lean_unsigned_to_nat(0);
    v___x_1353_ = leanh::lean_unsigned_to_nat(32);
    v___x_1354_ = lean_mk_empty_array_with_capacity(v___x_1353_);
    v___x_1355_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__3_once
        ),
        _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__3,
    );
    v___x_1356_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_1356_, 0, v___x_1355_);
    leanh::lean_ctor_set(v___x_1356_, 1, v___x_1354_);
    leanh::lean_ctor_set(v___x_1356_, 2, v___x_1352_);
    leanh::lean_ctor_set(v___x_1356_, 3, v___x_1352_);
    leanh::lean_ctor_set_usize(v___x_1356_, 4, v___x_1351_);
    return v___x_1356_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1357_ = leanh::lean_box(1);
    v___x_1358_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__4_once
        ),
        _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__4,
    );
    v___x_1359_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__1_once
        ),
        _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__1,
    );
    v___x_1360_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1360_, 0, v___x_1359_);
    leanh::lean_ctor_set(v___x_1360_, 1, v___x_1358_);
    leanh::lean_ctor_set(v___x_1360_, 2, v___x_1357_);
    return v___x_1360_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1362_ = l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__6;
    v___x_1363_ = l_Lean_stringToMessageData(v___x_1362_);
    return v___x_1363_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1365_ = l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__8;
    v___x_1366_ = l_Lean_stringToMessageData(v___x_1365_);
    return v___x_1366_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1368_ = l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__10;
    v___x_1369_ = l_Lean_stringToMessageData(v___x_1368_);
    return v___x_1369_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1371_ = l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__12;
    v___x_1372_ = l_Lean_stringToMessageData(v___x_1371_);
    return v___x_1372_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_1374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1374_ = l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__14;
    v___x_1375_ = l_Lean_stringToMessageData(v___x_1374_);
    return v___x_1375_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1377_ = l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__16;
    v___x_1378_ = l_Lean_stringToMessageData(v___x_1377_);
    return v___x_1378_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1380_ = l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__18;
    v___x_1381_ = l_Lean_stringToMessageData(v___x_1380_);
    return v___x_1381_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0(
    mut v_declHint_1382_: *mut leanh::LeanObject,
    mut v_toPure_1383_: *mut leanh::LeanObject,
    mut v_msg_1384_: *mut leanh::LeanObject,
    mut v_env_1385_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1386_: u8 = 0;
    v___x_1386_ = l_Lean_Name_isAnonymous(v_declHint_1382_);
    if v___x_1386_ == 0 {
        let mut v_isExporting_1387_: u8 = 0;
        v_isExporting_1387_ = leanh::lean_ctor_get_uint8(
            v_env_1385_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
        );
        if v_isExporting_1387_ == 0 {
            let mut v___x_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_env_1385_);
            leanh::lean_dec(v_declHint_1382_);
            v___x_1388_ =
                leanh::lean_apply_2(v_toPure_1383_, leanh::lean_box(0), v_msg_1384_);
            return v___x_1388_;
        } else {
            let mut v___x_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1390_: u8 = 0;
            leanh::lean_inc_ref(v_env_1385_);
            v___x_1389_ = l_Lean_Environment_setExporting(v_env_1385_, v___x_1386_);
            leanh::lean_inc(v_declHint_1382_);
            leanh::lean_inc_ref(v___x_1389_);
            v___x_1390_ =
                l_Lean_Environment_contains(v___x_1389_, v_declHint_1382_, v_isExporting_1387_);
            if v___x_1390_ == 0 {
                let mut v___x_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v___x_1389_);
                leanh::lean_dec_ref(v_env_1385_);
                leanh::lean_dec(v_declHint_1382_);
                v___x_1391_ = leanh::lean_apply_2(
                    v_toPure_1383_,
                    leanh::lean_box(0),
                    v_msg_1384_,
                );
                return v___x_1391_;
            } else {
                let mut v___x_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_c_1397_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1398_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1392_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__2_once
                    ),
                    _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__2,
                );
                v___x_1393_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__5
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__5_once
                    ),
                    _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__5,
                );
                v___x_1394_ = l_Lean_Options_empty;
                v___x_1395_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_1395_, 0, v___x_1389_);
                leanh::lean_ctor_set(v___x_1395_, 1, v___x_1392_);
                leanh::lean_ctor_set(v___x_1395_, 2, v___x_1393_);
                leanh::lean_ctor_set(v___x_1395_, 3, v___x_1394_);
                leanh::lean_inc(v_declHint_1382_);
                v___x_1396_ = l_Lean_MessageData_ofConstName(v_declHint_1382_, v___x_1386_);
                v_c_1397_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                leanh::lean_ctor_set(v_c_1397_, 0, v___x_1395_);
                leanh::lean_ctor_set(v_c_1397_, 1, v___x_1396_);
                v___x_1398_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1385_, v_declHint_1382_);
                if leanh::lean_obj_tag(v___x_1398_) == 0 {
                    let mut v___x_1399_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1400_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec_ref(v_env_1385_);
                    leanh::lean_dec(v_declHint_1382_);
                    v___x_1399_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__7);
                    v___x_1400_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1400_, 0, v___x_1399_);
                    leanh::lean_ctor_set(v___x_1400_, 1, v_c_1397_);
                    v___x_1401_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__9);
                    v___x_1402_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1402_, 0, v___x_1400_);
                    leanh::lean_ctor_set(v___x_1402_, 1, v___x_1401_);
                    v___x_1403_ = l_Lean_MessageData_note(v___x_1402_);
                    v___x_1404_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1404_, 0, v_msg_1384_);
                    leanh::lean_ctor_set(v___x_1404_, 1, v___x_1403_);
                    v___x_1405_ = leanh::lean_apply_2(
                        v_toPure_1383_,
                        leanh::lean_box(0),
                        v___x_1404_,
                    );
                    return v___x_1405_;
                } else {
                    let mut v_val_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v_mod_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1411_: u8 = 0;
                    v_val_1406_ = leanh::lean_ctor_get(v___x_1398_, 0);
                    leanh::lean_inc(v_val_1406_);
                    leanh::lean_dec_ref_known(v___x_1398_, 1);
                    v___x_1407_ = leanh::lean_box(0);
                    v___x_1408_ = l_Lean_Environment_header(v_env_1385_);
                    leanh::lean_dec_ref(v_env_1385_);
                    v___x_1409_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1408_);
                    v_mod_1410_ = lean_array_get(v___x_1407_, v___x_1409_, v_val_1406_);
                    leanh::lean_dec(v_val_1406_);
                    leanh::lean_dec_ref(v___x_1409_);
                    v___x_1411_ = l_Lean_isPrivateName(v_declHint_1382_);
                    leanh::lean_dec(v_declHint_1382_);
                    if v___x_1411_ == 0 {
                        let mut v___x_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1415_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v___x_1412_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__11);
                        v___x_1413_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1413_, 0, v___x_1412_);
                        leanh::lean_ctor_set(v___x_1413_, 1, v_c_1397_);
                        v___x_1414_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__13);
                        v___x_1415_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1415_, 0, v___x_1413_);
                        leanh::lean_ctor_set(v___x_1415_, 1, v___x_1414_);
                        v___x_1416_ = l_Lean_MessageData_ofName(v_mod_1410_);
                        v___x_1417_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1417_, 0, v___x_1415_);
                        leanh::lean_ctor_set(v___x_1417_, 1, v___x_1416_);
                        v___x_1418_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__15);
                        v___x_1419_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1419_, 0, v___x_1417_);
                        leanh::lean_ctor_set(v___x_1419_, 1, v___x_1418_);
                        v___x_1420_ = l_Lean_MessageData_note(v___x_1419_);
                        v___x_1421_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1421_, 0, v_msg_1384_);
                        leanh::lean_ctor_set(v___x_1421_, 1, v___x_1420_);
                        v___x_1422_ = leanh::lean_apply_2(
                            v_toPure_1383_,
                            leanh::lean_box(0),
                            v___x_1421_,
                        );
                        return v___x_1422_;
                    } else {
                        let mut v___x_1423_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1428_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1430_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v___x_1423_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__7);
                        v___x_1424_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1424_, 0, v___x_1423_);
                        leanh::lean_ctor_set(v___x_1424_, 1, v_c_1397_);
                        v___x_1425_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__17);
                        v___x_1426_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1426_, 0, v___x_1424_);
                        leanh::lean_ctor_set(v___x_1426_, 1, v___x_1425_);
                        v___x_1427_ = l_Lean_MessageData_ofName(v_mod_1410_);
                        v___x_1428_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1428_, 0, v___x_1426_);
                        leanh::lean_ctor_set(v___x_1428_, 1, v___x_1427_);
                        v___x_1429_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__19);
                        v___x_1430_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1430_, 0, v___x_1428_);
                        leanh::lean_ctor_set(v___x_1430_, 1, v___x_1429_);
                        v___x_1431_ = l_Lean_MessageData_note(v___x_1430_);
                        v___x_1432_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1432_, 0, v_msg_1384_);
                        leanh::lean_ctor_set(v___x_1432_, 1, v___x_1431_);
                        v___x_1433_ = leanh::lean_apply_2(
                            v_toPure_1383_,
                            leanh::lean_box(0),
                            v___x_1432_,
                        );
                        return v___x_1433_;
                    }
                }
            }
        }
    } else {
        let mut v___x_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_env_1385_);
        leanh::lean_dec(v_declHint_1382_);
        v___x_1434_ =
            leanh::lean_apply_2(v_toPure_1383_, leanh::lean_box(0), v_msg_1384_);
        return v___x_1434_;
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___redArg(
    mut v_inst_1435_: *mut leanh::LeanObject,
    mut v_inst_1436_: *mut leanh::LeanObject,
    mut v_msg_1437_: *mut leanh::LeanObject,
    mut v_declHint_1438_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1439_ = leanh::lean_ctor_get(v_inst_1435_, 0);
    leanh::lean_inc_ref(v_toApplicative_1439_);
    v_toBind_1440_ = leanh::lean_ctor_get(v_inst_1435_, 1);
    leanh::lean_inc(v_toBind_1440_);
    leanh::lean_dec_ref(v_inst_1435_);
    v_getEnv_1441_ = leanh::lean_ctor_get(v_inst_1436_, 0);
    leanh::lean_inc(v_getEnv_1441_);
    leanh::lean_dec_ref(v_inst_1436_);
    v_toPure_1442_ = leanh::lean_ctor_get(v_toApplicative_1439_, 1);
    leanh::lean_inc(v_toPure_1442_);
    leanh::lean_dec_ref(v_toApplicative_1439_);
    v___f_1443_ = leanh::lean_alloc_closure(
        l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_1443_, 0, v_declHint_1438_);
    leanh::lean_closure_set(v___f_1443_, 1, v_toPure_1442_);
    leanh::lean_closure_set(v___f_1443_, 2, v_msg_1437_);
    v___x_1444_ = leanh::lean_apply_4(
        v_toBind_1440_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getEnv_1441_,
        v___f_1443_,
    );
    return v___x_1444_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore(
    mut v_m_1445_: *mut leanh::LeanObject,
    mut v_inst_1446_: *mut leanh::LeanObject,
    mut v_inst_1447_: *mut leanh::LeanObject,
    mut v_inst_1448_: *mut leanh::LeanObject,
    mut v_msg_1449_: *mut leanh::LeanObject,
    mut v_declHint_1450_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1451_ = l_Lean_mkUnknownIdentifierMessageCore___redArg(
        v_inst_1446_,
        v_inst_1447_,
        v_msg_1449_,
        v_declHint_1450_,
    );
    return v___x_1451_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___boxed(
    mut v_m_1452_: *mut leanh::LeanObject,
    mut v_inst_1453_: *mut leanh::LeanObject,
    mut v_inst_1454_: *mut leanh::LeanObject,
    mut v_inst_1455_: *mut leanh::LeanObject,
    mut v_msg_1456_: *mut leanh::LeanObject,
    mut v_declHint_1457_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1458_ = l_Lean_mkUnknownIdentifierMessageCore(
        v_m_1452_,
        v_inst_1453_,
        v_inst_1454_,
        v_inst_1455_,
        v_msg_1456_,
        v_declHint_1457_,
    );
    leanh::lean_dec_ref(v_inst_1455_);
    return v_res_1458_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___redArg___lam__0(
    mut v_toPure_1459_: *mut leanh::LeanObject,
    mut v_msg_1460_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1461_ = l_Lean_unknownIdentifierMessageTag;
    v___x_1462_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1462_, 0, v___x_1461_);
    leanh::lean_ctor_set(v___x_1462_, 1, v_msg_1460_);
    v___x_1463_ =
        leanh::lean_apply_2(v_toPure_1459_, leanh::lean_box(0), v___x_1462_);
    return v___x_1463_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___redArg(
    mut v_inst_1464_: *mut leanh::LeanObject,
    mut v_inst_1465_: *mut leanh::LeanObject,
    mut v_msg_1466_: *mut leanh::LeanObject,
    mut v_declHint_1467_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1468_ = leanh::lean_ctor_get(v_inst_1464_, 0);
    v_toBind_1469_ = leanh::lean_ctor_get(v_inst_1464_, 1);
    leanh::lean_inc(v_toBind_1469_);
    v_toPure_1470_ = leanh::lean_ctor_get(v_toApplicative_1468_, 1);
    leanh::lean_inc(v_toPure_1470_);
    v___x_1471_ = l_Lean_mkUnknownIdentifierMessageCore___redArg(
        v_inst_1464_,
        v_inst_1465_,
        v_msg_1466_,
        v_declHint_1467_,
    );
    v___f_1472_ = leanh::lean_alloc_closure(
        l_Lean_mkUnknownIdentifierMessage___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1472_, 0, v_toPure_1470_);
    v___x_1473_ = leanh::lean_apply_4(
        v_toBind_1469_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1471_,
        v___f_1472_,
    );
    return v___x_1473_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage(
    mut v_m_1474_: *mut leanh::LeanObject,
    mut v_inst_1475_: *mut leanh::LeanObject,
    mut v_inst_1476_: *mut leanh::LeanObject,
    mut v_inst_1477_: *mut leanh::LeanObject,
    mut v_msg_1478_: *mut leanh::LeanObject,
    mut v_declHint_1479_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1480_ = l_Lean_mkUnknownIdentifierMessage___redArg(
        v_inst_1475_,
        v_inst_1476_,
        v_msg_1478_,
        v_declHint_1479_,
    );
    return v___x_1480_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___boxed(
    mut v_m_1481_: *mut leanh::LeanObject,
    mut v_inst_1482_: *mut leanh::LeanObject,
    mut v_inst_1483_: *mut leanh::LeanObject,
    mut v_inst_1484_: *mut leanh::LeanObject,
    mut v_msg_1485_: *mut leanh::LeanObject,
    mut v_declHint_1486_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1487_ = l_Lean_mkUnknownIdentifierMessage(
        v_m_1481_,
        v_inst_1482_,
        v_inst_1483_,
        v_inst_1484_,
        v_msg_1485_,
        v_declHint_1486_,
    );
    leanh::lean_dec_ref(v_inst_1484_);
    return v_res_1487_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___redArg___lam__0(
    mut v_inst_1488_: *mut leanh::LeanObject,
    mut v_inst_1489_: *mut leanh::LeanObject,
    mut v_ref_1490_: *mut leanh::LeanObject,
    mut v_____do__lift_1491_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1492_ = l_Lean_throwErrorAt___redArg(
        v_inst_1488_,
        v_inst_1489_,
        v_ref_1490_,
        v_____do__lift_1491_,
    );
    return v___x_1492_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___redArg(
    mut v_inst_1493_: *mut leanh::LeanObject,
    mut v_inst_1494_: *mut leanh::LeanObject,
    mut v_inst_1495_: *mut leanh::LeanObject,
    mut v_ref_1496_: *mut leanh::LeanObject,
    mut v_msg_1497_: *mut leanh::LeanObject,
    mut v_declHint_1498_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toBind_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toBind_1499_ = leanh::lean_ctor_get(v_inst_1493_, 1);
    leanh::lean_inc(v_toBind_1499_);
    leanh::lean_inc_ref(v_inst_1493_);
    v___f_1500_ = leanh::lean_alloc_closure(
        l_Lean_throwUnknownIdentifierAt___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_1500_, 0, v_inst_1493_);
    leanh::lean_closure_set(v___f_1500_, 1, v_inst_1495_);
    leanh::lean_closure_set(v___f_1500_, 2, v_ref_1496_);
    v___x_1501_ = l_Lean_mkUnknownIdentifierMessage___redArg(
        v_inst_1493_,
        v_inst_1494_,
        v_msg_1497_,
        v_declHint_1498_,
    );
    v___x_1502_ = leanh::lean_apply_4(
        v_toBind_1499_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1501_,
        v___f_1500_,
    );
    return v___x_1502_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt(
    mut v_m_1503_: *mut leanh::LeanObject,
    mut v_00_u03b1_1504_: *mut leanh::LeanObject,
    mut v_inst_1505_: *mut leanh::LeanObject,
    mut v_inst_1506_: *mut leanh::LeanObject,
    mut v_inst_1507_: *mut leanh::LeanObject,
    mut v_ref_1508_: *mut leanh::LeanObject,
    mut v_msg_1509_: *mut leanh::LeanObject,
    mut v_declHint_1510_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1511_ = l_Lean_throwUnknownIdentifierAt___redArg(
        v_inst_1505_,
        v_inst_1506_,
        v_inst_1507_,
        v_ref_1508_,
        v_msg_1509_,
        v_declHint_1510_,
    );
    return v___x_1511_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1513_ = l_Lean_throwUnknownConstantAt___redArg___closed__0;
    v___x_1514_ = l_Lean_stringToMessageData(v___x_1513_);
    return v___x_1514_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1516_ = l_Lean_throwUnknownConstantAt___redArg___closed__2;
    v___x_1517_ = l_Lean_stringToMessageData(v___x_1516_);
    return v___x_1517_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___redArg(
    mut v_inst_1518_: *mut leanh::LeanObject,
    mut v_inst_1519_: *mut leanh::LeanObject,
    mut v_inst_1520_: *mut leanh::LeanObject,
    mut v_ref_1521_: *mut leanh::LeanObject,
    mut v_constName_1522_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: u8 = 0;
    let mut v___x_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1523_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___redArg___closed__1_once),
        _init_l_Lean_throwUnknownConstantAt___redArg___closed__1,
    );
    v___x_1524_ = 0;
    leanh::lean_inc(v_constName_1522_);
    v___x_1525_ = l_Lean_MessageData_ofConstName(v_constName_1522_, v___x_1524_);
    v___x_1526_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1526_, 0, v___x_1523_);
    leanh::lean_ctor_set(v___x_1526_, 1, v___x_1525_);
    v___x_1527_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___redArg___closed__3),
        core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___redArg___closed__3_once),
        _init_l_Lean_throwUnknownConstantAt___redArg___closed__3,
    );
    v___x_1528_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1528_, 0, v___x_1526_);
    leanh::lean_ctor_set(v___x_1528_, 1, v___x_1527_);
    v___x_1529_ = l_Lean_throwUnknownIdentifierAt___redArg(
        v_inst_1518_,
        v_inst_1519_,
        v_inst_1520_,
        v_ref_1521_,
        v___x_1528_,
        v_constName_1522_,
    );
    return v___x_1529_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt(
    mut v_m_1530_: *mut leanh::LeanObject,
    mut v_00_u03b1_1531_: *mut leanh::LeanObject,
    mut v_inst_1532_: *mut leanh::LeanObject,
    mut v_inst_1533_: *mut leanh::LeanObject,
    mut v_inst_1534_: *mut leanh::LeanObject,
    mut v_ref_1535_: *mut leanh::LeanObject,
    mut v_constName_1536_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1537_ = l_Lean_throwUnknownConstantAt___redArg(
        v_inst_1532_,
        v_inst_1533_,
        v_inst_1534_,
        v_ref_1535_,
        v_constName_1536_,
    );
    return v___x_1537_;
}
pub unsafe fn l_Lean_throwUnknownConstant___redArg___lam__0(
    mut v_inst_1538_: *mut leanh::LeanObject,
    mut v_inst_1539_: *mut leanh::LeanObject,
    mut v_inst_1540_: *mut leanh::LeanObject,
    mut v_constName_1541_: *mut leanh::LeanObject,
    mut v_____do__lift_1542_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1543_ = l_Lean_throwUnknownConstantAt___redArg(
        v_inst_1538_,
        v_inst_1539_,
        v_inst_1540_,
        v_____do__lift_1542_,
        v_constName_1541_,
    );
    return v___x_1543_;
}
pub unsafe fn l_Lean_throwUnknownConstant___redArg(
    mut v_inst_1544_: *mut leanh::LeanObject,
    mut v_inst_1545_: *mut leanh::LeanObject,
    mut v_inst_1546_: *mut leanh::LeanObject,
    mut v_constName_1547_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toMonadRef_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRef_1550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toMonadRef_1548_ = leanh::lean_ctor_get(v_inst_1546_, 1);
    v_toBind_1549_ = leanh::lean_ctor_get(v_inst_1544_, 1);
    leanh::lean_inc(v_toBind_1549_);
    v_getRef_1550_ = leanh::lean_ctor_get(v_toMonadRef_1548_, 0);
    leanh::lean_inc(v_getRef_1550_);
    v___f_1551_ = leanh::lean_alloc_closure(
        l_Lean_throwUnknownConstant___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_1551_, 0, v_inst_1544_);
    leanh::lean_closure_set(v___f_1551_, 1, v_inst_1545_);
    leanh::lean_closure_set(v___f_1551_, 2, v_inst_1546_);
    leanh::lean_closure_set(v___f_1551_, 3, v_constName_1547_);
    v___x_1552_ = leanh::lean_apply_4(
        v_toBind_1549_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getRef_1550_,
        v___f_1551_,
    );
    return v___x_1552_;
}
pub unsafe fn l_Lean_throwUnknownConstant(
    mut v_m_1553_: *mut leanh::LeanObject,
    mut v_00_u03b1_1554_: *mut leanh::LeanObject,
    mut v_inst_1555_: *mut leanh::LeanObject,
    mut v_inst_1556_: *mut leanh::LeanObject,
    mut v_inst_1557_: *mut leanh::LeanObject,
    mut v_constName_1558_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1559_ = l_Lean_throwUnknownConstant___redArg(
        v_inst_1555_,
        v_inst_1556_,
        v_inst_1557_,
        v_constName_1558_,
    );
    return v___x_1559_;
}
pub unsafe fn l_Lean_ofExcept___redArg(
    mut v_inst_1560_: *mut leanh::LeanObject,
    mut v_inst_1561_: *mut leanh::LeanObject,
    mut v_inst_1562_: *mut leanh::LeanObject,
    mut v_x_1563_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1563_) == 0 {
        let mut v_a_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_1564_ = leanh::lean_ctor_get(v_x_1563_, 0);
        leanh::lean_inc(v_a_1564_);
        leanh::lean_dec_ref_known(v_x_1563_, 1);
        v___x_1565_ = leanh::lean_apply_1(v_inst_1562_, v_a_1564_);
        v___x_1566_ = l_Lean_throwError___redArg(v_inst_1560_, v_inst_1561_, v___x_1565_);
        return v___x_1566_;
    } else {
        let mut v_toApplicative_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_1567_ = leanh::lean_ctor_get(v_inst_1560_, 0);
        leanh::lean_inc_ref(v_toApplicative_1567_);
        leanh::lean_dec_ref(v_inst_1562_);
        leanh::lean_dec_ref(v_inst_1561_);
        leanh::lean_dec_ref(v_inst_1560_);
        v_toPure_1568_ = leanh::lean_ctor_get(v_toApplicative_1567_, 1);
        leanh::lean_inc(v_toPure_1568_);
        leanh::lean_dec_ref(v_toApplicative_1567_);
        v_a_1569_ = leanh::lean_ctor_get(v_x_1563_, 0);
        leanh::lean_inc(v_a_1569_);
        leanh::lean_dec_ref_known(v_x_1563_, 1);
        v___x_1570_ =
            leanh::lean_apply_2(v_toPure_1568_, leanh::lean_box(0), v_a_1569_);
        return v___x_1570_;
    }
}
pub unsafe fn l_Lean_ofExcept(
    mut v_m_1571_: *mut leanh::LeanObject,
    mut v_00_u03b5_1572_: *mut leanh::LeanObject,
    mut v_00_u03b1_1573_: *mut leanh::LeanObject,
    mut v_inst_1574_: *mut leanh::LeanObject,
    mut v_inst_1575_: *mut leanh::LeanObject,
    mut v_inst_1576_: *mut leanh::LeanObject,
    mut v_x_1577_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1578_ = l_Lean_ofExcept___redArg(v_inst_1574_, v_inst_1575_, v_inst_1576_, v_x_1577_);
    return v___x_1578_;
}
pub unsafe fn l___private_Lean_Exception_0__Lean_initFn_00___x40_Lean_Exception_2633972168____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1583_ = l___private_Lean_Exception_0__Lean_initFn___closed__1_00___x40_Lean_Exception_2633972168____hygCtx___hyg_2_;
    v___x_1584_ = l_Lean_registerInternalExceptionId(v___x_1583_);
    return v___x_1584_;
}
pub unsafe fn l___private_Lean_Exception_0__Lean_initFn_00___x40_Lean_Exception_2633972168____hygCtx___hyg_2____boxed(
    mut v_a_1585_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1586_ = l___private_Lean_Exception_0__Lean_initFn_00___x40_Lean_Exception_2633972168____hygCtx___hyg_2_();
    return v_res_1586_;
}
pub unsafe fn _init_l_Lean_throwInterruptException___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1587_ = leanh::lean_box(0);
    v___x_1588_ = l_Lean_interruptExceptionId;
    v___x_1589_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1589_, 0, v___x_1588_);
    leanh::lean_ctor_set(v___x_1589_, 1, v___x_1587_);
    return v___x_1589_;
}
pub unsafe fn l_Lean_throwInterruptException___redArg(
    mut v_inst_1590_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toMonadExceptOf_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_throw_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toMonadExceptOf_1591_ = leanh::lean_ctor_get(v_inst_1590_, 0);
    leanh::lean_inc_ref(v_toMonadExceptOf_1591_);
    leanh::lean_dec_ref(v_inst_1590_);
    v_throw_1592_ = leanh::lean_ctor_get(v_toMonadExceptOf_1591_, 0);
    leanh::lean_inc(v_throw_1592_);
    leanh::lean_dec_ref(v_toMonadExceptOf_1591_);
    v___x_1593_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_throwInterruptException___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_throwInterruptException___redArg___closed__0_once),
        _init_l_Lean_throwInterruptException___redArg___closed__0,
    );
    v___x_1594_ = leanh::lean_apply_2(v_throw_1592_, leanh::lean_box(0), v___x_1593_);
    return v___x_1594_;
}
pub unsafe fn l_Lean_throwInterruptException(
    mut v_m_1595_: *mut leanh::LeanObject,
    mut v_00_u03b1_1596_: *mut leanh::LeanObject,
    mut v_inst_1597_: *mut leanh::LeanObject,
    mut v_inst_1598_: *mut leanh::LeanObject,
    mut v_inst_1599_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1600_ = l_Lean_throwInterruptException___redArg(v_inst_1598_);
    return v___x_1600_;
}
pub unsafe fn l_Lean_throwInterruptException___boxed(
    mut v_m_1601_: *mut leanh::LeanObject,
    mut v_00_u03b1_1602_: *mut leanh::LeanObject,
    mut v_inst_1603_: *mut leanh::LeanObject,
    mut v_inst_1604_: *mut leanh::LeanObject,
    mut v_inst_1605_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1606_ = l_Lean_throwInterruptException(
        v_m_1601_,
        v_00_u03b1_1602_,
        v_inst_1603_,
        v_inst_1604_,
        v_inst_1605_,
    );
    leanh::lean_dec(v_inst_1605_);
    leanh::lean_dec_ref(v_inst_1603_);
    return v_res_1606_;
}
pub unsafe fn l_Lean_Exception_isInterrupt(mut v_x_1607_: *mut leanh::LeanObject) -> u8 {
    if leanh::lean_obj_tag(v_x_1607_) == 1 {
        let mut v_id_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1610_: u8 = 0;
        v_id_1608_ = leanh::lean_ctor_get(v_x_1607_, 0);
        v___x_1609_ = l_Lean_interruptExceptionId;
        v___x_1610_ = l_Lean_instBEqInternalExceptionId_beq(v_id_1608_, v___x_1609_);
        return v___x_1610_;
    } else {
        let mut v___x_1611_: u8 = 0;
        v___x_1611_ = 0;
        return v___x_1611_;
    }
}
pub unsafe fn l_Lean_Exception_isInterrupt___boxed(
    mut v_x_1612_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1613_: u8 = 0;
    let mut v_r_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1613_ = l_Lean_Exception_isInterrupt(v_x_1612_);
    leanh::lean_dec_ref(v_x_1612_);
    v_r_1614_ = leanh::lean_box((v_res_1613_) as usize);
    return v_r_1614_;
}
pub unsafe fn l_Lean_throwKernelException___redArg___lam__0(
    mut v_ex_1615_: *mut leanh::LeanObject,
    mut v_inst_1616_: *mut leanh::LeanObject,
    mut v_inst_1617_: *mut leanh::LeanObject,
    mut v_____do__lift_1618_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1619_ = l_Lean_Kernel_Exception_toMessageData(v_ex_1615_, v_____do__lift_1618_);
    v___x_1620_ = l_Lean_throwError___redArg(v_inst_1616_, v_inst_1617_, v___x_1619_);
    return v___x_1620_;
}
pub unsafe fn l_Lean_throwKernelException___redArg___lam__1(
    mut v_toBind_1621_: *mut leanh::LeanObject,
    mut v_inst_1622_: *mut leanh::LeanObject,
    mut v___f_1623_: *mut leanh::LeanObject,
    mut v_____r_1624_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1625_ = leanh::lean_apply_4(
        v_toBind_1621_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_1622_,
        v___f_1623_,
    );
    return v___x_1625_;
}
pub unsafe fn l_Lean_throwKernelException___redArg(
    mut v_inst_1626_: *mut leanh::LeanObject,
    mut v_inst_1627_: *mut leanh::LeanObject,
    mut v_inst_1628_: *mut leanh::LeanObject,
    mut v_ex_1629_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toBind_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toBind_1630_ = leanh::lean_ctor_get(v_inst_1626_, 1);
    leanh::lean_inc(v_toBind_1630_);
    leanh::lean_inc_ref(v_inst_1627_);
    leanh::lean_inc(v_ex_1629_);
    v___f_1631_ = leanh::lean_alloc_closure(
        l_Lean_throwKernelException___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_1631_, 0, v_ex_1629_);
    leanh::lean_closure_set(v___f_1631_, 1, v_inst_1626_);
    leanh::lean_closure_set(v___f_1631_, 2, v_inst_1627_);
    if leanh::lean_obj_tag(v_ex_1629_) == 16 {
        let mut v___f_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc(v_toBind_1630_);
        v___f_1632_ = leanh::lean_alloc_closure(
            l_Lean_throwKernelException___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            3,
        );
        leanh::lean_closure_set(v___f_1632_, 0, v_toBind_1630_);
        leanh::lean_closure_set(v___f_1632_, 1, v_inst_1628_);
        leanh::lean_closure_set(v___f_1632_, 2, v___f_1631_);
        v___x_1633_ = l_Lean_throwInterruptException___redArg(v_inst_1627_);
        v___x_1634_ = leanh::lean_apply_4(
            v_toBind_1630_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_1633_,
            v___f_1632_,
        );
        return v___x_1634_;
    } else {
        let mut v___x_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_ex_1629_);
        leanh::lean_dec_ref(v_inst_1627_);
        v___x_1635_ = leanh::lean_apply_4(
            v_toBind_1630_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v_inst_1628_,
            v___f_1631_,
        );
        return v___x_1635_;
    }
}
pub unsafe fn l_Lean_throwKernelException(
    mut v_m_1636_: *mut leanh::LeanObject,
    mut v_00_u03b1_1637_: *mut leanh::LeanObject,
    mut v_inst_1638_: *mut leanh::LeanObject,
    mut v_inst_1639_: *mut leanh::LeanObject,
    mut v_inst_1640_: *mut leanh::LeanObject,
    mut v_ex_1641_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1642_ =
        l_Lean_throwKernelException___redArg(v_inst_1638_, v_inst_1639_, v_inst_1640_, v_ex_1641_);
    return v___x_1642_;
}
pub unsafe fn l_Lean_ofExceptKernelException___redArg(
    mut v_inst_1643_: *mut leanh::LeanObject,
    mut v_inst_1644_: *mut leanh::LeanObject,
    mut v_inst_1645_: *mut leanh::LeanObject,
    mut v_x_1646_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1646_) == 0 {
        let mut v_a_1647_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_1647_ = leanh::lean_ctor_get(v_x_1646_, 0);
        leanh::lean_inc(v_a_1647_);
        leanh::lean_dec_ref_known(v_x_1646_, 1);
        v___x_1648_ = l_Lean_throwKernelException___redArg(
            v_inst_1643_,
            v_inst_1644_,
            v_inst_1645_,
            v_a_1647_,
        );
        return v___x_1648_;
    } else {
        let mut v_toApplicative_1649_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_1649_ = leanh::lean_ctor_get(v_inst_1643_, 0);
        leanh::lean_inc_ref(v_toApplicative_1649_);
        leanh::lean_dec(v_inst_1645_);
        leanh::lean_dec_ref(v_inst_1644_);
        leanh::lean_dec_ref(v_inst_1643_);
        v_toPure_1650_ = leanh::lean_ctor_get(v_toApplicative_1649_, 1);
        leanh::lean_inc(v_toPure_1650_);
        leanh::lean_dec_ref(v_toApplicative_1649_);
        v_a_1651_ = leanh::lean_ctor_get(v_x_1646_, 0);
        leanh::lean_inc(v_a_1651_);
        leanh::lean_dec_ref_known(v_x_1646_, 1);
        v___x_1652_ =
            leanh::lean_apply_2(v_toPure_1650_, leanh::lean_box(0), v_a_1651_);
        return v___x_1652_;
    }
}
pub unsafe fn l_Lean_ofExceptKernelException(
    mut v_m_1653_: *mut leanh::LeanObject,
    mut v_00_u03b1_1654_: *mut leanh::LeanObject,
    mut v_inst_1655_: *mut leanh::LeanObject,
    mut v_inst_1656_: *mut leanh::LeanObject,
    mut v_inst_1657_: *mut leanh::LeanObject,
    mut v_x_1658_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1659_ = l_Lean_ofExceptKernelException___redArg(
        v_inst_1655_,
        v_inst_1656_,
        v_inst_1657_,
        v_x_1658_,
    );
    return v___x_1659_;
}
pub unsafe fn l_Lean_instMonadRecDepthReaderT___redArg___lam__0(
    mut v_inst_1660_: *mut leanh::LeanObject,
    mut v_00_u03b1_1661_: *mut leanh::LeanObject,
    mut v_d_1662_: *mut leanh::LeanObject,
    mut v_x_1663_: *mut leanh::LeanObject,
    mut v_ctx_1664_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_withRecDepth_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_withRecDepth_1665_ = leanh::lean_ctor_get(v_inst_1660_, 0);
    leanh::lean_inc(v_withRecDepth_1665_);
    leanh::lean_dec_ref(v_inst_1660_);
    v___x_1666_ = leanh::lean_apply_1(v_x_1663_, v_ctx_1664_);
    v___x_1667_ = leanh::lean_apply_3(
        v_withRecDepth_1665_,
        leanh::lean_box(0),
        v_d_1662_,
        v___x_1666_,
    );
    return v___x_1667_;
}
pub unsafe fn l_Lean_instMonadRecDepthReaderT___redArg___lam__1(
    mut v_inst_1668_: *mut leanh::LeanObject,
    mut v_x_1669_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_getRecDepth_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_getRecDepth_1670_ = leanh::lean_ctor_get(v_inst_1668_, 1);
    leanh::lean_inc(v_getRecDepth_1670_);
    return v_getRecDepth_1670_;
}
pub unsafe fn l_Lean_instMonadRecDepthReaderT___redArg___lam__1___boxed(
    mut v_inst_1671_: *mut leanh::LeanObject,
    mut v_x_1672_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1673_ = l_Lean_instMonadRecDepthReaderT___redArg___lam__1(v_inst_1671_, v_x_1672_);
    leanh::lean_dec(v_x_1672_);
    leanh::lean_dec_ref(v_inst_1671_);
    return v_res_1673_;
}
pub unsafe fn l_Lean_instMonadRecDepthReaderT___redArg___lam__2(
    mut v_inst_1674_: *mut leanh::LeanObject,
    mut v_x_1675_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_getMaxRecDepth_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_getMaxRecDepth_1676_ = leanh::lean_ctor_get(v_inst_1674_, 2);
    leanh::lean_inc(v_getMaxRecDepth_1676_);
    return v_getMaxRecDepth_1676_;
}
pub unsafe fn l_Lean_instMonadRecDepthReaderT___redArg___lam__2___boxed(
    mut v_inst_1677_: *mut leanh::LeanObject,
    mut v_x_1678_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1679_ = l_Lean_instMonadRecDepthReaderT___redArg___lam__2(v_inst_1677_, v_x_1678_);
    leanh::lean_dec(v_x_1678_);
    leanh::lean_dec_ref(v_inst_1677_);
    return v_res_1679_;
}
pub unsafe fn l_Lean_instMonadRecDepthReaderT___redArg(
    mut v_inst_1680_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref_n(v_inst_1680_, 2);
    v___f_1681_ = leanh::lean_alloc_closure(
        l_Lean_instMonadRecDepthReaderT___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_1681_, 0, v_inst_1680_);
    v___f_1682_ = leanh::lean_alloc_closure(
        l_Lean_instMonadRecDepthReaderT___redArg___lam__1___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1682_, 0, v_inst_1680_);
    v___f_1683_ = leanh::lean_alloc_closure(
        l_Lean_instMonadRecDepthReaderT___redArg___lam__2___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1683_, 0, v_inst_1680_);
    v___x_1684_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1684_, 0, v___f_1681_);
    leanh::lean_ctor_set(v___x_1684_, 1, v___f_1682_);
    leanh::lean_ctor_set(v___x_1684_, 2, v___f_1683_);
    return v___x_1684_;
}
pub unsafe fn l_Lean_instMonadRecDepthReaderT(
    mut v_m_1685_: *mut leanh::LeanObject,
    mut v_00_u03c1_1686_: *mut leanh::LeanObject,
    mut v_inst_1687_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1688_ = l_Lean_instMonadRecDepthReaderT___redArg(v_inst_1687_);
    return v___x_1688_;
}
pub unsafe fn l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__1___redArg(
    mut v_inst_1689_: *mut leanh::LeanObject,
    mut v_d_1690_: *mut leanh::LeanObject,
    mut v_x_1691_: *mut leanh::LeanObject,
    mut v_ctx_1692_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_withRecDepth_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_withRecDepth_1693_ = leanh::lean_ctor_get(v_inst_1689_, 0);
    leanh::lean_inc(v_withRecDepth_1693_);
    leanh::lean_dec_ref(v_inst_1689_);
    leanh::lean_inc(v_ctx_1692_);
    v___x_1694_ = leanh::lean_apply_1(v_x_1691_, v_ctx_1692_);
    v___x_1695_ = leanh::lean_apply_3(
        v_withRecDepth_1693_,
        leanh::lean_box(0),
        v_d_1690_,
        v___x_1694_,
    );
    return v___x_1695_;
}
pub unsafe fn l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__1___redArg___boxed(
    mut v_inst_1696_: *mut leanh::LeanObject,
    mut v_d_1697_: *mut leanh::LeanObject,
    mut v_x_1698_: *mut leanh::LeanObject,
    mut v_ctx_1699_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1700_ = l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__1___redArg(
        v_inst_1696_,
        v_d_1697_,
        v_x_1698_,
        v_ctx_1699_,
    );
    leanh::lean_dec(v_ctx_1699_);
    return v_res_1700_;
}
pub unsafe fn l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__1(
    mut v_m_1701_: *mut leanh::LeanObject,
    mut v_00_u03c9_1702_: *mut leanh::LeanObject,
    mut v_00_u03c3_1703_: *mut leanh::LeanObject,
    mut v_inst_1704_: *mut leanh::LeanObject,
    mut v_00_u03b1_1705_: *mut leanh::LeanObject,
    mut v_d_1706_: *mut leanh::LeanObject,
    mut v_x_1707_: *mut leanh::LeanObject,
    mut v_ctx_1708_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_withRecDepth_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_withRecDepth_1709_ = leanh::lean_ctor_get(v_inst_1704_, 0);
    leanh::lean_inc(v_withRecDepth_1709_);
    leanh::lean_dec_ref(v_inst_1704_);
    leanh::lean_inc(v_ctx_1708_);
    v___x_1710_ = leanh::lean_apply_1(v_x_1707_, v_ctx_1708_);
    v___x_1711_ = leanh::lean_apply_3(
        v_withRecDepth_1709_,
        leanh::lean_box(0),
        v_d_1706_,
        v___x_1710_,
    );
    return v___x_1711_;
}
pub unsafe fn l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__1___boxed(
    mut v_m_1712_: *mut leanh::LeanObject,
    mut v_00_u03c9_1713_: *mut leanh::LeanObject,
    mut v_00_u03c3_1714_: *mut leanh::LeanObject,
    mut v_inst_1715_: *mut leanh::LeanObject,
    mut v_00_u03b1_1716_: *mut leanh::LeanObject,
    mut v_d_1717_: *mut leanh::LeanObject,
    mut v_x_1718_: *mut leanh::LeanObject,
    mut v_ctx_1719_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1720_ = l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__1(
        v_m_1712_,
        v_00_u03c9_1713_,
        v_00_u03c3_1714_,
        v_inst_1715_,
        v_00_u03b1_1716_,
        v_d_1717_,
        v_x_1718_,
        v_ctx_1719_,
    );
    leanh::lean_dec(v_ctx_1719_);
    return v_res_1720_;
}
pub unsafe fn l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__3___redArg(
    mut v_inst_1721_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_getRecDepth_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_getRecDepth_1722_ = leanh::lean_ctor_get(v_inst_1721_, 1);
    leanh::lean_inc(v_getRecDepth_1722_);
    return v_getRecDepth_1722_;
}
pub unsafe fn l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__3___redArg___boxed(
    mut v_inst_1723_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1724_ = l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__3___redArg(v_inst_1723_);
    leanh::lean_dec_ref(v_inst_1723_);
    return v_res_1724_;
}
pub unsafe fn l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__3(
    mut v_m_1725_: *mut leanh::LeanObject,
    mut v_00_u03c9_1726_: *mut leanh::LeanObject,
    mut v_00_u03c3_1727_: *mut leanh::LeanObject,
    mut v_inst_1728_: *mut leanh::LeanObject,
    mut v_x_1729_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_getRecDepth_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_getRecDepth_1730_ = leanh::lean_ctor_get(v_inst_1728_, 1);
    leanh::lean_inc(v_getRecDepth_1730_);
    return v_getRecDepth_1730_;
}
pub unsafe fn l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__3___boxed(
    mut v_m_1731_: *mut leanh::LeanObject,
    mut v_00_u03c9_1732_: *mut leanh::LeanObject,
    mut v_00_u03c3_1733_: *mut leanh::LeanObject,
    mut v_inst_1734_: *mut leanh::LeanObject,
    mut v_x_1735_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1736_ = l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__3(
        v_m_1731_,
        v_00_u03c9_1732_,
        v_00_u03c3_1733_,
        v_inst_1734_,
        v_x_1735_,
    );
    leanh::lean_dec(v_x_1735_);
    leanh::lean_dec_ref(v_inst_1734_);
    return v_res_1736_;
}
pub unsafe fn l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__5___redArg(
    mut v_inst_1737_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_getMaxRecDepth_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_getMaxRecDepth_1738_ = leanh::lean_ctor_get(v_inst_1737_, 2);
    leanh::lean_inc(v_getMaxRecDepth_1738_);
    return v_getMaxRecDepth_1738_;
}
pub unsafe fn l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__5___redArg___boxed(
    mut v_inst_1739_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1740_ = l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__5___redArg(v_inst_1739_);
    leanh::lean_dec_ref(v_inst_1739_);
    return v_res_1740_;
}
pub unsafe fn l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__5(
    mut v_m_1741_: *mut leanh::LeanObject,
    mut v_00_u03c9_1742_: *mut leanh::LeanObject,
    mut v_00_u03c3_1743_: *mut leanh::LeanObject,
    mut v_inst_1744_: *mut leanh::LeanObject,
    mut v_x_1745_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_getMaxRecDepth_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_getMaxRecDepth_1746_ = leanh::lean_ctor_get(v_inst_1744_, 2);
    leanh::lean_inc(v_getMaxRecDepth_1746_);
    return v_getMaxRecDepth_1746_;
}
pub unsafe fn l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__5___boxed(
    mut v_m_1747_: *mut leanh::LeanObject,
    mut v_00_u03c9_1748_: *mut leanh::LeanObject,
    mut v_00_u03c3_1749_: *mut leanh::LeanObject,
    mut v_inst_1750_: *mut leanh::LeanObject,
    mut v_x_1751_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1752_ = l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__5(
        v_m_1747_,
        v_00_u03c9_1748_,
        v_00_u03c3_1749_,
        v_inst_1750_,
        v_x_1751_,
    );
    leanh::lean_dec(v_x_1751_);
    leanh::lean_dec_ref(v_inst_1750_);
    return v_res_1752_;
}
pub unsafe fn l_Lean_instMonadRecDepthStateRefT_x27OfMonad___redArg(
    mut v_inst_1753_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref_n(v_inst_1753_, 2);
    v___x_1754_ = leanh::lean_alloc_closure(
        l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__1___boxed as *mut core::ffi::c_void,
        8,
        4,
    );
    leanh::lean_closure_set(v___x_1754_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1754_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1754_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1754_, 3, v_inst_1753_);
    v___x_1755_ = leanh::lean_alloc_closure(
        l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__3___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___x_1755_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1755_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1755_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1755_, 3, v_inst_1753_);
    v___x_1756_ = leanh::lean_alloc_closure(
        l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__5___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___x_1756_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1756_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1756_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1756_, 3, v_inst_1753_);
    v___x_1757_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1757_, 0, v___x_1754_);
    leanh::lean_ctor_set(v___x_1757_, 1, v___x_1755_);
    leanh::lean_ctor_set(v___x_1757_, 2, v___x_1756_);
    return v___x_1757_;
}
pub unsafe fn l_Lean_instMonadRecDepthStateRefT_x27OfMonad(
    mut v_m_1758_: *mut leanh::LeanObject,
    mut v_00_u03c9_1759_: *mut leanh::LeanObject,
    mut v_00_u03c3_1760_: *mut leanh::LeanObject,
    mut v_inst_1761_: *mut leanh::LeanObject,
    mut v_inst_1762_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1763_ = l_Lean_instMonadRecDepthStateRefT_x27OfMonad___redArg(v_inst_1762_);
    return v___x_1763_;
}
pub unsafe fn l_Lean_instMonadRecDepthStateRefT_x27OfMonad___boxed(
    mut v_m_1764_: *mut leanh::LeanObject,
    mut v_00_u03c9_1765_: *mut leanh::LeanObject,
    mut v_00_u03c3_1766_: *mut leanh::LeanObject,
    mut v_inst_1767_: *mut leanh::LeanObject,
    mut v_inst_1768_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1769_ = l_Lean_instMonadRecDepthStateRefT_x27OfMonad(
        v_m_1764_,
        v_00_u03c9_1765_,
        v_00_u03c3_1766_,
        v_inst_1767_,
        v_inst_1768_,
    );
    leanh::lean_dec_ref(v_inst_1767_);
    return v_res_1769_;
}
pub unsafe fn l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__1___redArg(
    mut v_inst_1770_: *mut leanh::LeanObject,
    mut v_a_1771_: *mut leanh::LeanObject,
    mut v_a_1772_: *mut leanh::LeanObject,
    mut v_a_1773_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_withRecDepth_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_withRecDepth_1774_ = leanh::lean_ctor_get(v_inst_1770_, 0);
    leanh::lean_inc(v_withRecDepth_1774_);
    leanh::lean_dec_ref(v_inst_1770_);
    leanh::lean_inc(v_a_1773_);
    v___x_1775_ = leanh::lean_apply_1(v_a_1772_, v_a_1773_);
    v___x_1776_ = leanh::lean_apply_3(
        v_withRecDepth_1774_,
        leanh::lean_box(0),
        v_a_1771_,
        v___x_1775_,
    );
    return v___x_1776_;
}
pub unsafe fn l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__1___redArg___boxed(
    mut v_inst_1777_: *mut leanh::LeanObject,
    mut v_a_1778_: *mut leanh::LeanObject,
    mut v_a_1779_: *mut leanh::LeanObject,
    mut v_a_1780_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1781_ = l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__1___redArg(
        v_inst_1777_,
        v_a_1778_,
        v_a_1779_,
        v_a_1780_,
    );
    leanh::lean_dec(v_a_1780_);
    return v_res_1781_;
}
pub unsafe fn l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__1(
    mut v_00_u03b1_1782_: *mut leanh::LeanObject,
    mut v_m_1783_: *mut leanh::LeanObject,
    mut v_00_u03c9_1784_: *mut leanh::LeanObject,
    mut v_00_u03b2_1785_: *mut leanh::LeanObject,
    mut v_inst_1786_: *mut leanh::LeanObject,
    mut v_inst_1787_: *mut leanh::LeanObject,
    mut v_inst_1788_: *mut leanh::LeanObject,
    mut v_inst_1789_: *mut leanh::LeanObject,
    mut v_00_u03b1_1790_: *mut leanh::LeanObject,
    mut v_a_1791_: *mut leanh::LeanObject,
    mut v_a_1792_: *mut leanh::LeanObject,
    mut v_a_1793_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_withRecDepth_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_withRecDepth_1794_ = leanh::lean_ctor_get(v_inst_1789_, 0);
    leanh::lean_inc(v_withRecDepth_1794_);
    leanh::lean_dec_ref(v_inst_1789_);
    leanh::lean_inc(v_a_1793_);
    v___x_1795_ = leanh::lean_apply_1(v_a_1792_, v_a_1793_);
    v___x_1796_ = leanh::lean_apply_3(
        v_withRecDepth_1794_,
        leanh::lean_box(0),
        v_a_1791_,
        v___x_1795_,
    );
    return v___x_1796_;
}
pub unsafe fn l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__1___boxed(
    mut v_00_u03b1_1797_: *mut leanh::LeanObject,
    mut v_m_1798_: *mut leanh::LeanObject,
    mut v_00_u03c9_1799_: *mut leanh::LeanObject,
    mut v_00_u03b2_1800_: *mut leanh::LeanObject,
    mut v_inst_1801_: *mut leanh::LeanObject,
    mut v_inst_1802_: *mut leanh::LeanObject,
    mut v_inst_1803_: *mut leanh::LeanObject,
    mut v_inst_1804_: *mut leanh::LeanObject,
    mut v_00_u03b1_1805_: *mut leanh::LeanObject,
    mut v_a_1806_: *mut leanh::LeanObject,
    mut v_a_1807_: *mut leanh::LeanObject,
    mut v_a_1808_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1809_ = l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__1(
        v_00_u03b1_1797_,
        v_m_1798_,
        v_00_u03c9_1799_,
        v_00_u03b2_1800_,
        v_inst_1801_,
        v_inst_1802_,
        v_inst_1803_,
        v_inst_1804_,
        v_00_u03b1_1805_,
        v_a_1806_,
        v_a_1807_,
        v_a_1808_,
    );
    leanh::lean_dec(v_a_1808_);
    leanh::lean_dec_ref(v_inst_1802_);
    leanh::lean_dec_ref(v_inst_1801_);
    return v_res_1809_;
}
pub unsafe fn l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__3___redArg(
    mut v_inst_1810_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_getRecDepth_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_getRecDepth_1811_ = leanh::lean_ctor_get(v_inst_1810_, 1);
    leanh::lean_inc(v_getRecDepth_1811_);
    return v_getRecDepth_1811_;
}
pub unsafe fn l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__3___redArg___boxed(
    mut v_inst_1812_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1813_ = l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__3___redArg(v_inst_1812_);
    leanh::lean_dec_ref(v_inst_1812_);
    return v_res_1813_;
}
pub unsafe fn l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__3(
    mut v_00_u03b1_1814_: *mut leanh::LeanObject,
    mut v_m_1815_: *mut leanh::LeanObject,
    mut v_00_u03c9_1816_: *mut leanh::LeanObject,
    mut v_00_u03b2_1817_: *mut leanh::LeanObject,
    mut v_inst_1818_: *mut leanh::LeanObject,
    mut v_inst_1819_: *mut leanh::LeanObject,
    mut v_inst_1820_: *mut leanh::LeanObject,
    mut v_inst_1821_: *mut leanh::LeanObject,
    mut v_a_1822_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_getRecDepth_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_getRecDepth_1823_ = leanh::lean_ctor_get(v_inst_1821_, 1);
    leanh::lean_inc(v_getRecDepth_1823_);
    return v_getRecDepth_1823_;
}
pub unsafe fn l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__3___boxed(
    mut v_00_u03b1_1824_: *mut leanh::LeanObject,
    mut v_m_1825_: *mut leanh::LeanObject,
    mut v_00_u03c9_1826_: *mut leanh::LeanObject,
    mut v_00_u03b2_1827_: *mut leanh::LeanObject,
    mut v_inst_1828_: *mut leanh::LeanObject,
    mut v_inst_1829_: *mut leanh::LeanObject,
    mut v_inst_1830_: *mut leanh::LeanObject,
    mut v_inst_1831_: *mut leanh::LeanObject,
    mut v_a_1832_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1833_ = l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__3(
        v_00_u03b1_1824_,
        v_m_1825_,
        v_00_u03c9_1826_,
        v_00_u03b2_1827_,
        v_inst_1828_,
        v_inst_1829_,
        v_inst_1830_,
        v_inst_1831_,
        v_a_1832_,
    );
    leanh::lean_dec(v_a_1832_);
    leanh::lean_dec_ref(v_inst_1831_);
    leanh::lean_dec_ref(v_inst_1829_);
    leanh::lean_dec_ref(v_inst_1828_);
    return v_res_1833_;
}
pub unsafe fn l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__5___redArg(
    mut v_inst_1834_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_getMaxRecDepth_1835_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_getMaxRecDepth_1835_ = leanh::lean_ctor_get(v_inst_1834_, 2);
    leanh::lean_inc(v_getMaxRecDepth_1835_);
    return v_getMaxRecDepth_1835_;
}
pub unsafe fn l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__5___redArg___boxed(
    mut v_inst_1836_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1837_ = l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__5___redArg(v_inst_1836_);
    leanh::lean_dec_ref(v_inst_1836_);
    return v_res_1837_;
}
pub unsafe fn l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__5(
    mut v_00_u03b1_1838_: *mut leanh::LeanObject,
    mut v_m_1839_: *mut leanh::LeanObject,
    mut v_00_u03c9_1840_: *mut leanh::LeanObject,
    mut v_00_u03b2_1841_: *mut leanh::LeanObject,
    mut v_inst_1842_: *mut leanh::LeanObject,
    mut v_inst_1843_: *mut leanh::LeanObject,
    mut v_inst_1844_: *mut leanh::LeanObject,
    mut v_inst_1845_: *mut leanh::LeanObject,
    mut v_a_1846_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_getMaxRecDepth_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_getMaxRecDepth_1847_ = leanh::lean_ctor_get(v_inst_1845_, 2);
    leanh::lean_inc(v_getMaxRecDepth_1847_);
    return v_getMaxRecDepth_1847_;
}
pub unsafe fn l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__5___boxed(
    mut v_00_u03b1_1848_: *mut leanh::LeanObject,
    mut v_m_1849_: *mut leanh::LeanObject,
    mut v_00_u03c9_1850_: *mut leanh::LeanObject,
    mut v_00_u03b2_1851_: *mut leanh::LeanObject,
    mut v_inst_1852_: *mut leanh::LeanObject,
    mut v_inst_1853_: *mut leanh::LeanObject,
    mut v_inst_1854_: *mut leanh::LeanObject,
    mut v_inst_1855_: *mut leanh::LeanObject,
    mut v_a_1856_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1857_ = l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__5(
        v_00_u03b1_1848_,
        v_m_1849_,
        v_00_u03c9_1850_,
        v_00_u03b2_1851_,
        v_inst_1852_,
        v_inst_1853_,
        v_inst_1854_,
        v_inst_1855_,
        v_a_1856_,
    );
    leanh::lean_dec(v_a_1856_);
    leanh::lean_dec_ref(v_inst_1855_);
    leanh::lean_dec_ref(v_inst_1853_);
    leanh::lean_dec_ref(v_inst_1852_);
    return v_res_1857_;
}
pub unsafe fn l_Lean_instMonadRecDepthMonadCacheTOfMonad___redArg(
    mut v_inst_1858_: *mut leanh::LeanObject,
    mut v_inst_1859_: *mut leanh::LeanObject,
    mut v_inst_1860_: *mut leanh::LeanObject,
    mut v_inst_1861_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref_n(v_inst_1861_, 2);
    leanh::lean_inc_ref_n(v_inst_1859_, 2);
    leanh::lean_inc_ref_n(v_inst_1858_, 2);
    v___x_1862_ = leanh::lean_alloc_closure(
        l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__1___boxed as *mut core::ffi::c_void,
        12,
        8,
    );
    leanh::lean_closure_set(v___x_1862_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1862_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1862_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1862_, 3, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1862_, 4, v_inst_1858_);
    leanh::lean_closure_set(v___x_1862_, 5, v_inst_1859_);
    leanh::lean_closure_set(v___x_1862_, 6, v_inst_1860_);
    leanh::lean_closure_set(v___x_1862_, 7, v_inst_1861_);
    v___x_1863_ = leanh::lean_alloc_closure(
        l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__3___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    leanh::lean_closure_set(v___x_1863_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1863_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1863_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1863_, 3, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1863_, 4, v_inst_1858_);
    leanh::lean_closure_set(v___x_1863_, 5, v_inst_1859_);
    leanh::lean_closure_set(v___x_1863_, 6, v_inst_1860_);
    leanh::lean_closure_set(v___x_1863_, 7, v_inst_1861_);
    v___x_1864_ = leanh::lean_alloc_closure(
        l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__5___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    leanh::lean_closure_set(v___x_1864_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1864_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1864_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1864_, 3, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1864_, 4, v_inst_1858_);
    leanh::lean_closure_set(v___x_1864_, 5, v_inst_1859_);
    leanh::lean_closure_set(v___x_1864_, 6, v_inst_1860_);
    leanh::lean_closure_set(v___x_1864_, 7, v_inst_1861_);
    v___x_1865_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1865_, 0, v___x_1862_);
    leanh::lean_ctor_set(v___x_1865_, 1, v___x_1863_);
    leanh::lean_ctor_set(v___x_1865_, 2, v___x_1864_);
    return v___x_1865_;
}
pub unsafe fn l_Lean_instMonadRecDepthMonadCacheTOfMonad(
    mut v_00_u03b1_1866_: *mut leanh::LeanObject,
    mut v_m_1867_: *mut leanh::LeanObject,
    mut v_00_u03c9_1868_: *mut leanh::LeanObject,
    mut v_00_u03b2_1869_: *mut leanh::LeanObject,
    mut v_inst_1870_: *mut leanh::LeanObject,
    mut v_inst_1871_: *mut leanh::LeanObject,
    mut v_inst_1872_: *mut leanh::LeanObject,
    mut v_inst_1873_: *mut leanh::LeanObject,
    mut v_inst_1874_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1875_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1875_ = l_Lean_instMonadRecDepthMonadCacheTOfMonad___redArg(
        v_inst_1870_,
        v_inst_1871_,
        v_inst_1873_,
        v_inst_1874_,
    );
    return v___x_1875_;
}
pub unsafe fn l_Lean_instMonadRecDepthMonadCacheTOfMonad___boxed(
    mut v_00_u03b1_1876_: *mut leanh::LeanObject,
    mut v_m_1877_: *mut leanh::LeanObject,
    mut v_00_u03c9_1878_: *mut leanh::LeanObject,
    mut v_00_u03b2_1879_: *mut leanh::LeanObject,
    mut v_inst_1880_: *mut leanh::LeanObject,
    mut v_inst_1881_: *mut leanh::LeanObject,
    mut v_inst_1882_: *mut leanh::LeanObject,
    mut v_inst_1883_: *mut leanh::LeanObject,
    mut v_inst_1884_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1885_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1885_ = l_Lean_instMonadRecDepthMonadCacheTOfMonad(
        v_00_u03b1_1876_,
        v_m_1877_,
        v_00_u03c9_1878_,
        v_00_u03b2_1879_,
        v_inst_1880_,
        v_inst_1881_,
        v_inst_1882_,
        v_inst_1883_,
        v_inst_1884_,
    );
    leanh::lean_dec_ref(v_inst_1882_);
    return v_res_1885_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___redArg___closed__3() -> *mut leanh::LeanObject
{
    let mut v___x_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1891_ = l_Lean_maxRecDepthErrorMessage;
    v___x_1892_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1892_, 0, v___x_1891_);
    return v___x_1892_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___redArg___closed__4() -> *mut leanh::LeanObject
{
    let mut v___x_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1893_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___redArg___closed__3),
        core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___redArg___closed__3_once),
        _init_l_Lean_throwMaxRecDepthAt___redArg___closed__3,
    );
    v___x_1894_ = l_Lean_MessageData_ofFormat(v___x_1893_);
    return v___x_1894_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___redArg___closed__5() -> *mut leanh::LeanObject
{
    let mut v___x_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1895_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___redArg___closed__4),
        core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___redArg___closed__4_once),
        _init_l_Lean_throwMaxRecDepthAt___redArg___closed__4,
    );
    v___x_1896_ = l_Lean_throwMaxRecDepthAt___redArg___closed__2;
    v___x_1897_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1897_, 0, v___x_1896_);
    leanh::lean_ctor_set(v___x_1897_, 1, v___x_1895_);
    return v___x_1897_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___redArg(
    mut v_inst_1898_: *mut leanh::LeanObject,
    mut v_ref_1899_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toMonadExceptOf_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_throw_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1904_: u8 = 0;
    let mut v___x_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1910_: u8 = 0;
    let mut v_unused_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toMonadExceptOf_1900_ = leanh::lean_ctor_get(v_inst_1898_, 0);
                leanh::lean_inc_ref(v_toMonadExceptOf_1900_);
                leanh::lean_dec_ref(v_inst_1898_);
                v_throw_1901_ = leanh::lean_ctor_get(v_toMonadExceptOf_1900_, 0);
                v_isSharedCheck_1910_ =
                    (!leanh::lean_is_exclusive(v_toMonadExceptOf_1900_)) as u8;
                if v_isSharedCheck_1910_ == 0 {
                    v_unused_1911_ = leanh::lean_ctor_get(v_toMonadExceptOf_1900_, 1);
                    leanh::lean_dec(v_unused_1911_);
                    v___x_1903_ = v_toMonadExceptOf_1900_;
                    v_isShared_1904_ = v_isSharedCheck_1910_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_throw_1901_);
                    leanh::lean_dec(v_toMonadExceptOf_1900_);
                    v___x_1903_ = leanh::lean_box(0);
                    v_isShared_1904_ = v_isSharedCheck_1910_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1905_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___redArg___closed__5),
                    core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___redArg___closed__5_once),
                    _init_l_Lean_throwMaxRecDepthAt___redArg___closed__5,
                );
                if v_isShared_1904_ == 0 {
                    leanh::lean_ctor_set(v___x_1903_, 1, v___x_1905_);
                    leanh::lean_ctor_set(v___x_1903_, 0, v_ref_1899_);
                    v___x_1907_ = v___x_1903_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1909_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1909_, 0, v_ref_1899_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1909_, 1, v___x_1905_);
                    v___x_1907_ = v_reuseFailAlloc_1909_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1908_ = leanh::lean_apply_2(
                    v_throw_1901_,
                    leanh::lean_box(0),
                    v___x_1907_,
                );
                return v___x_1908_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwMaxRecDepthAt(
    mut v_m_1912_: *mut leanh::LeanObject,
    mut v_00_u03b1_1913_: *mut leanh::LeanObject,
    mut v_inst_1914_: *mut leanh::LeanObject,
    mut v_ref_1915_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1916_ = l_Lean_throwMaxRecDepthAt___redArg(v_inst_1914_, v_ref_1915_);
    return v___x_1916_;
}
pub unsafe fn l_Lean_Exception_isMaxRecDepth(mut v_ex_1917_: *mut leanh::LeanObject) -> u8 {
    if leanh::lean_obj_tag(v_ex_1917_) == 0 {
        let mut v_msg_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1922_: u8 = 0;
        v_msg_1918_ = leanh::lean_ctor_get(v_ex_1917_, 1);
        leanh::lean_inc_ref(v_msg_1918_);
        leanh::lean_dec_ref_known(v_ex_1917_, 2);
        v___x_1919_ = l_Lean_MessageData_stripNestedTags(v_msg_1918_);
        v___x_1920_ = l_Lean_MessageData_kind(v___x_1919_);
        leanh::lean_dec_ref(v___x_1919_);
        v___x_1921_ = l_Lean_throwMaxRecDepthAt___redArg___closed__2;
        v___x_1922_ = lean_name_eq(v___x_1920_, v___x_1921_);
        leanh::lean_dec(v___x_1920_);
        return v___x_1922_;
    } else {
        let mut v___x_1923_: u8 = 0;
        leanh::lean_dec_ref(v_ex_1917_);
        v___x_1923_ = 0;
        return v___x_1923_;
    }
}
pub unsafe fn l_Lean_Exception_isMaxRecDepth___boxed(
    mut v_ex_1924_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1925_: u8 = 0;
    let mut v_r_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1925_ = l_Lean_Exception_isMaxRecDepth(v_ex_1924_);
    v_r_1926_ = leanh::lean_box((v_res_1925_) as usize);
    return v_r_1926_;
}
pub unsafe fn l_Lean_withIncRecDepth___redArg___lam__0(
    mut v_inst_1927_: *mut leanh::LeanObject,
    mut v_____do__lift_1928_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1929_ = l_Lean_throwMaxRecDepthAt___redArg(v_inst_1927_, v_____do__lift_1928_);
    return v___x_1929_;
}
pub unsafe fn l_Lean_withIncRecDepth___redArg___lam__1(
    mut v_curr_1930_: *mut leanh::LeanObject,
    mut v_withRecDepth_1931_: *mut leanh::LeanObject,
    mut v_x_1932_: *mut leanh::LeanObject,
    mut v_inst_1933_: *mut leanh::LeanObject,
    mut v_toBind_1934_: *mut leanh::LeanObject,
    mut v___f_1935_: *mut leanh::LeanObject,
    mut v_max_1936_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: u8 = 0;
    let mut v___x_1943_: u8 = 0;
    let mut v_toMonadRef_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRef_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1941_ = leanh::lean_unsigned_to_nat(0);
                v___x_1942_ = lean_nat_dec_eq(v_max_1936_, v___x_1941_);
                if v___x_1942_ == 0 {
                    v___x_1943_ = lean_nat_dec_eq(v_curr_1930_, v_max_1936_);
                    if v___x_1943_ == 0 {
                        leanh::lean_dec(v___f_1935_);
                        leanh::lean_dec(v_toBind_1934_);
                        leanh::lean_dec_ref(v_inst_1933_);
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_1932_);
                        leanh::lean_dec(v_withRecDepth_1931_);
                        v_toMonadRef_1944_ = leanh::lean_ctor_get(v_inst_1933_, 1);
                        leanh::lean_inc_ref(v_toMonadRef_1944_);
                        leanh::lean_dec_ref(v_inst_1933_);
                        v_getRef_1945_ = leanh::lean_ctor_get(v_toMonadRef_1944_, 0);
                        leanh::lean_inc(v_getRef_1945_);
                        leanh::lean_dec_ref(v_toMonadRef_1944_);
                        v___x_1946_ = leanh::lean_apply_4(
                            v_toBind_1934_,
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v_getRef_1945_,
                            v___f_1935_,
                        );
                        return v___x_1946_;
                    }
                } else {
                    leanh::lean_dec(v___f_1935_);
                    leanh::lean_dec(v_toBind_1934_);
                    leanh::lean_dec_ref(v_inst_1933_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1938_ = leanh::lean_unsigned_to_nat(1);
                v___x_1939_ = lean_nat_add(v_curr_1930_, v___x_1938_);
                v___x_1940_ = leanh::lean_apply_3(
                    v_withRecDepth_1931_,
                    leanh::lean_box(0),
                    v___x_1939_,
                    v_x_1932_,
                );
                return v___x_1940_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withIncRecDepth___redArg___lam__1___boxed(
    mut v_curr_1947_: *mut leanh::LeanObject,
    mut v_withRecDepth_1948_: *mut leanh::LeanObject,
    mut v_x_1949_: *mut leanh::LeanObject,
    mut v_inst_1950_: *mut leanh::LeanObject,
    mut v_toBind_1951_: *mut leanh::LeanObject,
    mut v___f_1952_: *mut leanh::LeanObject,
    mut v_max_1953_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1954_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1954_ = l_Lean_withIncRecDepth___redArg___lam__1(
        v_curr_1947_,
        v_withRecDepth_1948_,
        v_x_1949_,
        v_inst_1950_,
        v_toBind_1951_,
        v___f_1952_,
        v_max_1953_,
    );
    leanh::lean_dec(v_max_1953_);
    leanh::lean_dec(v_curr_1947_);
    return v_res_1954_;
}
pub unsafe fn l_Lean_withIncRecDepth___redArg___lam__2(
    mut v_withRecDepth_1955_: *mut leanh::LeanObject,
    mut v_x_1956_: *mut leanh::LeanObject,
    mut v_inst_1957_: *mut leanh::LeanObject,
    mut v_toBind_1958_: *mut leanh::LeanObject,
    mut v___f_1959_: *mut leanh::LeanObject,
    mut v_getMaxRecDepth_1960_: *mut leanh::LeanObject,
    mut v_curr_1961_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_toBind_1958_);
    v___f_1962_ = leanh::lean_alloc_closure(
        l_Lean_withIncRecDepth___redArg___lam__1___boxed as *mut core::ffi::c_void,
        7,
        6,
    );
    leanh::lean_closure_set(v___f_1962_, 0, v_curr_1961_);
    leanh::lean_closure_set(v___f_1962_, 1, v_withRecDepth_1955_);
    leanh::lean_closure_set(v___f_1962_, 2, v_x_1956_);
    leanh::lean_closure_set(v___f_1962_, 3, v_inst_1957_);
    leanh::lean_closure_set(v___f_1962_, 4, v_toBind_1958_);
    leanh::lean_closure_set(v___f_1962_, 5, v___f_1959_);
    v___x_1963_ = leanh::lean_apply_4(
        v_toBind_1958_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getMaxRecDepth_1960_,
        v___f_1962_,
    );
    return v___x_1963_;
}
pub unsafe fn l_Lean_withIncRecDepth___redArg(
    mut v_inst_1964_: *mut leanh::LeanObject,
    mut v_inst_1965_: *mut leanh::LeanObject,
    mut v_inst_1966_: *mut leanh::LeanObject,
    mut v_x_1967_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toBind_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_withRecDepth_1969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRecDepth_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getMaxRecDepth_1971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toBind_1968_ = leanh::lean_ctor_get(v_inst_1964_, 1);
    leanh::lean_inc_n(v_toBind_1968_, 2);
    leanh::lean_dec_ref(v_inst_1964_);
    v_withRecDepth_1969_ = leanh::lean_ctor_get(v_inst_1966_, 0);
    leanh::lean_inc(v_withRecDepth_1969_);
    v_getRecDepth_1970_ = leanh::lean_ctor_get(v_inst_1966_, 1);
    leanh::lean_inc(v_getRecDepth_1970_);
    v_getMaxRecDepth_1971_ = leanh::lean_ctor_get(v_inst_1966_, 2);
    leanh::lean_inc(v_getMaxRecDepth_1971_);
    leanh::lean_dec_ref(v_inst_1966_);
    leanh::lean_inc_ref(v_inst_1965_);
    v___f_1972_ = leanh::lean_alloc_closure(
        l_Lean_withIncRecDepth___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1972_, 0, v_inst_1965_);
    v___f_1973_ = leanh::lean_alloc_closure(
        l_Lean_withIncRecDepth___redArg___lam__2 as *mut core::ffi::c_void,
        7,
        6,
    );
    leanh::lean_closure_set(v___f_1973_, 0, v_withRecDepth_1969_);
    leanh::lean_closure_set(v___f_1973_, 1, v_x_1967_);
    leanh::lean_closure_set(v___f_1973_, 2, v_inst_1965_);
    leanh::lean_closure_set(v___f_1973_, 3, v_toBind_1968_);
    leanh::lean_closure_set(v___f_1973_, 4, v___f_1972_);
    leanh::lean_closure_set(v___f_1973_, 5, v_getMaxRecDepth_1971_);
    v___x_1974_ = leanh::lean_apply_4(
        v_toBind_1968_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getRecDepth_1970_,
        v___f_1973_,
    );
    return v___x_1974_;
}
pub unsafe fn l_Lean_withIncRecDepth(
    mut v_m_1975_: *mut leanh::LeanObject,
    mut v_00_u03b1_1976_: *mut leanh::LeanObject,
    mut v_inst_1977_: *mut leanh::LeanObject,
    mut v_inst_1978_: *mut leanh::LeanObject,
    mut v_inst_1979_: *mut leanh::LeanObject,
    mut v_x_1980_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toBind_1981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_withRecDepth_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRecDepth_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getMaxRecDepth_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toBind_1981_ = leanh::lean_ctor_get(v_inst_1977_, 1);
    leanh::lean_inc_n(v_toBind_1981_, 2);
    leanh::lean_dec_ref(v_inst_1977_);
    v_withRecDepth_1982_ = leanh::lean_ctor_get(v_inst_1979_, 0);
    leanh::lean_inc(v_withRecDepth_1982_);
    v_getRecDepth_1983_ = leanh::lean_ctor_get(v_inst_1979_, 1);
    leanh::lean_inc(v_getRecDepth_1983_);
    v_getMaxRecDepth_1984_ = leanh::lean_ctor_get(v_inst_1979_, 2);
    leanh::lean_inc(v_getMaxRecDepth_1984_);
    leanh::lean_dec_ref(v_inst_1979_);
    leanh::lean_inc_ref(v_inst_1978_);
    v___f_1985_ = leanh::lean_alloc_closure(
        l_Lean_withIncRecDepth___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1985_, 0, v_inst_1978_);
    v___f_1986_ = leanh::lean_alloc_closure(
        l_Lean_withIncRecDepth___redArg___lam__2 as *mut core::ffi::c_void,
        7,
        6,
    );
    leanh::lean_closure_set(v___f_1986_, 0, v_withRecDepth_1982_);
    leanh::lean_closure_set(v___f_1986_, 1, v_x_1980_);
    leanh::lean_closure_set(v___f_1986_, 2, v_inst_1978_);
    leanh::lean_closure_set(v___f_1986_, 3, v_toBind_1981_);
    leanh::lean_closure_set(v___f_1986_, 4, v___f_1985_);
    leanh::lean_closure_set(v___f_1986_, 5, v_getMaxRecDepth_1984_);
    v___x_1987_ = leanh::lean_apply_4(
        v_toBind_1981_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getRecDepth_1983_,
        v___f_1986_,
    );
    return v___x_1987_;
}
pub unsafe fn _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_2071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2071_ =
        l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__6;
    v___x_2072_ = l_String_toRawSubstring_x27(v___x_2071_);
    return v___x_2072_;
}
pub unsafe fn _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__22()
-> *mut leanh::LeanObject {
    let mut v___x_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2103_ =
        l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__21;
    v___x_2104_ = l_String_toRawSubstring_x27(v___x_2103_);
    return v___x_2104_;
}
pub unsafe fn l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1(
    mut v_x_2118_: *mut leanh::LeanObject,
    mut v_a_2119_: *mut leanh::LeanObject,
    mut v_a_2120_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: u8 = 0;
    v___x_2121_ = l_Lean_termThrowError_____00__closed__2;
    leanh::lean_inc(v_x_2118_);
    v___x_2122_ = l_Lean_Syntax_isOfKind(v_x_2118_, v___x_2121_);
    if v___x_2122_ == 0 {
        let mut v___x_2123_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2124_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_2118_);
        v___x_2123_ = leanh::lean_box(1);
        v___x_2124_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2124_, 0, v___x_2123_);
        leanh::lean_ctor_set(v___x_2124_, 1, v_a_2120_);
        return v___x_2124_;
    } else {
        let mut v___x_2125_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2126_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2128_: u8 = 0;
        v___x_2125_ = leanh::lean_unsigned_to_nat(1);
        v___x_2126_ = l_Lean_Syntax_getArg(v_x_2118_, v___x_2125_);
        leanh::lean_dec(v_x_2118_);
        v___x_2127_ =
            l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__1;
        leanh::lean_inc(v___x_2126_);
        v___x_2128_ = l_Lean_Syntax_isOfKind(v___x_2126_, v___x_2127_);
        if v___x_2128_ == 0 {
            let mut v_quotContext_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_currMacroScope_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_ref_2131_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2134_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2137_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2142_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_quotContext_2129_ = leanh::lean_ctor_get(v_a_2119_, 1);
            v_currMacroScope_2130_ = leanh::lean_ctor_get(v_a_2119_, 2);
            v_ref_2131_ = leanh::lean_ctor_get(v_a_2119_, 5);
            v___x_2132_ = l_Lean_SourceInfo_fromRef(v_ref_2131_, v___x_2128_);
            v___x_2133_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5;
            v___x_2134_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__7), core::ptr::addr_of_mut!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__7_once), _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__7);
            v___x_2135_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__9;
            leanh::lean_inc(v_currMacroScope_2130_);
            leanh::lean_inc(v_quotContext_2129_);
            v___x_2136_ =
                l_Lean_addMacroScope(v_quotContext_2129_, v___x_2135_, v_currMacroScope_2130_);
            v___x_2137_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__11;
            leanh::lean_inc_n(v___x_2132_, 2);
            v___x_2138_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
            leanh::lean_ctor_set(v___x_2138_, 0, v___x_2132_);
            leanh::lean_ctor_set(v___x_2138_, 1, v___x_2134_);
            leanh::lean_ctor_set(v___x_2138_, 2, v___x_2136_);
            leanh::lean_ctor_set(v___x_2138_, 3, v___x_2137_);
            v___x_2139_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__13;
            v___x_2140_ = l_Lean_Syntax_node1(v___x_2132_, v___x_2139_, v___x_2126_);
            v___x_2141_ = l_Lean_Syntax_node2(v___x_2132_, v___x_2133_, v___x_2138_, v___x_2140_);
            v___x_2142_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_2142_, 0, v___x_2141_);
            leanh::lean_ctor_set(v___x_2142_, 1, v_a_2120_);
            return v___x_2142_;
        } else {
            let mut v_quotContext_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_currMacroScope_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_ref_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2146_: u8 = 0;
            let mut v___x_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2149_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2151_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2152_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2157_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2158_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2160_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2161_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2162_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2163_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2165_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2166_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2167_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2168_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2171_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_quotContext_2143_ = leanh::lean_ctor_get(v_a_2119_, 1);
            v_currMacroScope_2144_ = leanh::lean_ctor_get(v_a_2119_, 2);
            v_ref_2145_ = leanh::lean_ctor_get(v_a_2119_, 5);
            v___x_2146_ = 0;
            v___x_2147_ = l_Lean_SourceInfo_fromRef(v_ref_2145_, v___x_2146_);
            v___x_2148_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5;
            v___x_2149_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__7), core::ptr::addr_of_mut!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__7_once), _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__7);
            v___x_2150_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__9;
            leanh::lean_inc_n(v_currMacroScope_2144_, 2);
            leanh::lean_inc_n(v_quotContext_2143_, 2);
            v___x_2151_ =
                l_Lean_addMacroScope(v_quotContext_2143_, v___x_2150_, v_currMacroScope_2144_);
            v___x_2152_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__11;
            leanh::lean_inc_n(v___x_2147_, 10);
            v___x_2153_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
            leanh::lean_ctor_set(v___x_2153_, 0, v___x_2147_);
            leanh::lean_ctor_set(v___x_2153_, 1, v___x_2149_);
            leanh::lean_ctor_set(v___x_2153_, 2, v___x_2151_);
            leanh::lean_ctor_set(v___x_2153_, 3, v___x_2152_);
            v___x_2154_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__13;
            v___x_2155_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__15;
            v___x_2156_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__17;
            v___x_2157_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__18;
            v___x_2158_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_2158_, 0, v___x_2147_);
            leanh::lean_ctor_set(v___x_2158_, 1, v___x_2157_);
            v___x_2159_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__20;
            v___x_2160_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__22), core::ptr::addr_of_mut!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__22_once), _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__22);
            v___x_2161_ = leanh::lean_box(0);
            v___x_2162_ =
                l_Lean_addMacroScope(v_quotContext_2143_, v___x_2161_, v_currMacroScope_2144_);
            v___x_2163_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__25;
            v___x_2164_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
            leanh::lean_ctor_set(v___x_2164_, 0, v___x_2147_);
            leanh::lean_ctor_set(v___x_2164_, 1, v___x_2160_);
            leanh::lean_ctor_set(v___x_2164_, 2, v___x_2162_);
            leanh::lean_ctor_set(v___x_2164_, 3, v___x_2163_);
            v___x_2165_ = l_Lean_Syntax_node1(v___x_2147_, v___x_2159_, v___x_2164_);
            v___x_2166_ = l_Lean_Syntax_node2(v___x_2147_, v___x_2156_, v___x_2158_, v___x_2165_);
            v___x_2167_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__27;
            v___x_2168_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__28;
            v___x_2169_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_2169_, 0, v___x_2147_);
            leanh::lean_ctor_set(v___x_2169_, 1, v___x_2168_);
            v___x_2170_ = l_Lean_Syntax_node2(v___x_2147_, v___x_2167_, v___x_2169_, v___x_2126_);
            v___x_2171_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__29;
            v___x_2172_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_2172_, 0, v___x_2147_);
            leanh::lean_ctor_set(v___x_2172_, 1, v___x_2171_);
            v___x_2173_ = l_Lean_Syntax_node3(
                v___x_2147_,
                v___x_2155_,
                v___x_2166_,
                v___x_2170_,
                v___x_2172_,
            );
            v___x_2174_ = l_Lean_Syntax_node1(v___x_2147_, v___x_2154_, v___x_2173_);
            v___x_2175_ = l_Lean_Syntax_node2(v___x_2147_, v___x_2148_, v___x_2153_, v___x_2174_);
            v___x_2176_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_2176_, 0, v___x_2175_);
            leanh::lean_ctor_set(v___x_2176_, 1, v_a_2120_);
            return v___x_2176_;
        }
    }
}
pub unsafe fn l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___boxed(
    mut v_x_2177_: *mut leanh::LeanObject,
    mut v_a_2178_: *mut leanh::LeanObject,
    mut v_a_2179_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2180_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1(
        v_x_2177_, v_a_2178_, v_a_2179_,
    );
    leanh::lean_dec_ref(v_a_2178_);
    return v_res_2180_;
}
pub unsafe fn _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2182_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__0;
    v___x_2183_ = l_String_toRawSubstring_x27(v___x_2182_);
    return v___x_2183_;
}
pub unsafe fn l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1(
    mut v_x_2194_: *mut leanh::LeanObject,
    mut v_a_2195_: *mut leanh::LeanObject,
    mut v_a_2196_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: u8 = 0;
    v___x_2197_ = l_Lean_termThrowErrorAt_________00__closed__1;
    leanh::lean_inc(v_x_2194_);
    v___x_2198_ = l_Lean_Syntax_isOfKind(v_x_2194_, v___x_2197_);
    if v___x_2198_ == 0 {
        let mut v___x_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_2194_);
        v___x_2199_ = leanh::lean_box(1);
        v___x_2200_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2200_, 0, v___x_2199_);
        leanh::lean_ctor_set(v___x_2200_, 1, v_a_2196_);
        return v___x_2200_;
    } else {
        let mut v___x_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2206_: u8 = 0;
        v___x_2201_ = leanh::lean_unsigned_to_nat(1);
        v___x_2202_ = l_Lean_Syntax_getArg(v_x_2194_, v___x_2201_);
        v___x_2203_ = leanh::lean_unsigned_to_nat(2);
        v___x_2204_ = l_Lean_Syntax_getArg(v_x_2194_, v___x_2203_);
        leanh::lean_dec(v_x_2194_);
        v___x_2205_ =
            l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__1;
        leanh::lean_inc(v___x_2204_);
        v___x_2206_ = l_Lean_Syntax_isOfKind(v___x_2204_, v___x_2205_);
        if v___x_2206_ == 0 {
            let mut v_quotContext_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_currMacroScope_2208_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_ref_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2210_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2211_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2216_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2219_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_quotContext_2207_ = leanh::lean_ctor_get(v_a_2195_, 1);
            v_currMacroScope_2208_ = leanh::lean_ctor_get(v_a_2195_, 2);
            v_ref_2209_ = leanh::lean_ctor_get(v_a_2195_, 5);
            v___x_2210_ = l_Lean_SourceInfo_fromRef(v_ref_2209_, v___x_2206_);
            v___x_2211_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5;
            v___x_2212_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__1), core::ptr::addr_of_mut!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__1_once), _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__1);
            v___x_2213_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__3;
            leanh::lean_inc(v_currMacroScope_2208_);
            leanh::lean_inc(v_quotContext_2207_);
            v___x_2214_ =
                l_Lean_addMacroScope(v_quotContext_2207_, v___x_2213_, v_currMacroScope_2208_);
            v___x_2215_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__5;
            leanh::lean_inc_n(v___x_2210_, 2);
            v___x_2216_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
            leanh::lean_ctor_set(v___x_2216_, 0, v___x_2210_);
            leanh::lean_ctor_set(v___x_2216_, 1, v___x_2212_);
            leanh::lean_ctor_set(v___x_2216_, 2, v___x_2214_);
            leanh::lean_ctor_set(v___x_2216_, 3, v___x_2215_);
            v___x_2217_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__13;
            v___x_2218_ = l_Lean_Syntax_node2(v___x_2210_, v___x_2217_, v___x_2202_, v___x_2204_);
            v___x_2219_ = l_Lean_Syntax_node2(v___x_2210_, v___x_2211_, v___x_2216_, v___x_2218_);
            v___x_2220_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_2220_, 0, v___x_2219_);
            leanh::lean_ctor_set(v___x_2220_, 1, v_a_2196_);
            return v___x_2220_;
        } else {
            let mut v_quotContext_2221_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_currMacroScope_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_ref_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2224_: u8 = 0;
            let mut v___x_2225_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2226_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2227_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2228_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2248_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2249_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2250_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2251_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2252_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2253_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_quotContext_2221_ = leanh::lean_ctor_get(v_a_2195_, 1);
            v_currMacroScope_2222_ = leanh::lean_ctor_get(v_a_2195_, 2);
            v_ref_2223_ = leanh::lean_ctor_get(v_a_2195_, 5);
            v___x_2224_ = 0;
            v___x_2225_ = l_Lean_SourceInfo_fromRef(v_ref_2223_, v___x_2224_);
            v___x_2226_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5;
            v___x_2227_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__1), core::ptr::addr_of_mut!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__1_once), _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__1);
            v___x_2228_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__3;
            leanh::lean_inc_n(v_currMacroScope_2222_, 2);
            leanh::lean_inc_n(v_quotContext_2221_, 2);
            v___x_2229_ =
                l_Lean_addMacroScope(v_quotContext_2221_, v___x_2228_, v_currMacroScope_2222_);
            v___x_2230_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__5;
            leanh::lean_inc_n(v___x_2225_, 10);
            v___x_2231_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
            leanh::lean_ctor_set(v___x_2231_, 0, v___x_2225_);
            leanh::lean_ctor_set(v___x_2231_, 1, v___x_2227_);
            leanh::lean_ctor_set(v___x_2231_, 2, v___x_2229_);
            leanh::lean_ctor_set(v___x_2231_, 3, v___x_2230_);
            v___x_2232_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__13;
            v___x_2233_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__15;
            v___x_2234_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__17;
            v___x_2235_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__18;
            v___x_2236_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_2236_, 0, v___x_2225_);
            leanh::lean_ctor_set(v___x_2236_, 1, v___x_2235_);
            v___x_2237_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__20;
            v___x_2238_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__22), core::ptr::addr_of_mut!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__22_once), _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__22);
            v___x_2239_ = leanh::lean_box(0);
            v___x_2240_ =
                l_Lean_addMacroScope(v_quotContext_2221_, v___x_2239_, v_currMacroScope_2222_);
            v___x_2241_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__25;
            v___x_2242_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
            leanh::lean_ctor_set(v___x_2242_, 0, v___x_2225_);
            leanh::lean_ctor_set(v___x_2242_, 1, v___x_2238_);
            leanh::lean_ctor_set(v___x_2242_, 2, v___x_2240_);
            leanh::lean_ctor_set(v___x_2242_, 3, v___x_2241_);
            v___x_2243_ = l_Lean_Syntax_node1(v___x_2225_, v___x_2237_, v___x_2242_);
            v___x_2244_ = l_Lean_Syntax_node2(v___x_2225_, v___x_2234_, v___x_2236_, v___x_2243_);
            v___x_2245_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__27;
            v___x_2246_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__28;
            v___x_2247_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_2247_, 0, v___x_2225_);
            leanh::lean_ctor_set(v___x_2247_, 1, v___x_2246_);
            v___x_2248_ = l_Lean_Syntax_node2(v___x_2225_, v___x_2245_, v___x_2247_, v___x_2204_);
            v___x_2249_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__29;
            v___x_2250_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_2250_, 0, v___x_2225_);
            leanh::lean_ctor_set(v___x_2250_, 1, v___x_2249_);
            v___x_2251_ = l_Lean_Syntax_node3(
                v___x_2225_,
                v___x_2233_,
                v___x_2244_,
                v___x_2248_,
                v___x_2250_,
            );
            v___x_2252_ = l_Lean_Syntax_node2(v___x_2225_, v___x_2232_, v___x_2202_, v___x_2251_);
            v___x_2253_ = l_Lean_Syntax_node2(v___x_2225_, v___x_2226_, v___x_2231_, v___x_2252_);
            v___x_2254_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_2254_, 0, v___x_2253_);
            leanh::lean_ctor_set(v___x_2254_, 1, v_a_2196_);
            return v___x_2254_;
        }
    }
}
pub unsafe fn l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___boxed(
    mut v_x_2255_: *mut leanh::LeanObject,
    mut v_a_2256_: *mut leanh::LeanObject,
    mut v_a_2257_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2258_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2258_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1(
        v_x_2255_, v_a_2256_, v_a_2257_,
    );
    leanh::lean_dec_ref(v_a_2256_);
    return v_res_2258_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Exception(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_InternalExceptionId(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_ErrorExplanation(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_instInhabitedException = _init_l_Lean_instInhabitedException();
    leanh::lean_mark_persistent(l_Lean_instInhabitedException);
    l_Lean_unknownIdentifierMessageTag = _init_l_Lean_unknownIdentifierMessageTag();
    leanh::lean_mark_persistent(l_Lean_unknownIdentifierMessageTag);
    res = l___private_Lean_Exception_0__Lean_initFn_00___x40_Lean_Exception_2633972168____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_interruptExceptionId = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_interruptExceptionId);
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Exception(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Exception(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_InternalExceptionId(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_ErrorExplanation(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Exception(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Exception(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Exception(builtin);
}