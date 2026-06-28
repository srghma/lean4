// Lean compiler output
// Module: Lean.Exception
// Imports: Lean.InternalExceptionId Lean.ErrorExplanation
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr4, l_Lean_SourceInfo_fromRef,
    l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind, l_Lean_Syntax_node1, l_Lean_Syntax_node2,
    l_Lean_Syntax_node3, l_Lean_addMacroScope, l_Lean_maxRecDepthErrorMessage, l_Lean_replaceRef,
    l_String_toRawSubstring_x27,
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
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get, lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add, lean_nat_dec_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_usize, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_get_value, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_unsigned_to_nat,
};
static mut l_Lean_instInhabitedException___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instInhabitedException___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_instInhabitedException: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_unknownIdentifierMessageTag___closed__0_value: LeanStringObject<5> =
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
        m_data: [108, 101, 97, 110, 0],
    };
static mut l_Lean_unknownIdentifierMessageTag___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_unknownIdentifierMessageTag___closed__0_value) as *mut LeanObject;
pub static l_Lean_unknownIdentifierMessageTag___closed__1_value: LeanStringObject<18> =
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
            117, 110, 107, 110, 111, 119, 110, 73, 100, 101, 110, 116, 105, 102, 105, 101, 114, 0,
        ],
    };
static mut l_Lean_unknownIdentifierMessageTag___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_unknownIdentifierMessageTag___closed__1_value) as *mut LeanObject;
static l_Lean_unknownIdentifierMessageTag___closed__2_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_unknownIdentifierMessageTag___closed__0_value)
                as *mut LeanObject,
            9199928461212983083 as *mut LeanObject,
        ],
    };
pub static l_Lean_unknownIdentifierMessageTag___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_unknownIdentifierMessageTag___closed__2_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_unknownIdentifierMessageTag___closed__1_value)
                as *mut LeanObject,
            12904620932282659916 as *mut LeanObject,
        ],
    };
static mut l_Lean_unknownIdentifierMessageTag___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_unknownIdentifierMessageTag___closed__2_value) as *mut LeanObject;
static mut l_Lean_unknownIdentifierMessageTag___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_unknownIdentifierMessageTag___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_unknownIdentifierMessageTag: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__6_value:
    LeanStringObject<24> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__6_value)
        as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__8_value:
    LeanStringObject<79> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__8_value)
        as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__9_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__9: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__10_value:
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
        65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110,
        32, 96, 0,
    ],
};
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__10_value)
        as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__11_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__11: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__12_value:
    LeanStringObject<68> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__12_value)
        as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__13_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__13: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__14_value:
    LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__14_value)
        as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__15_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__15: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__16_value:
    LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__16_value)
        as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__17_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__17: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__18_value:
    LeanStringObject<54> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__18_value)
        as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__19_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__19: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___redArg___closed__0_value: LeanStringObject<19> =
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
            85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0,
        ],
    };
static mut l_Lean_throwUnknownConstantAt___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___redArg___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___redArg___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_throwUnknownConstantAt___redArg___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___redArg___closed__2_value: LeanStringObject<2> =
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
        m_data: [96, 0],
    };
static mut l_Lean_throwUnknownConstantAt___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___redArg___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___redArg___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_throwUnknownConstantAt___redArg___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Exception_0__Lean_initFn___closed__0_00___x40_Lean_Exception_2633972168____hygCtx___hyg_2__value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [105, 110, 116, 101, 114, 114, 117, 112, 116, 0]};
static mut l___private_Lean_Exception_0__Lean_initFn___closed__0_00___x40_Lean_Exception_2633972168____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Exception_0__Lean_initFn___closed__0_00___x40_Lean_Exception_2633972168____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Exception_0__Lean_initFn___closed__1_00___x40_Lean_Exception_2633972168____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Exception_0__Lean_initFn___closed__0_00___x40_Lean_Exception_2633972168____hygCtx___hyg_2__value) as *mut LeanObject,13194118745300296762 as *mut LeanObject] };
static mut l___private_Lean_Exception_0__Lean_initFn___closed__1_00___x40_Lean_Exception_2633972168____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Exception_0__Lean_initFn___closed__1_00___x40_Lean_Exception_2633972168____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l_Lean_throwInterruptException___redArg___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_throwInterruptException___redArg___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_throwMaxRecDepthAt___redArg___closed__0_value: LeanStringObject<8> =
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
        m_data: [114, 117, 110, 116, 105, 109, 101, 0],
    };
static mut l_Lean_throwMaxRecDepthAt___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_throwMaxRecDepthAt___redArg___closed__1_value: LeanStringObject<12> =
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
        m_data: [109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 0],
    };
static mut l_Lean_throwMaxRecDepthAt___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___redArg___closed__1_value) as *mut LeanObject;
static l_Lean_throwMaxRecDepthAt___redArg___closed__2_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___redArg___closed__0_value)
                as *mut LeanObject,
            7310567555909517314 as *mut LeanObject,
        ],
    };
pub static l_Lean_throwMaxRecDepthAt___redArg___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___redArg___closed__2_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___redArg___closed__1_value)
                as *mut LeanObject,
            273128857561458264 as *mut LeanObject,
        ],
    };
static mut l_Lean_throwMaxRecDepthAt___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_throwMaxRecDepthAt___redArg___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_throwMaxRecDepthAt___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___redArg___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_throwMaxRecDepthAt___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___redArg___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_throwMaxRecDepthAt___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_termThrowError_____00__closed__0_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_termThrowError_____00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__0_value) as *mut LeanObject;
pub static l_Lean_termThrowError_____00__closed__1_value: LeanStringObject<17> = LeanStringObject {
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
        116, 101, 114, 109, 84, 104, 114, 111, 119, 69, 114, 114, 111, 114, 95, 95, 0,
    ],
};
static mut l_Lean_termThrowError_____00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__1_value) as *mut LeanObject;
static l_Lean_termThrowError_____00__closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
pub static l_Lean_termThrowError_____00__closed__2_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__2_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__1_value) as *mut LeanObject,
        3344210737276464609 as *mut LeanObject,
    ],
};
static mut l_Lean_termThrowError_____00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__2_value) as *mut LeanObject;
pub static l_Lean_termThrowError_____00__closed__3_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_termThrowError_____00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__3_value) as *mut LeanObject;
pub static l_Lean_termThrowError_____00__closed__4_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__3_value) as *mut LeanObject,
        12571085391447129896 as *mut LeanObject,
    ],
};
static mut l_Lean_termThrowError_____00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__4_value) as *mut LeanObject;
pub static l_Lean_termThrowError_____00__closed__5_value: LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_termThrowError_____00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__5_value) as *mut LeanObject;
pub static l_Lean_termThrowError_____00__closed__6_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__5_value) as *mut LeanObject],
};
static mut l_Lean_termThrowError_____00__closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__6_value) as *mut LeanObject;
pub static l_Lean_termThrowError_____00__closed__7_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_termThrowError_____00__closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__7_value) as *mut LeanObject;
pub static l_Lean_termThrowError_____00__closed__8_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__7_value) as *mut LeanObject,
        393173242845875278 as *mut LeanObject,
    ],
};
static mut l_Lean_termThrowError_____00__closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__8_value) as *mut LeanObject;
pub static l_Lean_termThrowError_____00__closed__9_value: LeanStringObject<16> = LeanStringObject {
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
        105, 110, 116, 101, 114, 112, 111, 108, 97, 116, 101, 100, 83, 116, 114, 0,
    ],
};
static mut l_Lean_termThrowError_____00__closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__9_value) as *mut LeanObject;
pub static l_Lean_termThrowError_____00__closed__10_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__9_value) as *mut LeanObject,
        18163029821153688220 as *mut LeanObject,
    ],
};
static mut l_Lean_termThrowError_____00__closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__10_value) as *mut LeanObject;
pub static l_Lean_termThrowError_____00__closed__11_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_termThrowError_____00__closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__11_value) as *mut LeanObject;
pub static l_Lean_termThrowError_____00__closed__12_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__11_value) as *mut LeanObject,
        8609355255726335675 as *mut LeanObject,
    ],
};
static mut l_Lean_termThrowError_____00__closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__12_value) as *mut LeanObject;
pub static l_Lean_termThrowError_____00__closed__13_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 7,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__12_value) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_termThrowError_____00__closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__13_value) as *mut LeanObject;
pub static l_Lean_termThrowError_____00__closed__14_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__10_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__13_value) as *mut LeanObject,
    ],
};
static mut l_Lean_termThrowError_____00__closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__14_value) as *mut LeanObject;
pub static l_Lean_termThrowError_____00__closed__15_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__14_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__13_value) as *mut LeanObject,
    ],
};
static mut l_Lean_termThrowError_____00__closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__15_value) as *mut LeanObject;
pub static l_Lean_termThrowError_____00__closed__16_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__15_value) as *mut LeanObject,
    ],
};
static mut l_Lean_termThrowError_____00__closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__16_value) as *mut LeanObject;
pub static l_Lean_termThrowError_____00__closed__17_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__2_value) as *mut LeanObject,
        (((1022 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__16_value) as *mut LeanObject,
    ],
};
static mut l_Lean_termThrowError_____00__closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__17_value) as *mut LeanObject;
pub static mut l_Lean_termThrowError____: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__17_value) as *mut LeanObject;
pub static l_Lean_termThrowErrorAt_________00__closed__0_value: LeanStringObject<21> =
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
            116, 101, 114, 109, 84, 104, 114, 111, 119, 69, 114, 114, 111, 114, 65, 116, 95, 95,
            95, 95, 0,
        ],
    };
static mut l_Lean_termThrowErrorAt_________00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowErrorAt_________00__closed__0_value) as *mut LeanObject;
static l_Lean_termThrowErrorAt_________00__closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__0_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
pub static l_Lean_termThrowErrorAt_________00__closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_termThrowErrorAt_________00__closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_termThrowErrorAt_________00__closed__0_value)
                as *mut LeanObject,
            4940719421648177115 as *mut LeanObject,
        ],
    };
static mut l_Lean_termThrowErrorAt_________00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowErrorAt_________00__closed__1_value) as *mut LeanObject;
pub static l_Lean_termThrowErrorAt_________00__closed__2_value: LeanStringObject<14> =
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
            116, 104, 114, 111, 119, 69, 114, 114, 111, 114, 65, 116, 32, 0,
        ],
    };
static mut l_Lean_termThrowErrorAt_________00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowErrorAt_________00__closed__2_value) as *mut LeanObject;
pub static l_Lean_termThrowErrorAt_________00__closed__3_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_termThrowErrorAt_________00__closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_termThrowErrorAt_________00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowErrorAt_________00__closed__3_value) as *mut LeanObject;
pub static l_Lean_termThrowErrorAt_________00__closed__4_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 7,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__12_value) as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_termThrowErrorAt_________00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowErrorAt_________00__closed__4_value) as *mut LeanObject;
pub static l_Lean_termThrowErrorAt_________00__closed__5_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__4_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_termThrowErrorAt_________00__closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_termThrowErrorAt_________00__closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_termThrowErrorAt_________00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowErrorAt_________00__closed__5_value) as *mut LeanObject;
pub static l_Lean_termThrowErrorAt_________00__closed__6_value: LeanStringObject<8> =
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
        m_data: [112, 112, 83, 112, 97, 99, 101, 0],
    };
static mut l_Lean_termThrowErrorAt_________00__closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowErrorAt_________00__closed__6_value) as *mut LeanObject;
pub static l_Lean_termThrowErrorAt_________00__closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_termThrowErrorAt_________00__closed__6_value)
                as *mut LeanObject,
            17761616517784022991 as *mut LeanObject,
        ],
    };
static mut l_Lean_termThrowErrorAt_________00__closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowErrorAt_________00__closed__7_value) as *mut LeanObject;
pub static l_Lean_termThrowErrorAt_________00__closed__8_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_termThrowErrorAt_________00__closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_termThrowErrorAt_________00__closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowErrorAt_________00__closed__8_value) as *mut LeanObject;
pub static l_Lean_termThrowErrorAt_________00__closed__9_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__4_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_termThrowErrorAt_________00__closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_termThrowErrorAt_________00__closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_termThrowErrorAt_________00__closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowErrorAt_________00__closed__9_value) as *mut LeanObject;
pub static l_Lean_termThrowErrorAt_________00__closed__10_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__4_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_termThrowErrorAt_________00__closed__9_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__15_value) as *mut LeanObject,
        ],
    };
static mut l_Lean_termThrowErrorAt_________00__closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowErrorAt_________00__closed__10_value) as *mut LeanObject;
pub static l_Lean_termThrowErrorAt_________00__closed__11_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_termThrowErrorAt_________00__closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_termThrowErrorAt_________00__closed__10_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_termThrowErrorAt_________00__closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowErrorAt_________00__closed__11_value) as *mut LeanObject;
pub static mut l_Lean_termThrowErrorAt________: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_termThrowErrorAt_________00__closed__11_value) as *mut LeanObject;
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__0_value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 116, 101, 114, 112, 111, 108, 97, 116, 101, 100, 83, 116, 114, 75, 105, 110, 100, 0]};
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__0_value) as *mut LeanObject;
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__0_value) as *mut LeanObject,14298422259736409839 as *mut LeanObject] };
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__1_value) as *mut LeanObject;
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__2_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__2_value) as *mut LeanObject;
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__3_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__3_value) as *mut LeanObject;
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__4_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__4_value) as *mut LeanObject;
static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__2_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__3_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__4_value) as *mut LeanObject,12966880221525079621 as *mut LeanObject] };
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5_value) as *mut LeanObject;
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__6_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [76, 101, 97, 110, 46, 116, 104, 114, 111, 119, 69, 114, 114, 111, 114, 0]};
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__6_value) as *mut LeanObject;
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__8_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [116, 104, 114, 111, 119, 69, 114, 114, 111, 114, 0]};
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__8_value) as *mut LeanObject;
static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__9_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__9_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__8_value) as *mut LeanObject,5078008955686056653 as *mut LeanObject] };
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__9: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__9_value) as *mut LeanObject;
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__10_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__9_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__10_value) as *mut LeanObject;
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__11_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__10_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__11: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__11_value) as *mut LeanObject;
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__12_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__12_value) as *mut LeanObject;
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__13_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__12_value) as *mut LeanObject,9855511589286918680 as *mut LeanObject] };
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__13: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__13_value) as *mut LeanObject;
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__14_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [112, 97, 114, 101, 110, 0]};
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__14: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__14_value) as *mut LeanObject;
static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__15_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__15_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__15_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__2_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__15_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__15_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__3_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__15_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__15_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__14_value) as *mut LeanObject,7932075773091973500 as *mut LeanObject] };
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__15: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__15_value) as *mut LeanObject;
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__16_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0]};
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__16: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__16_value) as *mut LeanObject;
static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__17_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__17_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__17_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__2_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__17_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__17_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__3_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__17_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__17_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__16_value) as *mut LeanObject,7306243862518720553 as *mut LeanObject] };
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__17: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__17_value) as *mut LeanObject;
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__18_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__18: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__18_value) as *mut LeanObject;
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__19_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0]};
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__19: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__19_value) as *mut LeanObject;
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__20_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__19_value) as *mut LeanObject,9871775667037945883 as *mut LeanObject] };
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__20: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__20_value) as *mut LeanObject;
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__21_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__21: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__21_value) as *mut LeanObject;
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__22_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__22: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__23_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__23: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__23_value) as *mut LeanObject;
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__24_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__23_value) as *mut LeanObject] };
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__24: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__24_value) as *mut LeanObject;
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__25_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__24_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__25: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__25_value) as *mut LeanObject;
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__26_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [116, 101, 114, 109, 77, 33, 95, 0]};
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__26: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__26_value) as *mut LeanObject;
static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__27_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__27_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__27_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__26_value) as *mut LeanObject,13317951319906582257 as *mut LeanObject] };
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__27: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__27_value) as *mut LeanObject;
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__28_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [109, 33, 0]};
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__28: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__28_value) as *mut LeanObject;
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__29_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__29: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__29_value) as *mut LeanObject;
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__0_value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [76, 101, 97, 110, 46, 116, 104, 114, 111, 119, 69, 114, 114, 111, 114, 65, 116, 0]};
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__0_value) as *mut LeanObject;
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__2_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [116, 104, 114, 111, 119, 69, 114, 114, 111, 114, 65, 116, 0]};
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__2_value) as *mut LeanObject;
static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_termThrowError_____00__closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__2_value) as *mut LeanObject,5209814932049838757 as *mut LeanObject] };
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__3_value) as *mut LeanObject;
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__3_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__4_value) as *mut LeanObject;
pub static l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__5_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__4_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__5_value) as *mut LeanObject;
pub unsafe fn l_Lean_Exception_ctorIdx(mut v_x_1130_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_1130_) == 0 {
        let mut v___x_1131_: *mut LeanObject = core::ptr::null_mut();
        v___x_1131_ = lean_unsigned_to_nat(0);
        return v___x_1131_;
    } else {
        let mut v___x_1132_: *mut LeanObject = core::ptr::null_mut();
        v___x_1132_ = lean_unsigned_to_nat(1);
        return v___x_1132_;
    }
}
pub unsafe fn l_Lean_Exception_ctorIdx___boxed(mut v_x_1133_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1134_: *mut LeanObject = core::ptr::null_mut();
    v_res_1134_ = l_Lean_Exception_ctorIdx(v_x_1133_);
    lean_dec_ref(v_x_1133_);
    return v_res_1134_;
}
pub unsafe fn l_Lean_Exception_ctorElim___redArg(
    mut v_t_1135_: *mut LeanObject,
    mut v_k_1136_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_1135_) == 0 {
        let mut v_ref_1137_: *mut LeanObject = core::ptr::null_mut();
        let mut v_msg_1138_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1139_: *mut LeanObject = core::ptr::null_mut();
        v_ref_1137_ = lean_ctor_get(v_t_1135_, 0);
        lean_inc(v_ref_1137_);
        v_msg_1138_ = lean_ctor_get(v_t_1135_, 1);
        lean_inc_ref(v_msg_1138_);
        lean_dec_ref_known(v_t_1135_, 2);
        v___x_1139_ = lean_apply_2(v_k_1136_, v_ref_1137_, v_msg_1138_);
        return v___x_1139_;
    } else {
        let mut v_id_1140_: *mut LeanObject = core::ptr::null_mut();
        let mut v_extra_1141_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1142_: *mut LeanObject = core::ptr::null_mut();
        v_id_1140_ = lean_ctor_get(v_t_1135_, 0);
        lean_inc(v_id_1140_);
        v_extra_1141_ = lean_ctor_get(v_t_1135_, 1);
        lean_inc(v_extra_1141_);
        lean_dec_ref_known(v_t_1135_, 2);
        v___x_1142_ = lean_apply_2(v_k_1136_, v_id_1140_, v_extra_1141_);
        return v___x_1142_;
    }
}
pub unsafe fn l_Lean_Exception_ctorElim(
    mut v_motive_1143_: *mut LeanObject,
    mut v_ctorIdx_1144_: *mut LeanObject,
    mut v_t_1145_: *mut LeanObject,
    mut v_h_1146_: *mut LeanObject,
    mut v_k_1147_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1148_: *mut LeanObject = core::ptr::null_mut();
    v___x_1148_ = l_Lean_Exception_ctorElim___redArg(v_t_1145_, v_k_1147_);
    return v___x_1148_;
}
pub unsafe fn l_Lean_Exception_ctorElim___boxed(
    mut v_motive_1149_: *mut LeanObject,
    mut v_ctorIdx_1150_: *mut LeanObject,
    mut v_t_1151_: *mut LeanObject,
    mut v_h_1152_: *mut LeanObject,
    mut v_k_1153_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1154_: *mut LeanObject = core::ptr::null_mut();
    v_res_1154_ = l_Lean_Exception_ctorElim(
        v_motive_1149_,
        v_ctorIdx_1150_,
        v_t_1151_,
        v_h_1152_,
        v_k_1153_,
    );
    lean_dec(v_ctorIdx_1150_);
    return v_res_1154_;
}
pub unsafe fn l_Lean_Exception_error_elim___redArg(
    mut v_t_1155_: *mut LeanObject,
    mut v_error_1156_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1157_: *mut LeanObject = core::ptr::null_mut();
    v___x_1157_ = l_Lean_Exception_ctorElim___redArg(v_t_1155_, v_error_1156_);
    return v___x_1157_;
}
pub unsafe fn l_Lean_Exception_error_elim(
    mut v_motive_1158_: *mut LeanObject,
    mut v_t_1159_: *mut LeanObject,
    mut v_h_1160_: *mut LeanObject,
    mut v_error_1161_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1162_: *mut LeanObject = core::ptr::null_mut();
    v___x_1162_ = l_Lean_Exception_ctorElim___redArg(v_t_1159_, v_error_1161_);
    return v___x_1162_;
}
pub unsafe fn l_Lean_Exception_internal_elim___redArg(
    mut v_t_1163_: *mut LeanObject,
    mut v_internal_1164_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1165_: *mut LeanObject = core::ptr::null_mut();
    v___x_1165_ = l_Lean_Exception_ctorElim___redArg(v_t_1163_, v_internal_1164_);
    return v___x_1165_;
}
pub unsafe fn l_Lean_Exception_internal_elim(
    mut v_motive_1166_: *mut LeanObject,
    mut v_t_1167_: *mut LeanObject,
    mut v_h_1168_: *mut LeanObject,
    mut v_internal_1169_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1170_: *mut LeanObject = core::ptr::null_mut();
    v___x_1170_ = l_Lean_Exception_ctorElim___redArg(v_t_1167_, v_internal_1169_);
    return v___x_1170_;
}
pub unsafe fn l_Lean_Exception_toMessageData(mut v_x_1171_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_1171_) == 0 {
        let mut v_msg_1172_: *mut LeanObject = core::ptr::null_mut();
        v_msg_1172_ = lean_ctor_get(v_x_1171_, 1);
        lean_inc_ref(v_msg_1172_);
        lean_dec_ref_known(v_x_1171_, 2);
        return v_msg_1172_;
    } else {
        let mut v_id_1173_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1174_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1175_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1176_: *mut LeanObject = core::ptr::null_mut();
        v_id_1173_ = lean_ctor_get(v_x_1171_, 0);
        lean_inc(v_id_1173_);
        lean_dec_ref_known(v_x_1171_, 2);
        v___x_1174_ = l_Lean_InternalExceptionId_toString(v_id_1173_);
        v___x_1175_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_1175_, 0, v___x_1174_);
        v___x_1176_ = l_Lean_MessageData_ofFormat(v___x_1175_);
        return v___x_1176_;
    }
}
pub unsafe fn l_Lean_Exception_hasSyntheticSorry(mut v_x_1177_: *mut LeanObject) -> u8 {
    if lean_obj_tag(v_x_1177_) == 0 {
        let mut v_msg_1178_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1179_: u8 = 0;
        v_msg_1178_ = lean_ctor_get(v_x_1177_, 1);
        lean_inc_ref(v_msg_1178_);
        lean_dec_ref_known(v_x_1177_, 2);
        v___x_1179_ = l_Lean_MessageData_hasSyntheticSorry(v_msg_1178_);
        return v___x_1179_;
    } else {
        let mut v___x_1180_: u8 = 0;
        lean_dec_ref(v_x_1177_);
        v___x_1180_ = 0;
        return v___x_1180_;
    }
}
pub unsafe fn l_Lean_Exception_hasSyntheticSorry___boxed(
    mut v_x_1181_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1182_: u8 = 0;
    let mut v_r_1183_: *mut LeanObject = core::ptr::null_mut();
    v_res_1182_ = l_Lean_Exception_hasSyntheticSorry(v_x_1181_);
    v_r_1183_ = lean_box((v_res_1182_) as usize);
    return v_r_1183_;
}
pub unsafe fn l_Lean_Exception_getRef(mut v_x_1184_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_1184_) == 0 {
        let mut v_ref_1185_: *mut LeanObject = core::ptr::null_mut();
        v_ref_1185_ = lean_ctor_get(v_x_1184_, 0);
        lean_inc(v_ref_1185_);
        return v_ref_1185_;
    } else {
        let mut v___x_1186_: *mut LeanObject = core::ptr::null_mut();
        v___x_1186_ = lean_box(0);
        return v___x_1186_;
    }
}
pub unsafe fn l_Lean_Exception_getRef___boxed(mut v_x_1187_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1188_: *mut LeanObject = core::ptr::null_mut();
    v_res_1188_ = l_Lean_Exception_getRef(v_x_1187_);
    lean_dec_ref(v_x_1187_);
    return v_res_1188_;
}
pub unsafe fn _init_l_Lean_instInhabitedException___closed__0() -> *mut LeanObject {
    let mut v___x_1189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1191_: *mut LeanObject = core::ptr::null_mut();
    v___x_1189_ = l_Lean_instInhabitedMessageData_default;
    v___x_1190_ = lean_box(0);
    v___x_1191_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1191_, 0, v___x_1190_);
    lean_ctor_set(v___x_1191_, 1, v___x_1189_);
    return v___x_1191_;
}
pub unsafe fn _init_l_Lean_instInhabitedException() -> *mut LeanObject {
    let mut v___x_1192_: *mut LeanObject = core::ptr::null_mut();
    v___x_1192_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedException___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedException___closed__0_once),
        _init_l_Lean_instInhabitedException___closed__0,
    );
    return v___x_1192_;
}
pub unsafe fn l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg___lam__0(
    mut v_ref_1193_: *mut LeanObject,
    mut v_toPure_1194_: *mut LeanObject,
    mut v_msg_1195_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut LeanObject = core::ptr::null_mut();
    v___x_1196_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1196_, 0, v_ref_1193_);
    lean_ctor_set(v___x_1196_, 1, v_msg_1195_);
    v___x_1197_ = lean_apply_2(v_toPure_1194_, lean_box(0), v___x_1196_);
    return v___x_1197_;
}
pub unsafe fn l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg___lam__1(
    mut v_toPure_1198_: *mut LeanObject,
    mut v_inst_1199_: *mut LeanObject,
    mut v_toBind_1200_: *mut LeanObject,
    mut v_ref_1201_: *mut LeanObject,
    mut v_msg_1202_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut LeanObject = core::ptr::null_mut();
    v___f_1203_ = lean_alloc_closure(
        l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1203_, 0, v_ref_1201_);
    lean_closure_set(v___f_1203_, 1, v_toPure_1198_);
    v___x_1204_ = lean_apply_1(v_inst_1199_, v_msg_1202_);
    v___x_1205_ = lean_apply_4(
        v_toBind_1200_,
        lean_box(0),
        lean_box(0),
        v___x_1204_,
        v___f_1203_,
    );
    return v___x_1205_;
}
pub unsafe fn l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(
    mut v_inst_1206_: *mut LeanObject,
    mut v_inst_1207_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1211_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1208_ = lean_ctor_get(v_inst_1207_, 0);
    lean_inc_ref(v_toApplicative_1208_);
    v_toBind_1209_ = lean_ctor_get(v_inst_1207_, 1);
    lean_inc(v_toBind_1209_);
    lean_dec_ref(v_inst_1207_);
    v_toPure_1210_ = lean_ctor_get(v_toApplicative_1208_, 1);
    lean_inc(v_toPure_1210_);
    lean_dec_ref(v_toApplicative_1208_);
    v___f_1211_ = lean_alloc_closure(
        l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg___lam__1
            as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v___f_1211_, 0, v_toPure_1210_);
    lean_closure_set(v___f_1211_, 1, v_inst_1206_);
    lean_closure_set(v___f_1211_, 2, v_toBind_1209_);
    return v___f_1211_;
}
pub unsafe fn l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad(
    mut v_m_1212_: *mut LeanObject,
    mut v_inst_1213_: *mut LeanObject,
    mut v_inst_1214_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1215_: *mut LeanObject = core::ptr::null_mut();
    v___x_1215_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(
        v_inst_1213_,
        v_inst_1214_,
    );
    return v___x_1215_;
}
pub unsafe fn l_Lean_throwError___redArg___lam__0(
    mut v_toMonadExceptOf_1216_: *mut LeanObject,
    mut v_____x_1217_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_1218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_throw_1220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1223_: u8 = 0;
    let mut v___x_1225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1228_: u8 = 0;
    let mut v_unused_1229_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1218_ = lean_ctor_get(v_____x_1217_, 0);
                v_snd_1219_ = lean_ctor_get(v_____x_1217_, 1);
                v_throw_1220_ = lean_ctor_get(v_toMonadExceptOf_1216_, 0);
                v_isSharedCheck_1228_ = (!lean_is_exclusive(v_toMonadExceptOf_1216_)) as u8;
                if v_isSharedCheck_1228_ == 0 {
                    v_unused_1229_ = lean_ctor_get(v_toMonadExceptOf_1216_, 1);
                    lean_dec(v_unused_1229_);
                    v___x_1222_ = v_toMonadExceptOf_1216_;
                    v_isShared_1223_ = v_isSharedCheck_1228_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_throw_1220_);
                    lean_dec(v_toMonadExceptOf_1216_);
                    v___x_1222_ = lean_box(0);
                    v_isShared_1223_ = v_isSharedCheck_1228_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_snd_1219_);
                lean_inc(v_fst_1218_);
                if v_isShared_1223_ == 0 {
                    lean_ctor_set(v___x_1222_, 1, v_snd_1219_);
                    lean_ctor_set(v___x_1222_, 0, v_fst_1218_);
                    v___x_1225_ = v___x_1222_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1227_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_fst_1218_);
                    lean_ctor_set(v_reuseFailAlloc_1227_, 1, v_snd_1219_);
                    v___x_1225_ = v_reuseFailAlloc_1227_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1226_ = lean_apply_2(v_throw_1220_, lean_box(0), v___x_1225_);
                return v___x_1226_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___redArg___lam__0___boxed(
    mut v_toMonadExceptOf_1230_: *mut LeanObject,
    mut v_____x_1231_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1232_: *mut LeanObject = core::ptr::null_mut();
    v_res_1232_ = l_Lean_throwError___redArg___lam__0(v_toMonadExceptOf_1230_, v_____x_1231_);
    lean_dec_ref(v_____x_1231_);
    return v_res_1232_;
}
pub unsafe fn l_Lean_throwError___redArg___lam__1(
    mut v_toAddErrorMessageContext_1233_: *mut LeanObject,
    mut v_msg_1234_: *mut LeanObject,
    mut v_toBind_1235_: *mut LeanObject,
    mut v___f_1236_: *mut LeanObject,
    mut v_ref_1237_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut LeanObject = core::ptr::null_mut();
    v___x_1238_ = lean_apply_2(v_toAddErrorMessageContext_1233_, v_ref_1237_, v_msg_1234_);
    v___x_1239_ = lean_apply_4(
        v_toBind_1235_,
        lean_box(0),
        lean_box(0),
        v___x_1238_,
        v___f_1236_,
    );
    return v___x_1239_;
}
pub unsafe fn l_Lean_throwError___redArg(
    mut v_inst_1240_: *mut LeanObject,
    mut v_inst_1241_: *mut LeanObject,
    mut v_msg_1242_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toMonadRef_1243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toMonadExceptOf_1245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toAddErrorMessageContext_1246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getRef_1247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut LeanObject = core::ptr::null_mut();
    v_toMonadRef_1243_ = lean_ctor_get(v_inst_1241_, 1);
    lean_inc_ref(v_toMonadRef_1243_);
    v_toBind_1244_ = lean_ctor_get(v_inst_1240_, 1);
    lean_inc_n(v_toBind_1244_, 2);
    lean_dec_ref(v_inst_1240_);
    v_toMonadExceptOf_1245_ = lean_ctor_get(v_inst_1241_, 0);
    lean_inc_ref(v_toMonadExceptOf_1245_);
    v_toAddErrorMessageContext_1246_ = lean_ctor_get(v_inst_1241_, 2);
    lean_inc(v_toAddErrorMessageContext_1246_);
    lean_dec_ref(v_inst_1241_);
    v_getRef_1247_ = lean_ctor_get(v_toMonadRef_1243_, 0);
    lean_inc(v_getRef_1247_);
    lean_dec_ref(v_toMonadRef_1243_);
    v___f_1248_ = lean_alloc_closure(
        l_Lean_throwError___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1248_, 0, v_toMonadExceptOf_1245_);
    v___f_1249_ = lean_alloc_closure(
        l_Lean_throwError___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_1249_, 0, v_toAddErrorMessageContext_1246_);
    lean_closure_set(v___f_1249_, 1, v_msg_1242_);
    lean_closure_set(v___f_1249_, 2, v_toBind_1244_);
    lean_closure_set(v___f_1249_, 3, v___f_1248_);
    v___x_1250_ = lean_apply_4(
        v_toBind_1244_,
        lean_box(0),
        lean_box(0),
        v_getRef_1247_,
        v___f_1249_,
    );
    return v___x_1250_;
}
pub unsafe fn l_Lean_throwError(
    mut v_m_1251_: *mut LeanObject,
    mut v_00_u03b1_1252_: *mut LeanObject,
    mut v_inst_1253_: *mut LeanObject,
    mut v_inst_1254_: *mut LeanObject,
    mut v_msg_1255_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1256_: *mut LeanObject = core::ptr::null_mut();
    v___x_1256_ = l_Lean_throwError___redArg(v_inst_1253_, v_inst_1254_, v_msg_1255_);
    return v___x_1256_;
}
pub unsafe fn _init_l_Lean_unknownIdentifierMessageTag___closed__3() -> *mut LeanObject {
    let mut v___x_1262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut LeanObject = core::ptr::null_mut();
    v___x_1262_ = l_Lean_unknownIdentifierMessageTag___closed__2;
    v___x_1263_ = l_Lean_kindOfErrorName(v___x_1262_);
    return v___x_1263_;
}
pub unsafe fn _init_l_Lean_unknownIdentifierMessageTag() -> *mut LeanObject {
    let mut v___x_1264_: *mut LeanObject = core::ptr::null_mut();
    v___x_1264_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_unknownIdentifierMessageTag___closed__3),
        core::ptr::addr_of_mut!(l_Lean_unknownIdentifierMessageTag___closed__3_once),
        _init_l_Lean_unknownIdentifierMessageTag___closed__3,
    );
    return v___x_1264_;
}
pub unsafe fn l_Lean_throwErrorAt___redArg___lam__0(
    mut v_ref_1265_: *mut LeanObject,
    mut v_withRef_1266_: *mut LeanObject,
    mut v___x_1267_: *mut LeanObject,
    mut v_oldRef_1268_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut LeanObject = core::ptr::null_mut();
    v_ref_1269_ = l_Lean_replaceRef(v_ref_1265_, v_oldRef_1268_);
    v___x_1270_ = lean_apply_3(v_withRef_1266_, lean_box(0), v_ref_1269_, v___x_1267_);
    return v___x_1270_;
}
pub unsafe fn l_Lean_throwErrorAt___redArg___lam__0___boxed(
    mut v_ref_1271_: *mut LeanObject,
    mut v_withRef_1272_: *mut LeanObject,
    mut v___x_1273_: *mut LeanObject,
    mut v_oldRef_1274_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1275_: *mut LeanObject = core::ptr::null_mut();
    v_res_1275_ = l_Lean_throwErrorAt___redArg___lam__0(
        v_ref_1271_,
        v_withRef_1272_,
        v___x_1273_,
        v_oldRef_1274_,
    );
    lean_dec(v_oldRef_1274_);
    lean_dec(v_ref_1271_);
    return v_res_1275_;
}
pub unsafe fn l_Lean_throwErrorAt___redArg(
    mut v_inst_1276_: *mut LeanObject,
    mut v_inst_1277_: *mut LeanObject,
    mut v_ref_1278_: *mut LeanObject,
    mut v_msg_1279_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toMonadRef_1280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getRef_1282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_withRef_1283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: *mut LeanObject = core::ptr::null_mut();
    v_toMonadRef_1280_ = lean_ctor_get(v_inst_1277_, 1);
    v_toBind_1281_ = lean_ctor_get(v_inst_1276_, 1);
    lean_inc(v_toBind_1281_);
    v_getRef_1282_ = lean_ctor_get(v_toMonadRef_1280_, 0);
    lean_inc(v_getRef_1282_);
    v_withRef_1283_ = lean_ctor_get(v_toMonadRef_1280_, 1);
    lean_inc(v_withRef_1283_);
    v___x_1284_ = l_Lean_throwError___redArg(v_inst_1276_, v_inst_1277_, v_msg_1279_);
    v___f_1285_ = lean_alloc_closure(
        l_Lean_throwErrorAt___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_1285_, 0, v_ref_1278_);
    lean_closure_set(v___f_1285_, 1, v_withRef_1283_);
    lean_closure_set(v___f_1285_, 2, v___x_1284_);
    v___x_1286_ = lean_apply_4(
        v_toBind_1281_,
        lean_box(0),
        lean_box(0),
        v_getRef_1282_,
        v___f_1285_,
    );
    return v___x_1286_;
}
pub unsafe fn l_Lean_throwErrorAt(
    mut v_m_1287_: *mut LeanObject,
    mut v_00_u03b1_1288_: *mut LeanObject,
    mut v_inst_1289_: *mut LeanObject,
    mut v_inst_1290_: *mut LeanObject,
    mut v_ref_1291_: *mut LeanObject,
    mut v_msg_1292_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1293_: *mut LeanObject = core::ptr::null_mut();
    v___x_1293_ =
        l_Lean_throwErrorAt___redArg(v_inst_1289_, v_inst_1290_, v_ref_1291_, v_msg_1292_);
    return v___x_1293_;
}
pub unsafe fn l_Lean_throwNamedError___redArg___lam__1(
    mut v_msg_1294_: *mut LeanObject,
    mut v_name_1295_: *mut LeanObject,
    mut v_toAddErrorMessageContext_1296_: *mut LeanObject,
    mut v_toBind_1297_: *mut LeanObject,
    mut v___f_1298_: *mut LeanObject,
    mut v_ref_1299_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_msg_1300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut LeanObject = core::ptr::null_mut();
    v_msg_1300_ = l_Lean_MessageData_tagWithErrorName(v_msg_1294_, v_name_1295_);
    v___x_1301_ = lean_apply_2(v_toAddErrorMessageContext_1296_, v_ref_1299_, v_msg_1300_);
    v___x_1302_ = lean_apply_4(
        v_toBind_1297_,
        lean_box(0),
        lean_box(0),
        v___x_1301_,
        v___f_1298_,
    );
    return v___x_1302_;
}
pub unsafe fn l_Lean_throwNamedError___redArg(
    mut v_inst_1303_: *mut LeanObject,
    mut v_inst_1304_: *mut LeanObject,
    mut v_name_1305_: *mut LeanObject,
    mut v_msg_1306_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toMonadRef_1307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toMonadExceptOf_1309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toAddErrorMessageContext_1310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getRef_1311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut LeanObject = core::ptr::null_mut();
    v_toMonadRef_1307_ = lean_ctor_get(v_inst_1304_, 1);
    lean_inc_ref(v_toMonadRef_1307_);
    v_toBind_1308_ = lean_ctor_get(v_inst_1303_, 1);
    lean_inc_n(v_toBind_1308_, 2);
    lean_dec_ref(v_inst_1303_);
    v_toMonadExceptOf_1309_ = lean_ctor_get(v_inst_1304_, 0);
    lean_inc_ref(v_toMonadExceptOf_1309_);
    v_toAddErrorMessageContext_1310_ = lean_ctor_get(v_inst_1304_, 2);
    lean_inc(v_toAddErrorMessageContext_1310_);
    lean_dec_ref(v_inst_1304_);
    v_getRef_1311_ = lean_ctor_get(v_toMonadRef_1307_, 0);
    lean_inc(v_getRef_1311_);
    lean_dec_ref(v_toMonadRef_1307_);
    v___f_1312_ = lean_alloc_closure(
        l_Lean_throwError___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1312_, 0, v_toMonadExceptOf_1309_);
    v___f_1313_ = lean_alloc_closure(
        l_Lean_throwNamedError___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_1313_, 0, v_msg_1306_);
    lean_closure_set(v___f_1313_, 1, v_name_1305_);
    lean_closure_set(v___f_1313_, 2, v_toAddErrorMessageContext_1310_);
    lean_closure_set(v___f_1313_, 3, v_toBind_1308_);
    lean_closure_set(v___f_1313_, 4, v___f_1312_);
    v___x_1314_ = lean_apply_4(
        v_toBind_1308_,
        lean_box(0),
        lean_box(0),
        v_getRef_1311_,
        v___f_1313_,
    );
    return v___x_1314_;
}
pub unsafe fn l_Lean_throwNamedError(
    mut v_m_1315_: *mut LeanObject,
    mut v_00_u03b1_1316_: *mut LeanObject,
    mut v_inst_1317_: *mut LeanObject,
    mut v_inst_1318_: *mut LeanObject,
    mut v_name_1319_: *mut LeanObject,
    mut v_msg_1320_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1321_: *mut LeanObject = core::ptr::null_mut();
    v___x_1321_ =
        l_Lean_throwNamedError___redArg(v_inst_1317_, v_inst_1318_, v_name_1319_, v_msg_1320_);
    return v___x_1321_;
}
pub unsafe fn l_Lean_throwNamedErrorAt___redArg(
    mut v_inst_1322_: *mut LeanObject,
    mut v_inst_1323_: *mut LeanObject,
    mut v_ref_1324_: *mut LeanObject,
    mut v_name_1325_: *mut LeanObject,
    mut v_msg_1326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toMonadRef_1327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getRef_1329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_withRef_1330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut LeanObject = core::ptr::null_mut();
    v_toMonadRef_1327_ = lean_ctor_get(v_inst_1323_, 1);
    v_toBind_1328_ = lean_ctor_get(v_inst_1322_, 1);
    lean_inc(v_toBind_1328_);
    v_getRef_1329_ = lean_ctor_get(v_toMonadRef_1327_, 0);
    lean_inc(v_getRef_1329_);
    v_withRef_1330_ = lean_ctor_get(v_toMonadRef_1327_, 1);
    lean_inc(v_withRef_1330_);
    v___x_1331_ =
        l_Lean_throwNamedError___redArg(v_inst_1322_, v_inst_1323_, v_name_1325_, v_msg_1326_);
    v___f_1332_ = lean_alloc_closure(
        l_Lean_throwErrorAt___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_1332_, 0, v_ref_1324_);
    lean_closure_set(v___f_1332_, 1, v_withRef_1330_);
    lean_closure_set(v___f_1332_, 2, v___x_1331_);
    v___x_1333_ = lean_apply_4(
        v_toBind_1328_,
        lean_box(0),
        lean_box(0),
        v_getRef_1329_,
        v___f_1332_,
    );
    return v___x_1333_;
}
pub unsafe fn l_Lean_throwNamedErrorAt(
    mut v_m_1334_: *mut LeanObject,
    mut v_00_u03b1_1335_: *mut LeanObject,
    mut v_inst_1336_: *mut LeanObject,
    mut v_inst_1337_: *mut LeanObject,
    mut v_ref_1338_: *mut LeanObject,
    mut v_name_1339_: *mut LeanObject,
    mut v_msg_1340_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1341_: *mut LeanObject = core::ptr::null_mut();
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
-> *mut LeanObject {
    let mut v___x_1342_: *mut LeanObject = core::ptr::null_mut();
    v___x_1342_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_1342_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_1343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: *mut LeanObject = core::ptr::null_mut();
    v___x_1343_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__0_once
        ),
        _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__0,
    );
    v___x_1344_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1344_, 0, v___x_1343_);
    return v___x_1344_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__2()
-> *mut LeanObject {
    let mut v___x_1345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut LeanObject = core::ptr::null_mut();
    v___x_1345_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__1_once
        ),
        _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__1,
    );
    v___x_1346_ = lean_unsigned_to_nat(0);
    v___x_1347_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_1347_, 0, v___x_1346_);
    lean_ctor_set(v___x_1347_, 1, v___x_1346_);
    lean_ctor_set(v___x_1347_, 2, v___x_1346_);
    lean_ctor_set(v___x_1347_, 3, v___x_1346_);
    lean_ctor_set(v___x_1347_, 4, v___x_1345_);
    lean_ctor_set(v___x_1347_, 5, v___x_1345_);
    lean_ctor_set(v___x_1347_, 6, v___x_1345_);
    lean_ctor_set(v___x_1347_, 7, v___x_1345_);
    lean_ctor_set(v___x_1347_, 8, v___x_1345_);
    lean_ctor_set(v___x_1347_, 9, v___x_1345_);
    return v___x_1347_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__3()
-> *mut LeanObject {
    let mut v___x_1348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut LeanObject = core::ptr::null_mut();
    v___x_1348_ = lean_unsigned_to_nat(32);
    v___x_1349_ = lean_mk_empty_array_with_capacity(v___x_1348_);
    v___x_1350_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1350_, 0, v___x_1349_);
    return v___x_1350_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__4()
-> *mut LeanObject {
    let mut v___x_1351_: usize = 0;
    let mut v___x_1352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut LeanObject = core::ptr::null_mut();
    v___x_1351_ = 5usize;
    v___x_1352_ = lean_unsigned_to_nat(0);
    v___x_1353_ = lean_unsigned_to_nat(32);
    v___x_1354_ = lean_mk_empty_array_with_capacity(v___x_1353_);
    v___x_1355_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__3_once
        ),
        _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__3,
    );
    v___x_1356_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_1356_, 0, v___x_1355_);
    lean_ctor_set(v___x_1356_, 1, v___x_1354_);
    lean_ctor_set(v___x_1356_, 2, v___x_1352_);
    lean_ctor_set(v___x_1356_, 3, v___x_1352_);
    lean_ctor_set_usize(v___x_1356_, 4, v___x_1351_);
    return v___x_1356_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__5()
-> *mut LeanObject {
    let mut v___x_1357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut LeanObject = core::ptr::null_mut();
    v___x_1357_ = lean_box(1);
    v___x_1358_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__4_once
        ),
        _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__4,
    );
    v___x_1359_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__1_once
        ),
        _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__1,
    );
    v___x_1360_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1360_, 0, v___x_1359_);
    lean_ctor_set(v___x_1360_, 1, v___x_1358_);
    lean_ctor_set(v___x_1360_, 2, v___x_1357_);
    return v___x_1360_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__7()
-> *mut LeanObject {
    let mut v___x_1362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut LeanObject = core::ptr::null_mut();
    v___x_1362_ = l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__6;
    v___x_1363_ = l_Lean_stringToMessageData(v___x_1362_);
    return v___x_1363_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__9()
-> *mut LeanObject {
    let mut v___x_1365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut LeanObject = core::ptr::null_mut();
    v___x_1365_ = l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__8;
    v___x_1366_ = l_Lean_stringToMessageData(v___x_1365_);
    return v___x_1366_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__11()
-> *mut LeanObject {
    let mut v___x_1368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut LeanObject = core::ptr::null_mut();
    v___x_1368_ = l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__10;
    v___x_1369_ = l_Lean_stringToMessageData(v___x_1368_);
    return v___x_1369_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__13()
-> *mut LeanObject {
    let mut v___x_1371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut LeanObject = core::ptr::null_mut();
    v___x_1371_ = l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__12;
    v___x_1372_ = l_Lean_stringToMessageData(v___x_1371_);
    return v___x_1372_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__15()
-> *mut LeanObject {
    let mut v___x_1374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut LeanObject = core::ptr::null_mut();
    v___x_1374_ = l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__14;
    v___x_1375_ = l_Lean_stringToMessageData(v___x_1374_);
    return v___x_1375_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__17()
-> *mut LeanObject {
    let mut v___x_1377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut LeanObject = core::ptr::null_mut();
    v___x_1377_ = l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__16;
    v___x_1378_ = l_Lean_stringToMessageData(v___x_1377_);
    return v___x_1378_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__19()
-> *mut LeanObject {
    let mut v___x_1380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut LeanObject = core::ptr::null_mut();
    v___x_1380_ = l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__18;
    v___x_1381_ = l_Lean_stringToMessageData(v___x_1380_);
    return v___x_1381_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0(
    mut v_declHint_1382_: *mut LeanObject,
    mut v_toPure_1383_: *mut LeanObject,
    mut v_msg_1384_: *mut LeanObject,
    mut v_env_1385_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1386_: u8 = 0;
    v___x_1386_ = l_Lean_Name_isAnonymous(v_declHint_1382_);
    if v___x_1386_ == 0 {
        let mut v_isExporting_1387_: u8 = 0;
        v_isExporting_1387_ = lean_ctor_get_uint8(
            v_env_1385_,
            (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
        );
        if v_isExporting_1387_ == 0 {
            let mut v___x_1388_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_env_1385_);
            lean_dec(v_declHint_1382_);
            v___x_1388_ = lean_apply_2(v_toPure_1383_, lean_box(0), v_msg_1384_);
            return v___x_1388_;
        } else {
            let mut v___x_1389_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1390_: u8 = 0;
            lean_inc_ref(v_env_1385_);
            v___x_1389_ = l_Lean_Environment_setExporting(v_env_1385_, v___x_1386_);
            lean_inc(v_declHint_1382_);
            lean_inc_ref(v___x_1389_);
            v___x_1390_ =
                l_Lean_Environment_contains(v___x_1389_, v_declHint_1382_, v_isExporting_1387_);
            if v___x_1390_ == 0 {
                let mut v___x_1391_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v___x_1389_);
                lean_dec_ref(v_env_1385_);
                lean_dec(v_declHint_1382_);
                v___x_1391_ = lean_apply_2(v_toPure_1383_, lean_box(0), v_msg_1384_);
                return v___x_1391_;
            } else {
                let mut v___x_1392_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1393_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1394_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1395_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1396_: *mut LeanObject = core::ptr::null_mut();
                let mut v_c_1397_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1398_: *mut LeanObject = core::ptr::null_mut();
                v___x_1392_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__2_once
                    ),
                    _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__2,
                );
                v___x_1393_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__5
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__5_once
                    ),
                    _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__5,
                );
                v___x_1394_ = l_Lean_Options_empty;
                v___x_1395_ = lean_alloc_ctor(0, 4, (0) as u32);
                lean_ctor_set(v___x_1395_, 0, v___x_1389_);
                lean_ctor_set(v___x_1395_, 1, v___x_1392_);
                lean_ctor_set(v___x_1395_, 2, v___x_1393_);
                lean_ctor_set(v___x_1395_, 3, v___x_1394_);
                lean_inc(v_declHint_1382_);
                v___x_1396_ = l_Lean_MessageData_ofConstName(v_declHint_1382_, v___x_1386_);
                v_c_1397_ = lean_alloc_ctor(3, 2, (0) as u32);
                lean_ctor_set(v_c_1397_, 0, v___x_1395_);
                lean_ctor_set(v_c_1397_, 1, v___x_1396_);
                v___x_1398_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1385_, v_declHint_1382_);
                if lean_obj_tag(v___x_1398_) == 0 {
                    let mut v___x_1399_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_1400_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_1401_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_1402_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_1403_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_1404_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_1405_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec_ref(v_env_1385_);
                    lean_dec(v_declHint_1382_);
                    v___x_1399_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__7);
                    v___x_1400_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1400_, 0, v___x_1399_);
                    lean_ctor_set(v___x_1400_, 1, v_c_1397_);
                    v___x_1401_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__9);
                    v___x_1402_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1402_, 0, v___x_1400_);
                    lean_ctor_set(v___x_1402_, 1, v___x_1401_);
                    v___x_1403_ = l_Lean_MessageData_note(v___x_1402_);
                    v___x_1404_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1404_, 0, v_msg_1384_);
                    lean_ctor_set(v___x_1404_, 1, v___x_1403_);
                    v___x_1405_ = lean_apply_2(v_toPure_1383_, lean_box(0), v___x_1404_);
                    return v___x_1405_;
                } else {
                    let mut v_val_1406_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_1407_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_1408_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_1409_: *mut LeanObject = core::ptr::null_mut();
                    let mut v_mod_1410_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_1411_: u8 = 0;
                    v_val_1406_ = lean_ctor_get(v___x_1398_, 0);
                    lean_inc(v_val_1406_);
                    lean_dec_ref_known(v___x_1398_, 1);
                    v___x_1407_ = lean_box(0);
                    v___x_1408_ = l_Lean_Environment_header(v_env_1385_);
                    lean_dec_ref(v_env_1385_);
                    v___x_1409_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1408_);
                    v_mod_1410_ = lean_array_get(v___x_1407_, v___x_1409_, v_val_1406_);
                    lean_dec(v_val_1406_);
                    lean_dec_ref(v___x_1409_);
                    v___x_1411_ = l_Lean_isPrivateName(v_declHint_1382_);
                    lean_dec(v_declHint_1382_);
                    if v___x_1411_ == 0 {
                        let mut v___x_1412_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_1413_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_1414_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_1415_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_1416_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_1417_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_1418_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_1419_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_1420_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_1421_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_1422_: *mut LeanObject = core::ptr::null_mut();
                        v___x_1412_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__11);
                        v___x_1413_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_1413_, 0, v___x_1412_);
                        lean_ctor_set(v___x_1413_, 1, v_c_1397_);
                        v___x_1414_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__13);
                        v___x_1415_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_1415_, 0, v___x_1413_);
                        lean_ctor_set(v___x_1415_, 1, v___x_1414_);
                        v___x_1416_ = l_Lean_MessageData_ofName(v_mod_1410_);
                        v___x_1417_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_1417_, 0, v___x_1415_);
                        lean_ctor_set(v___x_1417_, 1, v___x_1416_);
                        v___x_1418_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__15);
                        v___x_1419_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_1419_, 0, v___x_1417_);
                        lean_ctor_set(v___x_1419_, 1, v___x_1418_);
                        v___x_1420_ = l_Lean_MessageData_note(v___x_1419_);
                        v___x_1421_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_1421_, 0, v_msg_1384_);
                        lean_ctor_set(v___x_1421_, 1, v___x_1420_);
                        v___x_1422_ = lean_apply_2(v_toPure_1383_, lean_box(0), v___x_1421_);
                        return v___x_1422_;
                    } else {
                        let mut v___x_1423_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_1424_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_1425_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_1426_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_1427_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_1428_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_1429_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_1430_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_1431_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_1432_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_1433_: *mut LeanObject = core::ptr::null_mut();
                        v___x_1423_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__7);
                        v___x_1424_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_1424_, 0, v___x_1423_);
                        lean_ctor_set(v___x_1424_, 1, v_c_1397_);
                        v___x_1425_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__17);
                        v___x_1426_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_1426_, 0, v___x_1424_);
                        lean_ctor_set(v___x_1426_, 1, v___x_1425_);
                        v___x_1427_ = l_Lean_MessageData_ofName(v_mod_1410_);
                        v___x_1428_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_1428_, 0, v___x_1426_);
                        lean_ctor_set(v___x_1428_, 1, v___x_1427_);
                        v___x_1429_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0___closed__19);
                        v___x_1430_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_1430_, 0, v___x_1428_);
                        lean_ctor_set(v___x_1430_, 1, v___x_1429_);
                        v___x_1431_ = l_Lean_MessageData_note(v___x_1430_);
                        v___x_1432_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_1432_, 0, v_msg_1384_);
                        lean_ctor_set(v___x_1432_, 1, v___x_1431_);
                        v___x_1433_ = lean_apply_2(v_toPure_1383_, lean_box(0), v___x_1432_);
                        return v___x_1433_;
                    }
                }
            }
        }
    } else {
        let mut v___x_1434_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_env_1385_);
        lean_dec(v_declHint_1382_);
        v___x_1434_ = lean_apply_2(v_toPure_1383_, lean_box(0), v_msg_1384_);
        return v___x_1434_;
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___redArg(
    mut v_inst_1435_: *mut LeanObject,
    mut v_inst_1436_: *mut LeanObject,
    mut v_msg_1437_: *mut LeanObject,
    mut v_declHint_1438_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getEnv_1441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1439_ = lean_ctor_get(v_inst_1435_, 0);
    lean_inc_ref(v_toApplicative_1439_);
    v_toBind_1440_ = lean_ctor_get(v_inst_1435_, 1);
    lean_inc(v_toBind_1440_);
    lean_dec_ref(v_inst_1435_);
    v_getEnv_1441_ = lean_ctor_get(v_inst_1436_, 0);
    lean_inc(v_getEnv_1441_);
    lean_dec_ref(v_inst_1436_);
    v_toPure_1442_ = lean_ctor_get(v_toApplicative_1439_, 1);
    lean_inc(v_toPure_1442_);
    lean_dec_ref(v_toApplicative_1439_);
    v___f_1443_ = lean_alloc_closure(
        l_Lean_mkUnknownIdentifierMessageCore___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_1443_, 0, v_declHint_1438_);
    lean_closure_set(v___f_1443_, 1, v_toPure_1442_);
    lean_closure_set(v___f_1443_, 2, v_msg_1437_);
    v___x_1444_ = lean_apply_4(
        v_toBind_1440_,
        lean_box(0),
        lean_box(0),
        v_getEnv_1441_,
        v___f_1443_,
    );
    return v___x_1444_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore(
    mut v_m_1445_: *mut LeanObject,
    mut v_inst_1446_: *mut LeanObject,
    mut v_inst_1447_: *mut LeanObject,
    mut v_inst_1448_: *mut LeanObject,
    mut v_msg_1449_: *mut LeanObject,
    mut v_declHint_1450_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1451_: *mut LeanObject = core::ptr::null_mut();
    v___x_1451_ = l_Lean_mkUnknownIdentifierMessageCore___redArg(
        v_inst_1446_,
        v_inst_1447_,
        v_msg_1449_,
        v_declHint_1450_,
    );
    return v___x_1451_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___boxed(
    mut v_m_1452_: *mut LeanObject,
    mut v_inst_1453_: *mut LeanObject,
    mut v_inst_1454_: *mut LeanObject,
    mut v_inst_1455_: *mut LeanObject,
    mut v_msg_1456_: *mut LeanObject,
    mut v_declHint_1457_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1458_: *mut LeanObject = core::ptr::null_mut();
    v_res_1458_ = l_Lean_mkUnknownIdentifierMessageCore(
        v_m_1452_,
        v_inst_1453_,
        v_inst_1454_,
        v_inst_1455_,
        v_msg_1456_,
        v_declHint_1457_,
    );
    lean_dec_ref(v_inst_1455_);
    return v_res_1458_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___redArg___lam__0(
    mut v_toPure_1459_: *mut LeanObject,
    mut v_msg_1460_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut LeanObject = core::ptr::null_mut();
    v___x_1461_ = l_Lean_unknownIdentifierMessageTag;
    v___x_1462_ = lean_alloc_ctor(8, 2, (0) as u32);
    lean_ctor_set(v___x_1462_, 0, v___x_1461_);
    lean_ctor_set(v___x_1462_, 1, v_msg_1460_);
    v___x_1463_ = lean_apply_2(v_toPure_1459_, lean_box(0), v___x_1462_);
    return v___x_1463_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___redArg(
    mut v_inst_1464_: *mut LeanObject,
    mut v_inst_1465_: *mut LeanObject,
    mut v_msg_1466_: *mut LeanObject,
    mut v_declHint_1467_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1468_ = lean_ctor_get(v_inst_1464_, 0);
    v_toBind_1469_ = lean_ctor_get(v_inst_1464_, 1);
    lean_inc(v_toBind_1469_);
    v_toPure_1470_ = lean_ctor_get(v_toApplicative_1468_, 1);
    lean_inc(v_toPure_1470_);
    v___x_1471_ = l_Lean_mkUnknownIdentifierMessageCore___redArg(
        v_inst_1464_,
        v_inst_1465_,
        v_msg_1466_,
        v_declHint_1467_,
    );
    v___f_1472_ = lean_alloc_closure(
        l_Lean_mkUnknownIdentifierMessage___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1472_, 0, v_toPure_1470_);
    v___x_1473_ = lean_apply_4(
        v_toBind_1469_,
        lean_box(0),
        lean_box(0),
        v___x_1471_,
        v___f_1472_,
    );
    return v___x_1473_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage(
    mut v_m_1474_: *mut LeanObject,
    mut v_inst_1475_: *mut LeanObject,
    mut v_inst_1476_: *mut LeanObject,
    mut v_inst_1477_: *mut LeanObject,
    mut v_msg_1478_: *mut LeanObject,
    mut v_declHint_1479_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1480_: *mut LeanObject = core::ptr::null_mut();
    v___x_1480_ = l_Lean_mkUnknownIdentifierMessage___redArg(
        v_inst_1475_,
        v_inst_1476_,
        v_msg_1478_,
        v_declHint_1479_,
    );
    return v___x_1480_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___boxed(
    mut v_m_1481_: *mut LeanObject,
    mut v_inst_1482_: *mut LeanObject,
    mut v_inst_1483_: *mut LeanObject,
    mut v_inst_1484_: *mut LeanObject,
    mut v_msg_1485_: *mut LeanObject,
    mut v_declHint_1486_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1487_: *mut LeanObject = core::ptr::null_mut();
    v_res_1487_ = l_Lean_mkUnknownIdentifierMessage(
        v_m_1481_,
        v_inst_1482_,
        v_inst_1483_,
        v_inst_1484_,
        v_msg_1485_,
        v_declHint_1486_,
    );
    lean_dec_ref(v_inst_1484_);
    return v_res_1487_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___redArg___lam__0(
    mut v_inst_1488_: *mut LeanObject,
    mut v_inst_1489_: *mut LeanObject,
    mut v_ref_1490_: *mut LeanObject,
    mut v_____do__lift_1491_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1492_: *mut LeanObject = core::ptr::null_mut();
    v___x_1492_ = l_Lean_throwErrorAt___redArg(
        v_inst_1488_,
        v_inst_1489_,
        v_ref_1490_,
        v_____do__lift_1491_,
    );
    return v___x_1492_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___redArg(
    mut v_inst_1493_: *mut LeanObject,
    mut v_inst_1494_: *mut LeanObject,
    mut v_inst_1495_: *mut LeanObject,
    mut v_ref_1496_: *mut LeanObject,
    mut v_msg_1497_: *mut LeanObject,
    mut v_declHint_1498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_1499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_1499_ = lean_ctor_get(v_inst_1493_, 1);
    lean_inc(v_toBind_1499_);
    lean_inc_ref(v_inst_1493_);
    v___f_1500_ = lean_alloc_closure(
        l_Lean_throwUnknownIdentifierAt___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_1500_, 0, v_inst_1493_);
    lean_closure_set(v___f_1500_, 1, v_inst_1495_);
    lean_closure_set(v___f_1500_, 2, v_ref_1496_);
    v___x_1501_ = l_Lean_mkUnknownIdentifierMessage___redArg(
        v_inst_1493_,
        v_inst_1494_,
        v_msg_1497_,
        v_declHint_1498_,
    );
    v___x_1502_ = lean_apply_4(
        v_toBind_1499_,
        lean_box(0),
        lean_box(0),
        v___x_1501_,
        v___f_1500_,
    );
    return v___x_1502_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt(
    mut v_m_1503_: *mut LeanObject,
    mut v_00_u03b1_1504_: *mut LeanObject,
    mut v_inst_1505_: *mut LeanObject,
    mut v_inst_1506_: *mut LeanObject,
    mut v_inst_1507_: *mut LeanObject,
    mut v_ref_1508_: *mut LeanObject,
    mut v_msg_1509_: *mut LeanObject,
    mut v_declHint_1510_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1511_: *mut LeanObject = core::ptr::null_mut();
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
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___redArg___closed__1() -> *mut LeanObject {
    let mut v___x_1513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut LeanObject = core::ptr::null_mut();
    v___x_1513_ = l_Lean_throwUnknownConstantAt___redArg___closed__0;
    v___x_1514_ = l_Lean_stringToMessageData(v___x_1513_);
    return v___x_1514_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___redArg___closed__3() -> *mut LeanObject {
    let mut v___x_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut LeanObject = core::ptr::null_mut();
    v___x_1516_ = l_Lean_throwUnknownConstantAt___redArg___closed__2;
    v___x_1517_ = l_Lean_stringToMessageData(v___x_1516_);
    return v___x_1517_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___redArg(
    mut v_inst_1518_: *mut LeanObject,
    mut v_inst_1519_: *mut LeanObject,
    mut v_inst_1520_: *mut LeanObject,
    mut v_ref_1521_: *mut LeanObject,
    mut v_constName_1522_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: u8 = 0;
    let mut v___x_1525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut LeanObject = core::ptr::null_mut();
    v___x_1523_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___redArg___closed__1_once),
        _init_l_Lean_throwUnknownConstantAt___redArg___closed__1,
    );
    v___x_1524_ = 0;
    lean_inc(v_constName_1522_);
    v___x_1525_ = l_Lean_MessageData_ofConstName(v_constName_1522_, v___x_1524_);
    v___x_1526_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_1526_, 0, v___x_1523_);
    lean_ctor_set(v___x_1526_, 1, v___x_1525_);
    v___x_1527_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___redArg___closed__3),
        core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___redArg___closed__3_once),
        _init_l_Lean_throwUnknownConstantAt___redArg___closed__3,
    );
    v___x_1528_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_1528_, 0, v___x_1526_);
    lean_ctor_set(v___x_1528_, 1, v___x_1527_);
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
    mut v_m_1530_: *mut LeanObject,
    mut v_00_u03b1_1531_: *mut LeanObject,
    mut v_inst_1532_: *mut LeanObject,
    mut v_inst_1533_: *mut LeanObject,
    mut v_inst_1534_: *mut LeanObject,
    mut v_ref_1535_: *mut LeanObject,
    mut v_constName_1536_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1537_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_inst_1538_: *mut LeanObject,
    mut v_inst_1539_: *mut LeanObject,
    mut v_inst_1540_: *mut LeanObject,
    mut v_constName_1541_: *mut LeanObject,
    mut v_____do__lift_1542_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1543_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_inst_1544_: *mut LeanObject,
    mut v_inst_1545_: *mut LeanObject,
    mut v_inst_1546_: *mut LeanObject,
    mut v_constName_1547_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toMonadRef_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getRef_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut LeanObject = core::ptr::null_mut();
    v_toMonadRef_1548_ = lean_ctor_get(v_inst_1546_, 1);
    v_toBind_1549_ = lean_ctor_get(v_inst_1544_, 1);
    lean_inc(v_toBind_1549_);
    v_getRef_1550_ = lean_ctor_get(v_toMonadRef_1548_, 0);
    lean_inc(v_getRef_1550_);
    v___f_1551_ = lean_alloc_closure(
        l_Lean_throwUnknownConstant___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_1551_, 0, v_inst_1544_);
    lean_closure_set(v___f_1551_, 1, v_inst_1545_);
    lean_closure_set(v___f_1551_, 2, v_inst_1546_);
    lean_closure_set(v___f_1551_, 3, v_constName_1547_);
    v___x_1552_ = lean_apply_4(
        v_toBind_1549_,
        lean_box(0),
        lean_box(0),
        v_getRef_1550_,
        v___f_1551_,
    );
    return v___x_1552_;
}
pub unsafe fn l_Lean_throwUnknownConstant(
    mut v_m_1553_: *mut LeanObject,
    mut v_00_u03b1_1554_: *mut LeanObject,
    mut v_inst_1555_: *mut LeanObject,
    mut v_inst_1556_: *mut LeanObject,
    mut v_inst_1557_: *mut LeanObject,
    mut v_constName_1558_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1559_: *mut LeanObject = core::ptr::null_mut();
    v___x_1559_ = l_Lean_throwUnknownConstant___redArg(
        v_inst_1555_,
        v_inst_1556_,
        v_inst_1557_,
        v_constName_1558_,
    );
    return v___x_1559_;
}
pub unsafe fn l_Lean_ofExcept___redArg(
    mut v_inst_1560_: *mut LeanObject,
    mut v_inst_1561_: *mut LeanObject,
    mut v_inst_1562_: *mut LeanObject,
    mut v_x_1563_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1563_) == 0 {
        let mut v_a_1564_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1565_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1566_: *mut LeanObject = core::ptr::null_mut();
        v_a_1564_ = lean_ctor_get(v_x_1563_, 0);
        lean_inc(v_a_1564_);
        lean_dec_ref_known(v_x_1563_, 1);
        v___x_1565_ = lean_apply_1(v_inst_1562_, v_a_1564_);
        v___x_1566_ = l_Lean_throwError___redArg(v_inst_1560_, v_inst_1561_, v___x_1565_);
        return v___x_1566_;
    } else {
        let mut v_toApplicative_1567_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_1568_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_1569_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1570_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_1567_ = lean_ctor_get(v_inst_1560_, 0);
        lean_inc_ref(v_toApplicative_1567_);
        lean_dec_ref(v_inst_1562_);
        lean_dec_ref(v_inst_1561_);
        lean_dec_ref(v_inst_1560_);
        v_toPure_1568_ = lean_ctor_get(v_toApplicative_1567_, 1);
        lean_inc(v_toPure_1568_);
        lean_dec_ref(v_toApplicative_1567_);
        v_a_1569_ = lean_ctor_get(v_x_1563_, 0);
        lean_inc(v_a_1569_);
        lean_dec_ref_known(v_x_1563_, 1);
        v___x_1570_ = lean_apply_2(v_toPure_1568_, lean_box(0), v_a_1569_);
        return v___x_1570_;
    }
}
pub unsafe fn l_Lean_ofExcept(
    mut v_m_1571_: *mut LeanObject,
    mut v_00_u03b5_1572_: *mut LeanObject,
    mut v_00_u03b1_1573_: *mut LeanObject,
    mut v_inst_1574_: *mut LeanObject,
    mut v_inst_1575_: *mut LeanObject,
    mut v_inst_1576_: *mut LeanObject,
    mut v_x_1577_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1578_: *mut LeanObject = core::ptr::null_mut();
    v___x_1578_ = l_Lean_ofExcept___redArg(v_inst_1574_, v_inst_1575_, v_inst_1576_, v_x_1577_);
    return v___x_1578_;
}
pub unsafe fn l___private_Lean_Exception_0__Lean_initFn_00___x40_Lean_Exception_2633972168____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut LeanObject = core::ptr::null_mut();
    v___x_1583_ = l___private_Lean_Exception_0__Lean_initFn___closed__1_00___x40_Lean_Exception_2633972168____hygCtx___hyg_2_;
    v___x_1584_ = l_Lean_registerInternalExceptionId(v___x_1583_);
    return v___x_1584_;
}
pub unsafe fn l___private_Lean_Exception_0__Lean_initFn_00___x40_Lean_Exception_2633972168____hygCtx___hyg_2____boxed(
    mut v_a_1585_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1586_: *mut LeanObject = core::ptr::null_mut();
    v_res_1586_ = l___private_Lean_Exception_0__Lean_initFn_00___x40_Lean_Exception_2633972168____hygCtx___hyg_2_();
    return v_res_1586_;
}
pub unsafe fn _init_l_Lean_throwInterruptException___redArg___closed__0() -> *mut LeanObject {
    let mut v___x_1587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut LeanObject = core::ptr::null_mut();
    v___x_1587_ = lean_box(0);
    v___x_1588_ = l_Lean_interruptExceptionId;
    v___x_1589_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1589_, 0, v___x_1588_);
    lean_ctor_set(v___x_1589_, 1, v___x_1587_);
    return v___x_1589_;
}
pub unsafe fn l_Lean_throwInterruptException___redArg(
    mut v_inst_1590_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toMonadExceptOf_1591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_throw_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut LeanObject = core::ptr::null_mut();
    v_toMonadExceptOf_1591_ = lean_ctor_get(v_inst_1590_, 0);
    lean_inc_ref(v_toMonadExceptOf_1591_);
    lean_dec_ref(v_inst_1590_);
    v_throw_1592_ = lean_ctor_get(v_toMonadExceptOf_1591_, 0);
    lean_inc(v_throw_1592_);
    lean_dec_ref(v_toMonadExceptOf_1591_);
    v___x_1593_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_throwInterruptException___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_throwInterruptException___redArg___closed__0_once),
        _init_l_Lean_throwInterruptException___redArg___closed__0,
    );
    v___x_1594_ = lean_apply_2(v_throw_1592_, lean_box(0), v___x_1593_);
    return v___x_1594_;
}
pub unsafe fn l_Lean_throwInterruptException(
    mut v_m_1595_: *mut LeanObject,
    mut v_00_u03b1_1596_: *mut LeanObject,
    mut v_inst_1597_: *mut LeanObject,
    mut v_inst_1598_: *mut LeanObject,
    mut v_inst_1599_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1600_: *mut LeanObject = core::ptr::null_mut();
    v___x_1600_ = l_Lean_throwInterruptException___redArg(v_inst_1598_);
    return v___x_1600_;
}
pub unsafe fn l_Lean_throwInterruptException___boxed(
    mut v_m_1601_: *mut LeanObject,
    mut v_00_u03b1_1602_: *mut LeanObject,
    mut v_inst_1603_: *mut LeanObject,
    mut v_inst_1604_: *mut LeanObject,
    mut v_inst_1605_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1606_: *mut LeanObject = core::ptr::null_mut();
    v_res_1606_ = l_Lean_throwInterruptException(
        v_m_1601_,
        v_00_u03b1_1602_,
        v_inst_1603_,
        v_inst_1604_,
        v_inst_1605_,
    );
    lean_dec(v_inst_1605_);
    lean_dec_ref(v_inst_1603_);
    return v_res_1606_;
}
pub unsafe fn l_Lean_Exception_isInterrupt(mut v_x_1607_: *mut LeanObject) -> u8 {
    if lean_obj_tag(v_x_1607_) == 1 {
        let mut v_id_1608_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1609_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1610_: u8 = 0;
        v_id_1608_ = lean_ctor_get(v_x_1607_, 0);
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
    mut v_x_1612_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1613_: u8 = 0;
    let mut v_r_1614_: *mut LeanObject = core::ptr::null_mut();
    v_res_1613_ = l_Lean_Exception_isInterrupt(v_x_1612_);
    lean_dec_ref(v_x_1612_);
    v_r_1614_ = lean_box((v_res_1613_) as usize);
    return v_r_1614_;
}
pub unsafe fn l_Lean_throwKernelException___redArg___lam__0(
    mut v_ex_1615_: *mut LeanObject,
    mut v_inst_1616_: *mut LeanObject,
    mut v_inst_1617_: *mut LeanObject,
    mut v_____do__lift_1618_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut LeanObject = core::ptr::null_mut();
    v___x_1619_ = l_Lean_Kernel_Exception_toMessageData(v_ex_1615_, v_____do__lift_1618_);
    v___x_1620_ = l_Lean_throwError___redArg(v_inst_1616_, v_inst_1617_, v___x_1619_);
    return v___x_1620_;
}
pub unsafe fn l_Lean_throwKernelException___redArg___lam__1(
    mut v_toBind_1621_: *mut LeanObject,
    mut v_inst_1622_: *mut LeanObject,
    mut v___f_1623_: *mut LeanObject,
    mut v_____r_1624_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1625_: *mut LeanObject = core::ptr::null_mut();
    v___x_1625_ = lean_apply_4(
        v_toBind_1621_,
        lean_box(0),
        lean_box(0),
        v_inst_1622_,
        v___f_1623_,
    );
    return v___x_1625_;
}
pub unsafe fn l_Lean_throwKernelException___redArg(
    mut v_inst_1626_: *mut LeanObject,
    mut v_inst_1627_: *mut LeanObject,
    mut v_inst_1628_: *mut LeanObject,
    mut v_ex_1629_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_1630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1631_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_1630_ = lean_ctor_get(v_inst_1626_, 1);
    lean_inc(v_toBind_1630_);
    lean_inc_ref(v_inst_1627_);
    lean_inc(v_ex_1629_);
    v___f_1631_ = lean_alloc_closure(
        l_Lean_throwKernelException___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_1631_, 0, v_ex_1629_);
    lean_closure_set(v___f_1631_, 1, v_inst_1626_);
    lean_closure_set(v___f_1631_, 2, v_inst_1627_);
    if lean_obj_tag(v_ex_1629_) == 16 {
        let mut v___f_1632_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1633_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1634_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v_toBind_1630_);
        v___f_1632_ = lean_alloc_closure(
            l_Lean_throwKernelException___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            3,
        );
        lean_closure_set(v___f_1632_, 0, v_toBind_1630_);
        lean_closure_set(v___f_1632_, 1, v_inst_1628_);
        lean_closure_set(v___f_1632_, 2, v___f_1631_);
        v___x_1633_ = l_Lean_throwInterruptException___redArg(v_inst_1627_);
        v___x_1634_ = lean_apply_4(
            v_toBind_1630_,
            lean_box(0),
            lean_box(0),
            v___x_1633_,
            v___f_1632_,
        );
        return v___x_1634_;
    } else {
        let mut v___x_1635_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_ex_1629_);
        lean_dec_ref(v_inst_1627_);
        v___x_1635_ = lean_apply_4(
            v_toBind_1630_,
            lean_box(0),
            lean_box(0),
            v_inst_1628_,
            v___f_1631_,
        );
        return v___x_1635_;
    }
}
pub unsafe fn l_Lean_throwKernelException(
    mut v_m_1636_: *mut LeanObject,
    mut v_00_u03b1_1637_: *mut LeanObject,
    mut v_inst_1638_: *mut LeanObject,
    mut v_inst_1639_: *mut LeanObject,
    mut v_inst_1640_: *mut LeanObject,
    mut v_ex_1641_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1642_: *mut LeanObject = core::ptr::null_mut();
    v___x_1642_ =
        l_Lean_throwKernelException___redArg(v_inst_1638_, v_inst_1639_, v_inst_1640_, v_ex_1641_);
    return v___x_1642_;
}
pub unsafe fn l_Lean_ofExceptKernelException___redArg(
    mut v_inst_1643_: *mut LeanObject,
    mut v_inst_1644_: *mut LeanObject,
    mut v_inst_1645_: *mut LeanObject,
    mut v_x_1646_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1646_) == 0 {
        let mut v_a_1647_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1648_: *mut LeanObject = core::ptr::null_mut();
        v_a_1647_ = lean_ctor_get(v_x_1646_, 0);
        lean_inc(v_a_1647_);
        lean_dec_ref_known(v_x_1646_, 1);
        v___x_1648_ = l_Lean_throwKernelException___redArg(
            v_inst_1643_,
            v_inst_1644_,
            v_inst_1645_,
            v_a_1647_,
        );
        return v___x_1648_;
    } else {
        let mut v_toApplicative_1649_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_1650_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_1651_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1652_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_1649_ = lean_ctor_get(v_inst_1643_, 0);
        lean_inc_ref(v_toApplicative_1649_);
        lean_dec(v_inst_1645_);
        lean_dec_ref(v_inst_1644_);
        lean_dec_ref(v_inst_1643_);
        v_toPure_1650_ = lean_ctor_get(v_toApplicative_1649_, 1);
        lean_inc(v_toPure_1650_);
        lean_dec_ref(v_toApplicative_1649_);
        v_a_1651_ = lean_ctor_get(v_x_1646_, 0);
        lean_inc(v_a_1651_);
        lean_dec_ref_known(v_x_1646_, 1);
        v___x_1652_ = lean_apply_2(v_toPure_1650_, lean_box(0), v_a_1651_);
        return v___x_1652_;
    }
}
pub unsafe fn l_Lean_ofExceptKernelException(
    mut v_m_1653_: *mut LeanObject,
    mut v_00_u03b1_1654_: *mut LeanObject,
    mut v_inst_1655_: *mut LeanObject,
    mut v_inst_1656_: *mut LeanObject,
    mut v_inst_1657_: *mut LeanObject,
    mut v_x_1658_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1659_: *mut LeanObject = core::ptr::null_mut();
    v___x_1659_ = l_Lean_ofExceptKernelException___redArg(
        v_inst_1655_,
        v_inst_1656_,
        v_inst_1657_,
        v_x_1658_,
    );
    return v___x_1659_;
}
pub unsafe fn l_Lean_instMonadRecDepthReaderT___redArg___lam__0(
    mut v_inst_1660_: *mut LeanObject,
    mut v_00_u03b1_1661_: *mut LeanObject,
    mut v_d_1662_: *mut LeanObject,
    mut v_x_1663_: *mut LeanObject,
    mut v_ctx_1664_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_withRecDepth_1665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut LeanObject = core::ptr::null_mut();
    v_withRecDepth_1665_ = lean_ctor_get(v_inst_1660_, 0);
    lean_inc(v_withRecDepth_1665_);
    lean_dec_ref(v_inst_1660_);
    v___x_1666_ = lean_apply_1(v_x_1663_, v_ctx_1664_);
    v___x_1667_ = lean_apply_3(v_withRecDepth_1665_, lean_box(0), v_d_1662_, v___x_1666_);
    return v___x_1667_;
}
pub unsafe fn l_Lean_instMonadRecDepthReaderT___redArg___lam__1(
    mut v_inst_1668_: *mut LeanObject,
    mut v_x_1669_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_getRecDepth_1670_: *mut LeanObject = core::ptr::null_mut();
    v_getRecDepth_1670_ = lean_ctor_get(v_inst_1668_, 1);
    lean_inc(v_getRecDepth_1670_);
    return v_getRecDepth_1670_;
}
pub unsafe fn l_Lean_instMonadRecDepthReaderT___redArg___lam__1___boxed(
    mut v_inst_1671_: *mut LeanObject,
    mut v_x_1672_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1673_: *mut LeanObject = core::ptr::null_mut();
    v_res_1673_ = l_Lean_instMonadRecDepthReaderT___redArg___lam__1(v_inst_1671_, v_x_1672_);
    lean_dec(v_x_1672_);
    lean_dec_ref(v_inst_1671_);
    return v_res_1673_;
}
pub unsafe fn l_Lean_instMonadRecDepthReaderT___redArg___lam__2(
    mut v_inst_1674_: *mut LeanObject,
    mut v_x_1675_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_getMaxRecDepth_1676_: *mut LeanObject = core::ptr::null_mut();
    v_getMaxRecDepth_1676_ = lean_ctor_get(v_inst_1674_, 2);
    lean_inc(v_getMaxRecDepth_1676_);
    return v_getMaxRecDepth_1676_;
}
pub unsafe fn l_Lean_instMonadRecDepthReaderT___redArg___lam__2___boxed(
    mut v_inst_1677_: *mut LeanObject,
    mut v_x_1678_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1679_: *mut LeanObject = core::ptr::null_mut();
    v_res_1679_ = l_Lean_instMonadRecDepthReaderT___redArg___lam__2(v_inst_1677_, v_x_1678_);
    lean_dec(v_x_1678_);
    lean_dec_ref(v_inst_1677_);
    return v_res_1679_;
}
pub unsafe fn l_Lean_instMonadRecDepthReaderT___redArg(
    mut v_inst_1680_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref_n(v_inst_1680_, 2);
    v___f_1681_ = lean_alloc_closure(
        l_Lean_instMonadRecDepthReaderT___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_1681_, 0, v_inst_1680_);
    v___f_1682_ = lean_alloc_closure(
        l_Lean_instMonadRecDepthReaderT___redArg___lam__1___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1682_, 0, v_inst_1680_);
    v___f_1683_ = lean_alloc_closure(
        l_Lean_instMonadRecDepthReaderT___redArg___lam__2___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1683_, 0, v_inst_1680_);
    v___x_1684_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1684_, 0, v___f_1681_);
    lean_ctor_set(v___x_1684_, 1, v___f_1682_);
    lean_ctor_set(v___x_1684_, 2, v___f_1683_);
    return v___x_1684_;
}
pub unsafe fn l_Lean_instMonadRecDepthReaderT(
    mut v_m_1685_: *mut LeanObject,
    mut v_00_u03c1_1686_: *mut LeanObject,
    mut v_inst_1687_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1688_: *mut LeanObject = core::ptr::null_mut();
    v___x_1688_ = l_Lean_instMonadRecDepthReaderT___redArg(v_inst_1687_);
    return v___x_1688_;
}
pub unsafe fn l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__1___redArg(
    mut v_inst_1689_: *mut LeanObject,
    mut v_d_1690_: *mut LeanObject,
    mut v_x_1691_: *mut LeanObject,
    mut v_ctx_1692_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_withRecDepth_1693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut LeanObject = core::ptr::null_mut();
    v_withRecDepth_1693_ = lean_ctor_get(v_inst_1689_, 0);
    lean_inc(v_withRecDepth_1693_);
    lean_dec_ref(v_inst_1689_);
    lean_inc(v_ctx_1692_);
    v___x_1694_ = lean_apply_1(v_x_1691_, v_ctx_1692_);
    v___x_1695_ = lean_apply_3(v_withRecDepth_1693_, lean_box(0), v_d_1690_, v___x_1694_);
    return v___x_1695_;
}
pub unsafe fn l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__1___redArg___boxed(
    mut v_inst_1696_: *mut LeanObject,
    mut v_d_1697_: *mut LeanObject,
    mut v_x_1698_: *mut LeanObject,
    mut v_ctx_1699_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1700_: *mut LeanObject = core::ptr::null_mut();
    v_res_1700_ = l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__1___redArg(
        v_inst_1696_,
        v_d_1697_,
        v_x_1698_,
        v_ctx_1699_,
    );
    lean_dec(v_ctx_1699_);
    return v_res_1700_;
}
pub unsafe fn l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__1(
    mut v_m_1701_: *mut LeanObject,
    mut v_00_u03c9_1702_: *mut LeanObject,
    mut v_00_u03c3_1703_: *mut LeanObject,
    mut v_inst_1704_: *mut LeanObject,
    mut v_00_u03b1_1705_: *mut LeanObject,
    mut v_d_1706_: *mut LeanObject,
    mut v_x_1707_: *mut LeanObject,
    mut v_ctx_1708_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_withRecDepth_1709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut LeanObject = core::ptr::null_mut();
    v_withRecDepth_1709_ = lean_ctor_get(v_inst_1704_, 0);
    lean_inc(v_withRecDepth_1709_);
    lean_dec_ref(v_inst_1704_);
    lean_inc(v_ctx_1708_);
    v___x_1710_ = lean_apply_1(v_x_1707_, v_ctx_1708_);
    v___x_1711_ = lean_apply_3(v_withRecDepth_1709_, lean_box(0), v_d_1706_, v___x_1710_);
    return v___x_1711_;
}
pub unsafe fn l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__1___boxed(
    mut v_m_1712_: *mut LeanObject,
    mut v_00_u03c9_1713_: *mut LeanObject,
    mut v_00_u03c3_1714_: *mut LeanObject,
    mut v_inst_1715_: *mut LeanObject,
    mut v_00_u03b1_1716_: *mut LeanObject,
    mut v_d_1717_: *mut LeanObject,
    mut v_x_1718_: *mut LeanObject,
    mut v_ctx_1719_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1720_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_ctx_1719_);
    return v_res_1720_;
}
pub unsafe fn l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__3___redArg(
    mut v_inst_1721_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_getRecDepth_1722_: *mut LeanObject = core::ptr::null_mut();
    v_getRecDepth_1722_ = lean_ctor_get(v_inst_1721_, 1);
    lean_inc(v_getRecDepth_1722_);
    return v_getRecDepth_1722_;
}
pub unsafe fn l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__3___redArg___boxed(
    mut v_inst_1723_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1724_: *mut LeanObject = core::ptr::null_mut();
    v_res_1724_ = l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__3___redArg(v_inst_1723_);
    lean_dec_ref(v_inst_1723_);
    return v_res_1724_;
}
pub unsafe fn l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__3(
    mut v_m_1725_: *mut LeanObject,
    mut v_00_u03c9_1726_: *mut LeanObject,
    mut v_00_u03c3_1727_: *mut LeanObject,
    mut v_inst_1728_: *mut LeanObject,
    mut v_x_1729_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_getRecDepth_1730_: *mut LeanObject = core::ptr::null_mut();
    v_getRecDepth_1730_ = lean_ctor_get(v_inst_1728_, 1);
    lean_inc(v_getRecDepth_1730_);
    return v_getRecDepth_1730_;
}
pub unsafe fn l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__3___boxed(
    mut v_m_1731_: *mut LeanObject,
    mut v_00_u03c9_1732_: *mut LeanObject,
    mut v_00_u03c3_1733_: *mut LeanObject,
    mut v_inst_1734_: *mut LeanObject,
    mut v_x_1735_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1736_: *mut LeanObject = core::ptr::null_mut();
    v_res_1736_ = l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__3(
        v_m_1731_,
        v_00_u03c9_1732_,
        v_00_u03c3_1733_,
        v_inst_1734_,
        v_x_1735_,
    );
    lean_dec(v_x_1735_);
    lean_dec_ref(v_inst_1734_);
    return v_res_1736_;
}
pub unsafe fn l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__5___redArg(
    mut v_inst_1737_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_getMaxRecDepth_1738_: *mut LeanObject = core::ptr::null_mut();
    v_getMaxRecDepth_1738_ = lean_ctor_get(v_inst_1737_, 2);
    lean_inc(v_getMaxRecDepth_1738_);
    return v_getMaxRecDepth_1738_;
}
pub unsafe fn l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__5___redArg___boxed(
    mut v_inst_1739_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1740_: *mut LeanObject = core::ptr::null_mut();
    v_res_1740_ = l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__5___redArg(v_inst_1739_);
    lean_dec_ref(v_inst_1739_);
    return v_res_1740_;
}
pub unsafe fn l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__5(
    mut v_m_1741_: *mut LeanObject,
    mut v_00_u03c9_1742_: *mut LeanObject,
    mut v_00_u03c3_1743_: *mut LeanObject,
    mut v_inst_1744_: *mut LeanObject,
    mut v_x_1745_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_getMaxRecDepth_1746_: *mut LeanObject = core::ptr::null_mut();
    v_getMaxRecDepth_1746_ = lean_ctor_get(v_inst_1744_, 2);
    lean_inc(v_getMaxRecDepth_1746_);
    return v_getMaxRecDepth_1746_;
}
pub unsafe fn l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__5___boxed(
    mut v_m_1747_: *mut LeanObject,
    mut v_00_u03c9_1748_: *mut LeanObject,
    mut v_00_u03c3_1749_: *mut LeanObject,
    mut v_inst_1750_: *mut LeanObject,
    mut v_x_1751_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1752_: *mut LeanObject = core::ptr::null_mut();
    v_res_1752_ = l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__5(
        v_m_1747_,
        v_00_u03c9_1748_,
        v_00_u03c3_1749_,
        v_inst_1750_,
        v_x_1751_,
    );
    lean_dec(v_x_1751_);
    lean_dec_ref(v_inst_1750_);
    return v_res_1752_;
}
pub unsafe fn l_Lean_instMonadRecDepthStateRefT_x27OfMonad___redArg(
    mut v_inst_1753_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref_n(v_inst_1753_, 2);
    v___x_1754_ = lean_alloc_closure(
        l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__1___boxed as *mut core::ffi::c_void,
        8,
        4,
    );
    lean_closure_set(v___x_1754_, 0, lean_box(0));
    lean_closure_set(v___x_1754_, 1, lean_box(0));
    lean_closure_set(v___x_1754_, 2, lean_box(0));
    lean_closure_set(v___x_1754_, 3, v_inst_1753_);
    v___x_1755_ = lean_alloc_closure(
        l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__3___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___x_1755_, 0, lean_box(0));
    lean_closure_set(v___x_1755_, 1, lean_box(0));
    lean_closure_set(v___x_1755_, 2, lean_box(0));
    lean_closure_set(v___x_1755_, 3, v_inst_1753_);
    v___x_1756_ = lean_alloc_closure(
        l_Lean_instMonadRecDepthStateRefT_x27OfMonad___aux__5___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___x_1756_, 0, lean_box(0));
    lean_closure_set(v___x_1756_, 1, lean_box(0));
    lean_closure_set(v___x_1756_, 2, lean_box(0));
    lean_closure_set(v___x_1756_, 3, v_inst_1753_);
    v___x_1757_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1757_, 0, v___x_1754_);
    lean_ctor_set(v___x_1757_, 1, v___x_1755_);
    lean_ctor_set(v___x_1757_, 2, v___x_1756_);
    return v___x_1757_;
}
pub unsafe fn l_Lean_instMonadRecDepthStateRefT_x27OfMonad(
    mut v_m_1758_: *mut LeanObject,
    mut v_00_u03c9_1759_: *mut LeanObject,
    mut v_00_u03c3_1760_: *mut LeanObject,
    mut v_inst_1761_: *mut LeanObject,
    mut v_inst_1762_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1763_: *mut LeanObject = core::ptr::null_mut();
    v___x_1763_ = l_Lean_instMonadRecDepthStateRefT_x27OfMonad___redArg(v_inst_1762_);
    return v___x_1763_;
}
pub unsafe fn l_Lean_instMonadRecDepthStateRefT_x27OfMonad___boxed(
    mut v_m_1764_: *mut LeanObject,
    mut v_00_u03c9_1765_: *mut LeanObject,
    mut v_00_u03c3_1766_: *mut LeanObject,
    mut v_inst_1767_: *mut LeanObject,
    mut v_inst_1768_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1769_: *mut LeanObject = core::ptr::null_mut();
    v_res_1769_ = l_Lean_instMonadRecDepthStateRefT_x27OfMonad(
        v_m_1764_,
        v_00_u03c9_1765_,
        v_00_u03c3_1766_,
        v_inst_1767_,
        v_inst_1768_,
    );
    lean_dec_ref(v_inst_1767_);
    return v_res_1769_;
}
pub unsafe fn l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__1___redArg(
    mut v_inst_1770_: *mut LeanObject,
    mut v_a_1771_: *mut LeanObject,
    mut v_a_1772_: *mut LeanObject,
    mut v_a_1773_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_withRecDepth_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut LeanObject = core::ptr::null_mut();
    v_withRecDepth_1774_ = lean_ctor_get(v_inst_1770_, 0);
    lean_inc(v_withRecDepth_1774_);
    lean_dec_ref(v_inst_1770_);
    lean_inc(v_a_1773_);
    v___x_1775_ = lean_apply_1(v_a_1772_, v_a_1773_);
    v___x_1776_ = lean_apply_3(v_withRecDepth_1774_, lean_box(0), v_a_1771_, v___x_1775_);
    return v___x_1776_;
}
pub unsafe fn l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__1___redArg___boxed(
    mut v_inst_1777_: *mut LeanObject,
    mut v_a_1778_: *mut LeanObject,
    mut v_a_1779_: *mut LeanObject,
    mut v_a_1780_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1781_: *mut LeanObject = core::ptr::null_mut();
    v_res_1781_ = l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__1___redArg(
        v_inst_1777_,
        v_a_1778_,
        v_a_1779_,
        v_a_1780_,
    );
    lean_dec(v_a_1780_);
    return v_res_1781_;
}
pub unsafe fn l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__1(
    mut v_00_u03b1_1782_: *mut LeanObject,
    mut v_m_1783_: *mut LeanObject,
    mut v_00_u03c9_1784_: *mut LeanObject,
    mut v_00_u03b2_1785_: *mut LeanObject,
    mut v_inst_1786_: *mut LeanObject,
    mut v_inst_1787_: *mut LeanObject,
    mut v_inst_1788_: *mut LeanObject,
    mut v_inst_1789_: *mut LeanObject,
    mut v_00_u03b1_1790_: *mut LeanObject,
    mut v_a_1791_: *mut LeanObject,
    mut v_a_1792_: *mut LeanObject,
    mut v_a_1793_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_withRecDepth_1794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut LeanObject = core::ptr::null_mut();
    v_withRecDepth_1794_ = lean_ctor_get(v_inst_1789_, 0);
    lean_inc(v_withRecDepth_1794_);
    lean_dec_ref(v_inst_1789_);
    lean_inc(v_a_1793_);
    v___x_1795_ = lean_apply_1(v_a_1792_, v_a_1793_);
    v___x_1796_ = lean_apply_3(v_withRecDepth_1794_, lean_box(0), v_a_1791_, v___x_1795_);
    return v___x_1796_;
}
pub unsafe fn l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__1___boxed(
    mut v_00_u03b1_1797_: *mut LeanObject,
    mut v_m_1798_: *mut LeanObject,
    mut v_00_u03c9_1799_: *mut LeanObject,
    mut v_00_u03b2_1800_: *mut LeanObject,
    mut v_inst_1801_: *mut LeanObject,
    mut v_inst_1802_: *mut LeanObject,
    mut v_inst_1803_: *mut LeanObject,
    mut v_inst_1804_: *mut LeanObject,
    mut v_00_u03b1_1805_: *mut LeanObject,
    mut v_a_1806_: *mut LeanObject,
    mut v_a_1807_: *mut LeanObject,
    mut v_a_1808_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1809_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_1808_);
    lean_dec_ref(v_inst_1802_);
    lean_dec_ref(v_inst_1801_);
    return v_res_1809_;
}
pub unsafe fn l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__3___redArg(
    mut v_inst_1810_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_getRecDepth_1811_: *mut LeanObject = core::ptr::null_mut();
    v_getRecDepth_1811_ = lean_ctor_get(v_inst_1810_, 1);
    lean_inc(v_getRecDepth_1811_);
    return v_getRecDepth_1811_;
}
pub unsafe fn l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__3___redArg___boxed(
    mut v_inst_1812_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1813_: *mut LeanObject = core::ptr::null_mut();
    v_res_1813_ = l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__3___redArg(v_inst_1812_);
    lean_dec_ref(v_inst_1812_);
    return v_res_1813_;
}
pub unsafe fn l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__3(
    mut v_00_u03b1_1814_: *mut LeanObject,
    mut v_m_1815_: *mut LeanObject,
    mut v_00_u03c9_1816_: *mut LeanObject,
    mut v_00_u03b2_1817_: *mut LeanObject,
    mut v_inst_1818_: *mut LeanObject,
    mut v_inst_1819_: *mut LeanObject,
    mut v_inst_1820_: *mut LeanObject,
    mut v_inst_1821_: *mut LeanObject,
    mut v_a_1822_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_getRecDepth_1823_: *mut LeanObject = core::ptr::null_mut();
    v_getRecDepth_1823_ = lean_ctor_get(v_inst_1821_, 1);
    lean_inc(v_getRecDepth_1823_);
    return v_getRecDepth_1823_;
}
pub unsafe fn l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__3___boxed(
    mut v_00_u03b1_1824_: *mut LeanObject,
    mut v_m_1825_: *mut LeanObject,
    mut v_00_u03c9_1826_: *mut LeanObject,
    mut v_00_u03b2_1827_: *mut LeanObject,
    mut v_inst_1828_: *mut LeanObject,
    mut v_inst_1829_: *mut LeanObject,
    mut v_inst_1830_: *mut LeanObject,
    mut v_inst_1831_: *mut LeanObject,
    mut v_a_1832_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1833_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_1832_);
    lean_dec_ref(v_inst_1831_);
    lean_dec_ref(v_inst_1829_);
    lean_dec_ref(v_inst_1828_);
    return v_res_1833_;
}
pub unsafe fn l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__5___redArg(
    mut v_inst_1834_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_getMaxRecDepth_1835_: *mut LeanObject = core::ptr::null_mut();
    v_getMaxRecDepth_1835_ = lean_ctor_get(v_inst_1834_, 2);
    lean_inc(v_getMaxRecDepth_1835_);
    return v_getMaxRecDepth_1835_;
}
pub unsafe fn l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__5___redArg___boxed(
    mut v_inst_1836_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1837_: *mut LeanObject = core::ptr::null_mut();
    v_res_1837_ = l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__5___redArg(v_inst_1836_);
    lean_dec_ref(v_inst_1836_);
    return v_res_1837_;
}
pub unsafe fn l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__5(
    mut v_00_u03b1_1838_: *mut LeanObject,
    mut v_m_1839_: *mut LeanObject,
    mut v_00_u03c9_1840_: *mut LeanObject,
    mut v_00_u03b2_1841_: *mut LeanObject,
    mut v_inst_1842_: *mut LeanObject,
    mut v_inst_1843_: *mut LeanObject,
    mut v_inst_1844_: *mut LeanObject,
    mut v_inst_1845_: *mut LeanObject,
    mut v_a_1846_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_getMaxRecDepth_1847_: *mut LeanObject = core::ptr::null_mut();
    v_getMaxRecDepth_1847_ = lean_ctor_get(v_inst_1845_, 2);
    lean_inc(v_getMaxRecDepth_1847_);
    return v_getMaxRecDepth_1847_;
}
pub unsafe fn l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__5___boxed(
    mut v_00_u03b1_1848_: *mut LeanObject,
    mut v_m_1849_: *mut LeanObject,
    mut v_00_u03c9_1850_: *mut LeanObject,
    mut v_00_u03b2_1851_: *mut LeanObject,
    mut v_inst_1852_: *mut LeanObject,
    mut v_inst_1853_: *mut LeanObject,
    mut v_inst_1854_: *mut LeanObject,
    mut v_inst_1855_: *mut LeanObject,
    mut v_a_1856_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1857_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_1856_);
    lean_dec_ref(v_inst_1855_);
    lean_dec_ref(v_inst_1853_);
    lean_dec_ref(v_inst_1852_);
    return v_res_1857_;
}
pub unsafe fn l_Lean_instMonadRecDepthMonadCacheTOfMonad___redArg(
    mut v_inst_1858_: *mut LeanObject,
    mut v_inst_1859_: *mut LeanObject,
    mut v_inst_1860_: *mut LeanObject,
    mut v_inst_1861_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref_n(v_inst_1861_, 2);
    lean_inc_ref_n(v_inst_1859_, 2);
    lean_inc_ref_n(v_inst_1858_, 2);
    v___x_1862_ = lean_alloc_closure(
        l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__1___boxed as *mut core::ffi::c_void,
        12,
        8,
    );
    lean_closure_set(v___x_1862_, 0, lean_box(0));
    lean_closure_set(v___x_1862_, 1, lean_box(0));
    lean_closure_set(v___x_1862_, 2, lean_box(0));
    lean_closure_set(v___x_1862_, 3, lean_box(0));
    lean_closure_set(v___x_1862_, 4, v_inst_1858_);
    lean_closure_set(v___x_1862_, 5, v_inst_1859_);
    lean_closure_set(v___x_1862_, 6, v_inst_1860_);
    lean_closure_set(v___x_1862_, 7, v_inst_1861_);
    v___x_1863_ = lean_alloc_closure(
        l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__3___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    lean_closure_set(v___x_1863_, 0, lean_box(0));
    lean_closure_set(v___x_1863_, 1, lean_box(0));
    lean_closure_set(v___x_1863_, 2, lean_box(0));
    lean_closure_set(v___x_1863_, 3, lean_box(0));
    lean_closure_set(v___x_1863_, 4, v_inst_1858_);
    lean_closure_set(v___x_1863_, 5, v_inst_1859_);
    lean_closure_set(v___x_1863_, 6, v_inst_1860_);
    lean_closure_set(v___x_1863_, 7, v_inst_1861_);
    v___x_1864_ = lean_alloc_closure(
        l_Lean_instMonadRecDepthMonadCacheTOfMonad___aux__5___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    lean_closure_set(v___x_1864_, 0, lean_box(0));
    lean_closure_set(v___x_1864_, 1, lean_box(0));
    lean_closure_set(v___x_1864_, 2, lean_box(0));
    lean_closure_set(v___x_1864_, 3, lean_box(0));
    lean_closure_set(v___x_1864_, 4, v_inst_1858_);
    lean_closure_set(v___x_1864_, 5, v_inst_1859_);
    lean_closure_set(v___x_1864_, 6, v_inst_1860_);
    lean_closure_set(v___x_1864_, 7, v_inst_1861_);
    v___x_1865_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1865_, 0, v___x_1862_);
    lean_ctor_set(v___x_1865_, 1, v___x_1863_);
    lean_ctor_set(v___x_1865_, 2, v___x_1864_);
    return v___x_1865_;
}
pub unsafe fn l_Lean_instMonadRecDepthMonadCacheTOfMonad(
    mut v_00_u03b1_1866_: *mut LeanObject,
    mut v_m_1867_: *mut LeanObject,
    mut v_00_u03c9_1868_: *mut LeanObject,
    mut v_00_u03b2_1869_: *mut LeanObject,
    mut v_inst_1870_: *mut LeanObject,
    mut v_inst_1871_: *mut LeanObject,
    mut v_inst_1872_: *mut LeanObject,
    mut v_inst_1873_: *mut LeanObject,
    mut v_inst_1874_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1875_: *mut LeanObject = core::ptr::null_mut();
    v___x_1875_ = l_Lean_instMonadRecDepthMonadCacheTOfMonad___redArg(
        v_inst_1870_,
        v_inst_1871_,
        v_inst_1873_,
        v_inst_1874_,
    );
    return v___x_1875_;
}
pub unsafe fn l_Lean_instMonadRecDepthMonadCacheTOfMonad___boxed(
    mut v_00_u03b1_1876_: *mut LeanObject,
    mut v_m_1877_: *mut LeanObject,
    mut v_00_u03c9_1878_: *mut LeanObject,
    mut v_00_u03b2_1879_: *mut LeanObject,
    mut v_inst_1880_: *mut LeanObject,
    mut v_inst_1881_: *mut LeanObject,
    mut v_inst_1882_: *mut LeanObject,
    mut v_inst_1883_: *mut LeanObject,
    mut v_inst_1884_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1885_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_inst_1882_);
    return v_res_1885_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___redArg___closed__3() -> *mut LeanObject {
    let mut v___x_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut LeanObject = core::ptr::null_mut();
    v___x_1891_ = l_Lean_maxRecDepthErrorMessage;
    v___x_1892_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_1892_, 0, v___x_1891_);
    return v___x_1892_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___redArg___closed__4() -> *mut LeanObject {
    let mut v___x_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut LeanObject = core::ptr::null_mut();
    v___x_1893_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___redArg___closed__3),
        core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___redArg___closed__3_once),
        _init_l_Lean_throwMaxRecDepthAt___redArg___closed__3,
    );
    v___x_1894_ = l_Lean_MessageData_ofFormat(v___x_1893_);
    return v___x_1894_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___redArg___closed__5() -> *mut LeanObject {
    let mut v___x_1895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut LeanObject = core::ptr::null_mut();
    v___x_1895_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___redArg___closed__4),
        core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___redArg___closed__4_once),
        _init_l_Lean_throwMaxRecDepthAt___redArg___closed__4,
    );
    v___x_1896_ = l_Lean_throwMaxRecDepthAt___redArg___closed__2;
    v___x_1897_ = lean_alloc_ctor(8, 2, (0) as u32);
    lean_ctor_set(v___x_1897_, 0, v___x_1896_);
    lean_ctor_set(v___x_1897_, 1, v___x_1895_);
    return v___x_1897_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___redArg(
    mut v_inst_1898_: *mut LeanObject,
    mut v_ref_1899_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toMonadExceptOf_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_throw_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1904_: u8 = 0;
    let mut v___x_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1910_: u8 = 0;
    let mut v_unused_1911_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toMonadExceptOf_1900_ = lean_ctor_get(v_inst_1898_, 0);
                lean_inc_ref(v_toMonadExceptOf_1900_);
                lean_dec_ref(v_inst_1898_);
                v_throw_1901_ = lean_ctor_get(v_toMonadExceptOf_1900_, 0);
                v_isSharedCheck_1910_ = (!lean_is_exclusive(v_toMonadExceptOf_1900_)) as u8;
                if v_isSharedCheck_1910_ == 0 {
                    v_unused_1911_ = lean_ctor_get(v_toMonadExceptOf_1900_, 1);
                    lean_dec(v_unused_1911_);
                    v___x_1903_ = v_toMonadExceptOf_1900_;
                    v_isShared_1904_ = v_isSharedCheck_1910_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_throw_1901_);
                    lean_dec(v_toMonadExceptOf_1900_);
                    v___x_1903_ = lean_box(0);
                    v_isShared_1904_ = v_isSharedCheck_1910_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1905_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___redArg___closed__5),
                    core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___redArg___closed__5_once),
                    _init_l_Lean_throwMaxRecDepthAt___redArg___closed__5,
                );
                if v_isShared_1904_ == 0 {
                    lean_ctor_set(v___x_1903_, 1, v___x_1905_);
                    lean_ctor_set(v___x_1903_, 0, v_ref_1899_);
                    v___x_1907_ = v___x_1903_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1909_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1909_, 0, v_ref_1899_);
                    lean_ctor_set(v_reuseFailAlloc_1909_, 1, v___x_1905_);
                    v___x_1907_ = v_reuseFailAlloc_1909_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1908_ = lean_apply_2(v_throw_1901_, lean_box(0), v___x_1907_);
                return v___x_1908_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwMaxRecDepthAt(
    mut v_m_1912_: *mut LeanObject,
    mut v_00_u03b1_1913_: *mut LeanObject,
    mut v_inst_1914_: *mut LeanObject,
    mut v_ref_1915_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1916_: *mut LeanObject = core::ptr::null_mut();
    v___x_1916_ = l_Lean_throwMaxRecDepthAt___redArg(v_inst_1914_, v_ref_1915_);
    return v___x_1916_;
}
pub unsafe fn l_Lean_Exception_isMaxRecDepth(mut v_ex_1917_: *mut LeanObject) -> u8 {
    if lean_obj_tag(v_ex_1917_) == 0 {
        let mut v_msg_1918_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1919_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1920_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1921_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1922_: u8 = 0;
        v_msg_1918_ = lean_ctor_get(v_ex_1917_, 1);
        lean_inc_ref(v_msg_1918_);
        lean_dec_ref_known(v_ex_1917_, 2);
        v___x_1919_ = l_Lean_MessageData_stripNestedTags(v_msg_1918_);
        v___x_1920_ = l_Lean_MessageData_kind(v___x_1919_);
        lean_dec_ref(v___x_1919_);
        v___x_1921_ = l_Lean_throwMaxRecDepthAt___redArg___closed__2;
        v___x_1922_ = lean_name_eq(v___x_1920_, v___x_1921_);
        lean_dec(v___x_1920_);
        return v___x_1922_;
    } else {
        let mut v___x_1923_: u8 = 0;
        lean_dec_ref(v_ex_1917_);
        v___x_1923_ = 0;
        return v___x_1923_;
    }
}
pub unsafe fn l_Lean_Exception_isMaxRecDepth___boxed(
    mut v_ex_1924_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1925_: u8 = 0;
    let mut v_r_1926_: *mut LeanObject = core::ptr::null_mut();
    v_res_1925_ = l_Lean_Exception_isMaxRecDepth(v_ex_1924_);
    v_r_1926_ = lean_box((v_res_1925_) as usize);
    return v_r_1926_;
}
pub unsafe fn l_Lean_withIncRecDepth___redArg___lam__0(
    mut v_inst_1927_: *mut LeanObject,
    mut v_____do__lift_1928_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1929_: *mut LeanObject = core::ptr::null_mut();
    v___x_1929_ = l_Lean_throwMaxRecDepthAt___redArg(v_inst_1927_, v_____do__lift_1928_);
    return v___x_1929_;
}
pub unsafe fn l_Lean_withIncRecDepth___redArg___lam__1(
    mut v_curr_1930_: *mut LeanObject,
    mut v_withRecDepth_1931_: *mut LeanObject,
    mut v_x_1932_: *mut LeanObject,
    mut v_inst_1933_: *mut LeanObject,
    mut v_toBind_1934_: *mut LeanObject,
    mut v___f_1935_: *mut LeanObject,
    mut v_max_1936_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: u8 = 0;
    let mut v___x_1943_: u8 = 0;
    let mut v_toMonadRef_1944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getRef_1945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1941_ = lean_unsigned_to_nat(0);
                v___x_1942_ = lean_nat_dec_eq(v_max_1936_, v___x_1941_);
                if v___x_1942_ == 0 {
                    v___x_1943_ = lean_nat_dec_eq(v_curr_1930_, v_max_1936_);
                    if v___x_1943_ == 0 {
                        lean_dec(v___f_1935_);
                        lean_dec(v_toBind_1934_);
                        lean_dec_ref(v_inst_1933_);
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_x_1932_);
                        lean_dec(v_withRecDepth_1931_);
                        v_toMonadRef_1944_ = lean_ctor_get(v_inst_1933_, 1);
                        lean_inc_ref(v_toMonadRef_1944_);
                        lean_dec_ref(v_inst_1933_);
                        v_getRef_1945_ = lean_ctor_get(v_toMonadRef_1944_, 0);
                        lean_inc(v_getRef_1945_);
                        lean_dec_ref(v_toMonadRef_1944_);
                        v___x_1946_ = lean_apply_4(
                            v_toBind_1934_,
                            lean_box(0),
                            lean_box(0),
                            v_getRef_1945_,
                            v___f_1935_,
                        );
                        return v___x_1946_;
                    }
                } else {
                    lean_dec(v___f_1935_);
                    lean_dec(v_toBind_1934_);
                    lean_dec_ref(v_inst_1933_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1938_ = lean_unsigned_to_nat(1);
                v___x_1939_ = lean_nat_add(v_curr_1930_, v___x_1938_);
                v___x_1940_ =
                    lean_apply_3(v_withRecDepth_1931_, lean_box(0), v___x_1939_, v_x_1932_);
                return v___x_1940_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withIncRecDepth___redArg___lam__1___boxed(
    mut v_curr_1947_: *mut LeanObject,
    mut v_withRecDepth_1948_: *mut LeanObject,
    mut v_x_1949_: *mut LeanObject,
    mut v_inst_1950_: *mut LeanObject,
    mut v_toBind_1951_: *mut LeanObject,
    mut v___f_1952_: *mut LeanObject,
    mut v_max_1953_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1954_: *mut LeanObject = core::ptr::null_mut();
    v_res_1954_ = l_Lean_withIncRecDepth___redArg___lam__1(
        v_curr_1947_,
        v_withRecDepth_1948_,
        v_x_1949_,
        v_inst_1950_,
        v_toBind_1951_,
        v___f_1952_,
        v_max_1953_,
    );
    lean_dec(v_max_1953_);
    lean_dec(v_curr_1947_);
    return v_res_1954_;
}
pub unsafe fn l_Lean_withIncRecDepth___redArg___lam__2(
    mut v_withRecDepth_1955_: *mut LeanObject,
    mut v_x_1956_: *mut LeanObject,
    mut v_inst_1957_: *mut LeanObject,
    mut v_toBind_1958_: *mut LeanObject,
    mut v___f_1959_: *mut LeanObject,
    mut v_getMaxRecDepth_1960_: *mut LeanObject,
    mut v_curr_1961_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_toBind_1958_);
    v___f_1962_ = lean_alloc_closure(
        l_Lean_withIncRecDepth___redArg___lam__1___boxed as *mut core::ffi::c_void,
        7,
        6,
    );
    lean_closure_set(v___f_1962_, 0, v_curr_1961_);
    lean_closure_set(v___f_1962_, 1, v_withRecDepth_1955_);
    lean_closure_set(v___f_1962_, 2, v_x_1956_);
    lean_closure_set(v___f_1962_, 3, v_inst_1957_);
    lean_closure_set(v___f_1962_, 4, v_toBind_1958_);
    lean_closure_set(v___f_1962_, 5, v___f_1959_);
    v___x_1963_ = lean_apply_4(
        v_toBind_1958_,
        lean_box(0),
        lean_box(0),
        v_getMaxRecDepth_1960_,
        v___f_1962_,
    );
    return v___x_1963_;
}
pub unsafe fn l_Lean_withIncRecDepth___redArg(
    mut v_inst_1964_: *mut LeanObject,
    mut v_inst_1965_: *mut LeanObject,
    mut v_inst_1966_: *mut LeanObject,
    mut v_x_1967_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_withRecDepth_1969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getRecDepth_1970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getMaxRecDepth_1971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_1968_ = lean_ctor_get(v_inst_1964_, 1);
    lean_inc_n(v_toBind_1968_, 2);
    lean_dec_ref(v_inst_1964_);
    v_withRecDepth_1969_ = lean_ctor_get(v_inst_1966_, 0);
    lean_inc(v_withRecDepth_1969_);
    v_getRecDepth_1970_ = lean_ctor_get(v_inst_1966_, 1);
    lean_inc(v_getRecDepth_1970_);
    v_getMaxRecDepth_1971_ = lean_ctor_get(v_inst_1966_, 2);
    lean_inc(v_getMaxRecDepth_1971_);
    lean_dec_ref(v_inst_1966_);
    lean_inc_ref(v_inst_1965_);
    v___f_1972_ = lean_alloc_closure(
        l_Lean_withIncRecDepth___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1972_, 0, v_inst_1965_);
    v___f_1973_ = lean_alloc_closure(
        l_Lean_withIncRecDepth___redArg___lam__2 as *mut core::ffi::c_void,
        7,
        6,
    );
    lean_closure_set(v___f_1973_, 0, v_withRecDepth_1969_);
    lean_closure_set(v___f_1973_, 1, v_x_1967_);
    lean_closure_set(v___f_1973_, 2, v_inst_1965_);
    lean_closure_set(v___f_1973_, 3, v_toBind_1968_);
    lean_closure_set(v___f_1973_, 4, v___f_1972_);
    lean_closure_set(v___f_1973_, 5, v_getMaxRecDepth_1971_);
    v___x_1974_ = lean_apply_4(
        v_toBind_1968_,
        lean_box(0),
        lean_box(0),
        v_getRecDepth_1970_,
        v___f_1973_,
    );
    return v___x_1974_;
}
pub unsafe fn l_Lean_withIncRecDepth(
    mut v_m_1975_: *mut LeanObject,
    mut v_00_u03b1_1976_: *mut LeanObject,
    mut v_inst_1977_: *mut LeanObject,
    mut v_inst_1978_: *mut LeanObject,
    mut v_inst_1979_: *mut LeanObject,
    mut v_x_1980_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_1981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_withRecDepth_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getRecDepth_1983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getMaxRecDepth_1984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_1981_ = lean_ctor_get(v_inst_1977_, 1);
    lean_inc_n(v_toBind_1981_, 2);
    lean_dec_ref(v_inst_1977_);
    v_withRecDepth_1982_ = lean_ctor_get(v_inst_1979_, 0);
    lean_inc(v_withRecDepth_1982_);
    v_getRecDepth_1983_ = lean_ctor_get(v_inst_1979_, 1);
    lean_inc(v_getRecDepth_1983_);
    v_getMaxRecDepth_1984_ = lean_ctor_get(v_inst_1979_, 2);
    lean_inc(v_getMaxRecDepth_1984_);
    lean_dec_ref(v_inst_1979_);
    lean_inc_ref(v_inst_1978_);
    v___f_1985_ = lean_alloc_closure(
        l_Lean_withIncRecDepth___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1985_, 0, v_inst_1978_);
    v___f_1986_ = lean_alloc_closure(
        l_Lean_withIncRecDepth___redArg___lam__2 as *mut core::ffi::c_void,
        7,
        6,
    );
    lean_closure_set(v___f_1986_, 0, v_withRecDepth_1982_);
    lean_closure_set(v___f_1986_, 1, v_x_1980_);
    lean_closure_set(v___f_1986_, 2, v_inst_1978_);
    lean_closure_set(v___f_1986_, 3, v_toBind_1981_);
    lean_closure_set(v___f_1986_, 4, v___f_1985_);
    lean_closure_set(v___f_1986_, 5, v_getMaxRecDepth_1984_);
    v___x_1987_ = lean_apply_4(
        v_toBind_1981_,
        lean_box(0),
        lean_box(0),
        v_getRecDepth_1983_,
        v___f_1986_,
    );
    return v___x_1987_;
}
pub unsafe fn _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__7()
-> *mut LeanObject {
    let mut v___x_2071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut LeanObject = core::ptr::null_mut();
    v___x_2071_ =
        l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__6;
    v___x_2072_ = l_String_toRawSubstring_x27(v___x_2071_);
    return v___x_2072_;
}
pub unsafe fn _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__22()
-> *mut LeanObject {
    let mut v___x_2103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut LeanObject = core::ptr::null_mut();
    v___x_2103_ =
        l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__21;
    v___x_2104_ = l_String_toRawSubstring_x27(v___x_2103_);
    return v___x_2104_;
}
pub unsafe fn l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1(
    mut v_x_2118_: *mut LeanObject,
    mut v_a_2119_: *mut LeanObject,
    mut v_a_2120_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: u8 = 0;
    v___x_2121_ = l_Lean_termThrowError_____00__closed__2;
    lean_inc(v_x_2118_);
    v___x_2122_ = l_Lean_Syntax_isOfKind(v_x_2118_, v___x_2121_);
    if v___x_2122_ == 0 {
        let mut v___x_2123_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2124_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_2118_);
        v___x_2123_ = lean_box(1);
        v___x_2124_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_2124_, 0, v___x_2123_);
        lean_ctor_set(v___x_2124_, 1, v_a_2120_);
        return v___x_2124_;
    } else {
        let mut v___x_2125_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2126_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2127_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2128_: u8 = 0;
        v___x_2125_ = lean_unsigned_to_nat(1);
        v___x_2126_ = l_Lean_Syntax_getArg(v_x_2118_, v___x_2125_);
        lean_dec(v_x_2118_);
        v___x_2127_ =
            l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__1;
        lean_inc(v___x_2126_);
        v___x_2128_ = l_Lean_Syntax_isOfKind(v___x_2126_, v___x_2127_);
        if v___x_2128_ == 0 {
            let mut v_quotContext_2129_: *mut LeanObject = core::ptr::null_mut();
            let mut v_currMacroScope_2130_: *mut LeanObject = core::ptr::null_mut();
            let mut v_ref_2131_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2132_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2133_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2134_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2135_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2136_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2137_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2138_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2139_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2140_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2141_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2142_: *mut LeanObject = core::ptr::null_mut();
            v_quotContext_2129_ = lean_ctor_get(v_a_2119_, 1);
            v_currMacroScope_2130_ = lean_ctor_get(v_a_2119_, 2);
            v_ref_2131_ = lean_ctor_get(v_a_2119_, 5);
            v___x_2132_ = l_Lean_SourceInfo_fromRef(v_ref_2131_, v___x_2128_);
            v___x_2133_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5;
            v___x_2134_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__7), core::ptr::addr_of_mut!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__7_once), _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__7);
            v___x_2135_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__9;
            lean_inc(v_currMacroScope_2130_);
            lean_inc(v_quotContext_2129_);
            v___x_2136_ =
                l_Lean_addMacroScope(v_quotContext_2129_, v___x_2135_, v_currMacroScope_2130_);
            v___x_2137_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__11;
            lean_inc_n(v___x_2132_, 2);
            v___x_2138_ = lean_alloc_ctor(3, 4, (0) as u32);
            lean_ctor_set(v___x_2138_, 0, v___x_2132_);
            lean_ctor_set(v___x_2138_, 1, v___x_2134_);
            lean_ctor_set(v___x_2138_, 2, v___x_2136_);
            lean_ctor_set(v___x_2138_, 3, v___x_2137_);
            v___x_2139_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__13;
            v___x_2140_ = l_Lean_Syntax_node1(v___x_2132_, v___x_2139_, v___x_2126_);
            v___x_2141_ = l_Lean_Syntax_node2(v___x_2132_, v___x_2133_, v___x_2138_, v___x_2140_);
            v___x_2142_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_2142_, 0, v___x_2141_);
            lean_ctor_set(v___x_2142_, 1, v_a_2120_);
            return v___x_2142_;
        } else {
            let mut v_quotContext_2143_: *mut LeanObject = core::ptr::null_mut();
            let mut v_currMacroScope_2144_: *mut LeanObject = core::ptr::null_mut();
            let mut v_ref_2145_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2146_: u8 = 0;
            let mut v___x_2147_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2148_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2149_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2150_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2151_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2152_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2153_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2154_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2155_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2156_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2157_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2158_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2159_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2160_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2161_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2162_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2163_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2164_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2165_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2166_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2167_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2168_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2169_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2170_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2171_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2172_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2173_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2174_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2175_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2176_: *mut LeanObject = core::ptr::null_mut();
            v_quotContext_2143_ = lean_ctor_get(v_a_2119_, 1);
            v_currMacroScope_2144_ = lean_ctor_get(v_a_2119_, 2);
            v_ref_2145_ = lean_ctor_get(v_a_2119_, 5);
            v___x_2146_ = 0;
            v___x_2147_ = l_Lean_SourceInfo_fromRef(v_ref_2145_, v___x_2146_);
            v___x_2148_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5;
            v___x_2149_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__7), core::ptr::addr_of_mut!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__7_once), _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__7);
            v___x_2150_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__9;
            lean_inc_n(v_currMacroScope_2144_, 2);
            lean_inc_n(v_quotContext_2143_, 2);
            v___x_2151_ =
                l_Lean_addMacroScope(v_quotContext_2143_, v___x_2150_, v_currMacroScope_2144_);
            v___x_2152_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__11;
            lean_inc_n(v___x_2147_, 10);
            v___x_2153_ = lean_alloc_ctor(3, 4, (0) as u32);
            lean_ctor_set(v___x_2153_, 0, v___x_2147_);
            lean_ctor_set(v___x_2153_, 1, v___x_2149_);
            lean_ctor_set(v___x_2153_, 2, v___x_2151_);
            lean_ctor_set(v___x_2153_, 3, v___x_2152_);
            v___x_2154_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__13;
            v___x_2155_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__15;
            v___x_2156_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__17;
            v___x_2157_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__18;
            v___x_2158_ = lean_alloc_ctor(2, 2, (0) as u32);
            lean_ctor_set(v___x_2158_, 0, v___x_2147_);
            lean_ctor_set(v___x_2158_, 1, v___x_2157_);
            v___x_2159_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__20;
            v___x_2160_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__22), core::ptr::addr_of_mut!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__22_once), _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__22);
            v___x_2161_ = lean_box(0);
            v___x_2162_ =
                l_Lean_addMacroScope(v_quotContext_2143_, v___x_2161_, v_currMacroScope_2144_);
            v___x_2163_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__25;
            v___x_2164_ = lean_alloc_ctor(3, 4, (0) as u32);
            lean_ctor_set(v___x_2164_, 0, v___x_2147_);
            lean_ctor_set(v___x_2164_, 1, v___x_2160_);
            lean_ctor_set(v___x_2164_, 2, v___x_2162_);
            lean_ctor_set(v___x_2164_, 3, v___x_2163_);
            v___x_2165_ = l_Lean_Syntax_node1(v___x_2147_, v___x_2159_, v___x_2164_);
            v___x_2166_ = l_Lean_Syntax_node2(v___x_2147_, v___x_2156_, v___x_2158_, v___x_2165_);
            v___x_2167_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__27;
            v___x_2168_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__28;
            v___x_2169_ = lean_alloc_ctor(2, 2, (0) as u32);
            lean_ctor_set(v___x_2169_, 0, v___x_2147_);
            lean_ctor_set(v___x_2169_, 1, v___x_2168_);
            v___x_2170_ = l_Lean_Syntax_node2(v___x_2147_, v___x_2167_, v___x_2169_, v___x_2126_);
            v___x_2171_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__29;
            v___x_2172_ = lean_alloc_ctor(2, 2, (0) as u32);
            lean_ctor_set(v___x_2172_, 0, v___x_2147_);
            lean_ctor_set(v___x_2172_, 1, v___x_2171_);
            v___x_2173_ = l_Lean_Syntax_node3(
                v___x_2147_,
                v___x_2155_,
                v___x_2166_,
                v___x_2170_,
                v___x_2172_,
            );
            v___x_2174_ = l_Lean_Syntax_node1(v___x_2147_, v___x_2154_, v___x_2173_);
            v___x_2175_ = l_Lean_Syntax_node2(v___x_2147_, v___x_2148_, v___x_2153_, v___x_2174_);
            v___x_2176_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_2176_, 0, v___x_2175_);
            lean_ctor_set(v___x_2176_, 1, v_a_2120_);
            return v___x_2176_;
        }
    }
}
pub unsafe fn l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___boxed(
    mut v_x_2177_: *mut LeanObject,
    mut v_a_2178_: *mut LeanObject,
    mut v_a_2179_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2180_: *mut LeanObject = core::ptr::null_mut();
    v_res_2180_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1(
        v_x_2177_, v_a_2178_, v_a_2179_,
    );
    lean_dec_ref(v_a_2178_);
    return v_res_2180_;
}
pub unsafe fn _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__1()
-> *mut LeanObject {
    let mut v___x_2182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut LeanObject = core::ptr::null_mut();
    v___x_2182_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__0;
    v___x_2183_ = l_String_toRawSubstring_x27(v___x_2182_);
    return v___x_2183_;
}
pub unsafe fn l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1(
    mut v_x_2194_: *mut LeanObject,
    mut v_a_2195_: *mut LeanObject,
    mut v_a_2196_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: u8 = 0;
    v___x_2197_ = l_Lean_termThrowErrorAt_________00__closed__1;
    lean_inc(v_x_2194_);
    v___x_2198_ = l_Lean_Syntax_isOfKind(v_x_2194_, v___x_2197_);
    if v___x_2198_ == 0 {
        let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2200_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_2194_);
        v___x_2199_ = lean_box(1);
        v___x_2200_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_2200_, 0, v___x_2199_);
        lean_ctor_set(v___x_2200_, 1, v_a_2196_);
        return v___x_2200_;
    } else {
        let mut v___x_2201_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2202_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2203_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2204_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2205_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2206_: u8 = 0;
        v___x_2201_ = lean_unsigned_to_nat(1);
        v___x_2202_ = l_Lean_Syntax_getArg(v_x_2194_, v___x_2201_);
        v___x_2203_ = lean_unsigned_to_nat(2);
        v___x_2204_ = l_Lean_Syntax_getArg(v_x_2194_, v___x_2203_);
        lean_dec(v_x_2194_);
        v___x_2205_ =
            l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__1;
        lean_inc(v___x_2204_);
        v___x_2206_ = l_Lean_Syntax_isOfKind(v___x_2204_, v___x_2205_);
        if v___x_2206_ == 0 {
            let mut v_quotContext_2207_: *mut LeanObject = core::ptr::null_mut();
            let mut v_currMacroScope_2208_: *mut LeanObject = core::ptr::null_mut();
            let mut v_ref_2209_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2210_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2211_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2212_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2213_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2214_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2215_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2216_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2217_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2218_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2219_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2220_: *mut LeanObject = core::ptr::null_mut();
            v_quotContext_2207_ = lean_ctor_get(v_a_2195_, 1);
            v_currMacroScope_2208_ = lean_ctor_get(v_a_2195_, 2);
            v_ref_2209_ = lean_ctor_get(v_a_2195_, 5);
            v___x_2210_ = l_Lean_SourceInfo_fromRef(v_ref_2209_, v___x_2206_);
            v___x_2211_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5;
            v___x_2212_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__1), core::ptr::addr_of_mut!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__1_once), _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__1);
            v___x_2213_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__3;
            lean_inc(v_currMacroScope_2208_);
            lean_inc(v_quotContext_2207_);
            v___x_2214_ =
                l_Lean_addMacroScope(v_quotContext_2207_, v___x_2213_, v_currMacroScope_2208_);
            v___x_2215_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__5;
            lean_inc_n(v___x_2210_, 2);
            v___x_2216_ = lean_alloc_ctor(3, 4, (0) as u32);
            lean_ctor_set(v___x_2216_, 0, v___x_2210_);
            lean_ctor_set(v___x_2216_, 1, v___x_2212_);
            lean_ctor_set(v___x_2216_, 2, v___x_2214_);
            lean_ctor_set(v___x_2216_, 3, v___x_2215_);
            v___x_2217_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__13;
            v___x_2218_ = l_Lean_Syntax_node2(v___x_2210_, v___x_2217_, v___x_2202_, v___x_2204_);
            v___x_2219_ = l_Lean_Syntax_node2(v___x_2210_, v___x_2211_, v___x_2216_, v___x_2218_);
            v___x_2220_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_2220_, 0, v___x_2219_);
            lean_ctor_set(v___x_2220_, 1, v_a_2196_);
            return v___x_2220_;
        } else {
            let mut v_quotContext_2221_: *mut LeanObject = core::ptr::null_mut();
            let mut v_currMacroScope_2222_: *mut LeanObject = core::ptr::null_mut();
            let mut v_ref_2223_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2224_: u8 = 0;
            let mut v___x_2225_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2226_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2227_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2228_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2229_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2230_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2231_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2232_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2233_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2234_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2235_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2236_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2237_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2238_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2239_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2240_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2241_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2242_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2243_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2244_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2245_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2246_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2247_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2248_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2249_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2250_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2251_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2252_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2253_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2254_: *mut LeanObject = core::ptr::null_mut();
            v_quotContext_2221_ = lean_ctor_get(v_a_2195_, 1);
            v_currMacroScope_2222_ = lean_ctor_get(v_a_2195_, 2);
            v_ref_2223_ = lean_ctor_get(v_a_2195_, 5);
            v___x_2224_ = 0;
            v___x_2225_ = l_Lean_SourceInfo_fromRef(v_ref_2223_, v___x_2224_);
            v___x_2226_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5;
            v___x_2227_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__1), core::ptr::addr_of_mut!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__1_once), _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__1);
            v___x_2228_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__3;
            lean_inc_n(v_currMacroScope_2222_, 2);
            lean_inc_n(v_quotContext_2221_, 2);
            v___x_2229_ =
                l_Lean_addMacroScope(v_quotContext_2221_, v___x_2228_, v_currMacroScope_2222_);
            v___x_2230_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__5;
            lean_inc_n(v___x_2225_, 10);
            v___x_2231_ = lean_alloc_ctor(3, 4, (0) as u32);
            lean_ctor_set(v___x_2231_, 0, v___x_2225_);
            lean_ctor_set(v___x_2231_, 1, v___x_2227_);
            lean_ctor_set(v___x_2231_, 2, v___x_2229_);
            lean_ctor_set(v___x_2231_, 3, v___x_2230_);
            v___x_2232_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__13;
            v___x_2233_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__15;
            v___x_2234_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__17;
            v___x_2235_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__18;
            v___x_2236_ = lean_alloc_ctor(2, 2, (0) as u32);
            lean_ctor_set(v___x_2236_, 0, v___x_2225_);
            lean_ctor_set(v___x_2236_, 1, v___x_2235_);
            v___x_2237_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__20;
            v___x_2238_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__22), core::ptr::addr_of_mut!(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__22_once), _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__22);
            v___x_2239_ = lean_box(0);
            v___x_2240_ =
                l_Lean_addMacroScope(v_quotContext_2221_, v___x_2239_, v_currMacroScope_2222_);
            v___x_2241_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__25;
            v___x_2242_ = lean_alloc_ctor(3, 4, (0) as u32);
            lean_ctor_set(v___x_2242_, 0, v___x_2225_);
            lean_ctor_set(v___x_2242_, 1, v___x_2238_);
            lean_ctor_set(v___x_2242_, 2, v___x_2240_);
            lean_ctor_set(v___x_2242_, 3, v___x_2241_);
            v___x_2243_ = l_Lean_Syntax_node1(v___x_2225_, v___x_2237_, v___x_2242_);
            v___x_2244_ = l_Lean_Syntax_node2(v___x_2225_, v___x_2234_, v___x_2236_, v___x_2243_);
            v___x_2245_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__27;
            v___x_2246_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__28;
            v___x_2247_ = lean_alloc_ctor(2, 2, (0) as u32);
            lean_ctor_set(v___x_2247_, 0, v___x_2225_);
            lean_ctor_set(v___x_2247_, 1, v___x_2246_);
            v___x_2248_ = l_Lean_Syntax_node2(v___x_2225_, v___x_2245_, v___x_2247_, v___x_2204_);
            v___x_2249_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__29;
            v___x_2250_ = lean_alloc_ctor(2, 2, (0) as u32);
            lean_ctor_set(v___x_2250_, 0, v___x_2225_);
            lean_ctor_set(v___x_2250_, 1, v___x_2249_);
            v___x_2251_ = l_Lean_Syntax_node3(
                v___x_2225_,
                v___x_2233_,
                v___x_2244_,
                v___x_2248_,
                v___x_2250_,
            );
            v___x_2252_ = l_Lean_Syntax_node2(v___x_2225_, v___x_2232_, v___x_2202_, v___x_2251_);
            v___x_2253_ = l_Lean_Syntax_node2(v___x_2225_, v___x_2226_, v___x_2231_, v___x_2252_);
            v___x_2254_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_2254_, 0, v___x_2253_);
            lean_ctor_set(v___x_2254_, 1, v_a_2196_);
            return v___x_2254_;
        }
    }
}
pub unsafe fn l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___boxed(
    mut v_x_2255_: *mut LeanObject,
    mut v_a_2256_: *mut LeanObject,
    mut v_a_2257_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2258_: *mut LeanObject = core::ptr::null_mut();
    v_res_2258_ = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1(
        v_x_2255_, v_a_2256_, v_a_2257_,
    );
    lean_dec_ref(v_a_2256_);
    return v_res_2258_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Exception(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_InternalExceptionId(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_ErrorExplanation(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_instInhabitedException = _init_l_Lean_instInhabitedException();
    lean_mark_persistent(l_Lean_instInhabitedException);
    l_Lean_unknownIdentifierMessageTag = _init_l_Lean_unknownIdentifierMessageTag();
    lean_mark_persistent(l_Lean_unknownIdentifierMessageTag);
    res = l___private_Lean_Exception_0__Lean_initFn_00___x40_Lean_Exception_2633972168____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_interruptExceptionId = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_interruptExceptionId);
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Exception(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Exception(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_InternalExceptionId(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_ErrorExplanation(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Exception(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Exception(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Exception(builtin);
}
