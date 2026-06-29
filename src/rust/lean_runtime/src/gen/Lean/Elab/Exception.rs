// Lean compiler output
// Module: Lean.Elab.Exception
// Imports: Lean.Exception
use crate::r#gen::Init::Prelude::l_Lean_Name_mkStr1;
use crate::r#gen::Lean::Data::KVMap::{
    l_Lean_KVMap_empty, l_Lean_KVMap_getName, l_Lean_KVMap_insert,
};
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::Exception::{
    initialize_Lean_Exception, l_Lean_throwError___redArg, runtime_initialize_Lean_Exception,
};
use crate::r#gen::Lean::InternalExceptionId::{
    l_Lean_instBEqInternalExceptionId_beq, l_Lean_registerInternalExceptionId,
};
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofName, l_Lean_stringToMessageData};
pub static l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [112, 111, 115, 116, 112, 111, 110, 101, 0]};
static mut l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,14195790338645463942 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_postponeExceptionId: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [117, 110, 115, 117, 112, 112, 111, 114, 116, 101, 100, 83, 121, 110, 116, 97, 120, 0]};
static mut l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5818550267645997922 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_unsupportedSyntaxExceptionId: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [97, 98, 111, 114, 116, 67, 111, 109, 109, 97, 110, 100, 69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4356718917055565152 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_abortCommandExceptionId: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [97, 98, 111, 114, 116, 84, 101, 114, 109, 69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,9488515195678987403 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_abortTermExceptionId: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [97, 98, 111, 114, 116, 84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,14901901600741704791 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_abortTacticExceptionId: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [97, 117, 116, 111, 66, 111, 117, 110, 100, 73, 109, 112, 108, 105, 99, 105, 116, 0]};
static mut l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,16378790584025775847 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_autoBoundImplicitExceptionId: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_throwPostpone___redArg___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_throwPostpone___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_throwUnsupportedSyntax___redArg___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_throwUnsupportedSyntax___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_throwIllFormedSyntax___redArg___closed__0_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
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
        105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 115, 121, 110, 116, 97, 120, 0,
    ],
};
static mut l_Lean_Elab_throwIllFormedSyntax___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_throwIllFormedSyntax___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_throwIllFormedSyntax___redArg___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_throwIllFormedSyntax___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__0_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [108, 111, 99, 97, 108, 73, 100, 0],
};
static mut l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        3068268904682231766 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_isAutoBoundImplicitLocalException_x3f___closed__0_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [120, 0],
};
static mut l_Lean_Elab_isAutoBoundImplicitLocalException_x3f___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_isAutoBoundImplicitLocalException_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_isAutoBoundImplicitLocalException_x3f___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_isAutoBoundImplicitLocalException_x3f___closed__0_value)
            as *mut crate::leanh::LeanObject,
        13655884332201764339 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_isAutoBoundImplicitLocalException_x3f___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_isAutoBoundImplicitLocalException_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__0_value:
    crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        97, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32, 108, 101, 118, 101, 108, 32, 110, 97,
        109, 101, 100, 32, 96, 0,
    ],
};
static mut l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__2_value:
    crate::leanh::LeanStringObject<28> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 27,
    m_data: [
        96, 32, 104, 97, 115, 32, 97, 108, 114, 101, 97, 100, 121, 32, 98, 101, 101, 110, 32, 100,
        101, 99, 108, 97, 114, 101, 100, 0,
    ],
};
static mut l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_throwAbortCommand___redArg___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_throwAbortCommand___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_throwAbortTerm___redArg___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_throwAbortTerm___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_throwAbortTactic___redArg___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_throwAbortTactic___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_mkMessageCore___closed__0_value: crate::leanh::LeanStringObject<1> =
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
static mut l_Lean_Elab_mkMessageCore___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkMessageCore___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_230_ = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2_;
    v___x_231_ = l_Lean_registerInternalExceptionId(v___x_230_);
    return v___x_231_;
}
pub unsafe fn l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2____boxed(
    mut v_a_232_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_233_ = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2_();
    return v_res_233_;
}
pub unsafe fn l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_238_ = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2_;
    v___x_239_ = l_Lean_registerInternalExceptionId(v___x_238_);
    return v___x_239_;
}
pub unsafe fn l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2____boxed(
    mut v_a_240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_241_ = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2_();
    return v_res_241_;
}
pub unsafe fn l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_246_ = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2_;
    v___x_247_ = l_Lean_registerInternalExceptionId(v___x_246_);
    return v___x_247_;
}
pub unsafe fn l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2____boxed(
    mut v_a_248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_249_ = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2_();
    return v_res_249_;
}
pub unsafe fn l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_254_ = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2_;
    v___x_255_ = l_Lean_registerInternalExceptionId(v___x_254_);
    return v___x_255_;
}
pub unsafe fn l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2____boxed(
    mut v_a_256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_257_ = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2_();
    return v_res_257_;
}
pub unsafe fn l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_262_ = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2_;
    v___x_263_ = l_Lean_registerInternalExceptionId(v___x_262_);
    return v___x_263_;
}
pub unsafe fn l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2____boxed(
    mut v_a_264_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_265_ = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2_();
    return v_res_265_;
}
pub unsafe fn l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_270_ = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2_;
    v___x_271_ = l_Lean_registerInternalExceptionId(v___x_270_);
    return v___x_271_;
}
pub unsafe fn l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2____boxed(
    mut v_a_272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_273_ = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2_();
    return v_res_273_;
}
pub unsafe fn _init_l_Lean_Elab_throwPostpone___redArg___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_274_ = crate::leanh::lean_box(0);
    v___x_275_ = l_Lean_Elab_postponeExceptionId;
    v___x_276_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_276_, 0, v___x_275_);
    crate::leanh::lean_ctor_set(v___x_276_, 1, v___x_274_);
    return v___x_276_;
}
pub unsafe fn l_Lean_Elab_throwPostpone___redArg(
    mut v_inst_277_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_throw_278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_throw_278_ = crate::leanh::lean_ctor_get(v_inst_277_, 0);
    crate::leanh::lean_inc(v_throw_278_);
    crate::leanh::lean_dec_ref(v_inst_277_);
    v___x_279_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_throwPostpone___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Elab_throwPostpone___redArg___closed__0_once),
        _init_l_Lean_Elab_throwPostpone___redArg___closed__0,
    );
    v___x_280_ = crate::leanh::lean_apply_2(v_throw_278_, crate::leanh::lean_box(0), v___x_279_);
    return v___x_280_;
}
pub unsafe fn l_Lean_Elab_throwPostpone(
    mut v_m_281_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_282_: *mut crate::leanh::LeanObject,
    mut v_inst_283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_284_ = l_Lean_Elab_throwPostpone___redArg(v_inst_283_);
    return v___x_284_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_285_ = crate::leanh::lean_box(0);
    v___x_286_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_287_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_287_, 0, v___x_286_);
    crate::leanh::lean_ctor_set(v___x_287_, 1, v___x_285_);
    return v___x_287_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___redArg(
    mut v_inst_288_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_throw_289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_throw_289_ = crate::leanh::lean_ctor_get(v_inst_288_, 0);
    crate::leanh::lean_inc(v_throw_289_);
    crate::leanh::lean_dec_ref(v_inst_288_);
    v___x_290_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___redArg___closed__0_once),
        _init_l_Lean_Elab_throwUnsupportedSyntax___redArg___closed__0,
    );
    v___x_291_ = crate::leanh::lean_apply_2(v_throw_289_, crate::leanh::lean_box(0), v___x_290_);
    return v___x_291_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax(
    mut v_m_292_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_293_: *mut crate::leanh::LeanObject,
    mut v_inst_294_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_295_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v_inst_294_);
    return v___x_295_;
}
pub unsafe fn _init_l_Lean_Elab_throwIllFormedSyntax___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_297_ = l_Lean_Elab_throwIllFormedSyntax___redArg___closed__0;
    v___x_298_ = l_Lean_stringToMessageData(v___x_297_);
    return v___x_298_;
}
pub unsafe fn l_Lean_Elab_throwIllFormedSyntax___redArg(
    mut v_inst_299_: *mut crate::leanh::LeanObject,
    mut v_inst_300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_301_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_throwIllFormedSyntax___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_throwIllFormedSyntax___redArg___closed__1_once),
        _init_l_Lean_Elab_throwIllFormedSyntax___redArg___closed__1,
    );
    v___x_302_ = l_Lean_throwError___redArg(v_inst_299_, v_inst_300_, v___x_301_);
    return v___x_302_;
}
pub unsafe fn l_Lean_Elab_throwIllFormedSyntax(
    mut v_m_303_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_304_: *mut crate::leanh::LeanObject,
    mut v_inst_305_: *mut crate::leanh::LeanObject,
    mut v_inst_306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_307_ = l_Lean_Elab_throwIllFormedSyntax___redArg(v_inst_305_, v_inst_306_);
    return v___x_307_;
}
pub unsafe fn l_Lean_Elab_throwAutoBoundImplicitLocal___redArg(
    mut v_inst_311_: *mut crate::leanh::LeanObject,
    mut v_n_312_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_throw_313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_316_: u8 = 0;
    let mut v___x_317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_326_: u8 = 0;
    let mut v_unused_327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_throw_313_ = crate::leanh::lean_ctor_get(v_inst_311_, 0);
                v_isSharedCheck_326_ = (!crate::leanh::lean_is_exclusive(v_inst_311_)) as u8;
                if v_isSharedCheck_326_ == 0 {
                    v_unused_327_ = crate::leanh::lean_ctor_get(v_inst_311_, 1);
                    crate::leanh::lean_dec(v_unused_327_);
                    v___x_315_ = v_inst_311_;
                    v_isShared_316_ = v_isSharedCheck_326_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_throw_313_);
                    crate::leanh::lean_dec(v_inst_311_);
                    v___x_315_ = crate::leanh::lean_box(0);
                    v_isShared_316_ = v_isSharedCheck_326_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_317_ = l_Lean_Elab_autoBoundImplicitExceptionId;
                v___x_318_ = l_Lean_KVMap_empty;
                v___x_319_ = l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__1;
                v___x_320_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_320_, 0, v_n_312_);
                v___x_321_ = l_Lean_KVMap_insert(v___x_318_, v___x_319_, v___x_320_);
                if v_isShared_316_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_315_, 1);
                    crate::leanh::lean_ctor_set(v___x_315_, 1, v___x_321_);
                    crate::leanh::lean_ctor_set(v___x_315_, 0, v___x_317_);
                    v___x_323_ = v___x_315_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_325_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_325_, 0, v___x_317_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_325_, 1, v___x_321_);
                    v___x_323_ = v_reuseFailAlloc_325_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_324_ =
                    crate::leanh::lean_apply_2(v_throw_313_, crate::leanh::lean_box(0), v___x_323_);
                return v___x_324_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_throwAutoBoundImplicitLocal(
    mut v_m_328_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_329_: *mut crate::leanh::LeanObject,
    mut v_inst_330_: *mut crate::leanh::LeanObject,
    mut v_n_331_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_332_ = l_Lean_Elab_throwAutoBoundImplicitLocal___redArg(v_inst_330_, v_n_331_);
    return v___x_332_;
}
pub unsafe fn l_Lean_Elab_isAutoBoundImplicitLocalException_x3f(
    mut v_ex_336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_ex_336_) == 1 {
        let mut v_id_337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_extra_338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_340_: u8 = 0;
        v_id_337_ = crate::leanh::lean_ctor_get(v_ex_336_, 0);
        v_extra_338_ = crate::leanh::lean_ctor_get(v_ex_336_, 1);
        v___x_339_ = l_Lean_Elab_autoBoundImplicitExceptionId;
        v___x_340_ = l_Lean_instBEqInternalExceptionId_beq(v_id_337_, v___x_339_);
        if v___x_340_ == 0 {
            let mut v___x_341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_341_ = crate::leanh::lean_box(0);
            return v___x_341_;
        } else {
            let mut v___x_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_342_ = l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__1;
            v___x_343_ = l_Lean_Elab_isAutoBoundImplicitLocalException_x3f___closed__1;
            v___x_344_ = l_Lean_KVMap_getName(v_extra_338_, v___x_342_, v___x_343_);
            v___x_345_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_345_, 0, v___x_344_);
            return v___x_345_;
        }
    } else {
        let mut v___x_346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_346_ = crate::leanh::lean_box(0);
        return v___x_346_;
    }
}
pub unsafe fn l_Lean_Elab_isAutoBoundImplicitLocalException_x3f___boxed(
    mut v_ex_347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_348_ = l_Lean_Elab_isAutoBoundImplicitLocalException_x3f(v_ex_347_);
    crate::leanh::lean_dec_ref(v_ex_347_);
    return v_res_348_;
}
pub unsafe fn _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_350_ = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__0;
    v___x_351_ = l_Lean_stringToMessageData(v___x_350_);
    return v___x_351_;
}
pub unsafe fn _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_353_ = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__2;
    v___x_354_ = l_Lean_stringToMessageData(v___x_353_);
    return v___x_354_;
}
pub unsafe fn l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg(
    mut v_inst_355_: *mut crate::leanh::LeanObject,
    mut v_inst_356_: *mut crate::leanh::LeanObject,
    mut v_u_357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_358_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__1_once
        ),
        _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__1,
    );
    v___x_359_ = l_Lean_MessageData_ofName(v_u_357_);
    v___x_360_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_360_, 0, v___x_358_);
    crate::leanh::lean_ctor_set(v___x_360_, 1, v___x_359_);
    v___x_361_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__3_once
        ),
        _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__3,
    );
    v___x_362_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_362_, 0, v___x_360_);
    crate::leanh::lean_ctor_set(v___x_362_, 1, v___x_361_);
    v___x_363_ = l_Lean_throwError___redArg(v_inst_355_, v_inst_356_, v___x_362_);
    return v___x_363_;
}
pub unsafe fn l_Lean_Elab_throwAlreadyDeclaredUniverseLevel(
    mut v_m_364_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_365_: *mut crate::leanh::LeanObject,
    mut v_inst_366_: *mut crate::leanh::LeanObject,
    mut v_inst_367_: *mut crate::leanh::LeanObject,
    mut v_u_368_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_369_ =
        l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg(v_inst_366_, v_inst_367_, v_u_368_);
    return v___x_369_;
}
pub unsafe fn _init_l_Lean_Elab_throwAbortCommand___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_370_ = crate::leanh::lean_box(0);
    v___x_371_ = l_Lean_Elab_abortCommandExceptionId;
    v___x_372_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_372_, 0, v___x_371_);
    crate::leanh::lean_ctor_set(v___x_372_, 1, v___x_370_);
    return v___x_372_;
}
pub unsafe fn l_Lean_Elab_throwAbortCommand___redArg(
    mut v_inst_373_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_throw_374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_throw_374_ = crate::leanh::lean_ctor_get(v_inst_373_, 0);
    crate::leanh::lean_inc(v_throw_374_);
    crate::leanh::lean_dec_ref(v_inst_373_);
    v___x_375_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortCommand___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortCommand___redArg___closed__0_once),
        _init_l_Lean_Elab_throwAbortCommand___redArg___closed__0,
    );
    v___x_376_ = crate::leanh::lean_apply_2(v_throw_374_, crate::leanh::lean_box(0), v___x_375_);
    return v___x_376_;
}
pub unsafe fn l_Lean_Elab_throwAbortCommand(
    mut v_00_u03b1_377_: *mut crate::leanh::LeanObject,
    mut v_m_378_: *mut crate::leanh::LeanObject,
    mut v_inst_379_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_380_ = l_Lean_Elab_throwAbortCommand___redArg(v_inst_379_);
    return v___x_380_;
}
pub unsafe fn _init_l_Lean_Elab_throwAbortTerm___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_381_ = crate::leanh::lean_box(0);
    v___x_382_ = l_Lean_Elab_abortTermExceptionId;
    v___x_383_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_383_, 0, v___x_382_);
    crate::leanh::lean_ctor_set(v___x_383_, 1, v___x_381_);
    return v___x_383_;
}
pub unsafe fn l_Lean_Elab_throwAbortTerm___redArg(
    mut v_inst_384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_throw_385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_throw_385_ = crate::leanh::lean_ctor_get(v_inst_384_, 0);
    crate::leanh::lean_inc(v_throw_385_);
    crate::leanh::lean_dec_ref(v_inst_384_);
    v___x_386_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortTerm___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortTerm___redArg___closed__0_once),
        _init_l_Lean_Elab_throwAbortTerm___redArg___closed__0,
    );
    v___x_387_ = crate::leanh::lean_apply_2(v_throw_385_, crate::leanh::lean_box(0), v___x_386_);
    return v___x_387_;
}
pub unsafe fn l_Lean_Elab_throwAbortTerm(
    mut v_00_u03b1_388_: *mut crate::leanh::LeanObject,
    mut v_m_389_: *mut crate::leanh::LeanObject,
    mut v_inst_390_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_391_ = l_Lean_Elab_throwAbortTerm___redArg(v_inst_390_);
    return v___x_391_;
}
pub unsafe fn _init_l_Lean_Elab_throwAbortTactic___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_392_ = crate::leanh::lean_box(0);
    v___x_393_ = l_Lean_Elab_abortTacticExceptionId;
    v___x_394_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_394_, 0, v___x_393_);
    crate::leanh::lean_ctor_set(v___x_394_, 1, v___x_392_);
    return v___x_394_;
}
pub unsafe fn l_Lean_Elab_throwAbortTactic___redArg(
    mut v_inst_395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_throw_396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_throw_396_ = crate::leanh::lean_ctor_get(v_inst_395_, 0);
    crate::leanh::lean_inc(v_throw_396_);
    crate::leanh::lean_dec_ref(v_inst_395_);
    v___x_397_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortTactic___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortTactic___redArg___closed__0_once),
        _init_l_Lean_Elab_throwAbortTactic___redArg___closed__0,
    );
    v___x_398_ = crate::leanh::lean_apply_2(v_throw_396_, crate::leanh::lean_box(0), v___x_397_);
    return v___x_398_;
}
pub unsafe fn l_Lean_Elab_throwAbortTactic(
    mut v_00_u03b1_399_: *mut crate::leanh::LeanObject,
    mut v_m_400_: *mut crate::leanh::LeanObject,
    mut v_inst_401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_402_ = l_Lean_Elab_throwAbortTactic___redArg(v_inst_401_);
    return v___x_402_;
}
pub unsafe fn l_Lean_Elab_isAbortTacticException(
    mut v_ex_403_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_ex_403_) == 1 {
        let mut v_id_404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_406_: u8 = 0;
        v_id_404_ = crate::leanh::lean_ctor_get(v_ex_403_, 0);
        v___x_405_ = l_Lean_Elab_abortTacticExceptionId;
        v___x_406_ = l_Lean_instBEqInternalExceptionId_beq(v_id_404_, v___x_405_);
        return v___x_406_;
    } else {
        let mut v___x_407_: u8 = 0;
        v___x_407_ = 0;
        return v___x_407_;
    }
}
pub unsafe fn l_Lean_Elab_isAbortTacticException___boxed(
    mut v_ex_408_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_409_: u8 = 0;
    let mut v_r_410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_409_ = l_Lean_Elab_isAbortTacticException(v_ex_408_);
    crate::leanh::lean_dec_ref(v_ex_408_);
    v_r_410_ = crate::leanh::lean_box((v_res_409_) as usize);
    return v_r_410_;
}
pub unsafe fn l_Lean_Elab_isAbortExceptionId(mut v_id_411_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___y_413_: u8 = 0;
    let mut v___x_414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_415_: u8 = 0;
    let mut v___x_416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_417_: u8 = 0;
    let mut v___x_418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_419_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_416_ = l_Lean_Elab_abortCommandExceptionId;
                v___x_417_ = l_Lean_instBEqInternalExceptionId_beq(v_id_411_, v___x_416_);
                if v___x_417_ == 0 {
                    v___x_418_ = l_Lean_Elab_abortTermExceptionId;
                    v___x_419_ = l_Lean_instBEqInternalExceptionId_beq(v_id_411_, v___x_418_);
                    v___y_413_ = v___x_419_;
                    state = 1;
                    continue;
                } else {
                    v___y_413_ = v___x_417_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_413_ == 0 {
                    v___x_414_ = l_Lean_Elab_abortTacticExceptionId;
                    v___x_415_ = l_Lean_instBEqInternalExceptionId_beq(v_id_411_, v___x_414_);
                    return v___x_415_;
                } else {
                    return v___y_413_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_isAbortExceptionId___boxed(
    mut v_id_420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_421_: u8 = 0;
    let mut v_r_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_421_ = l_Lean_Elab_isAbortExceptionId(v_id_420_);
    crate::leanh::lean_dec(v_id_420_);
    v_r_422_ = crate::leanh::lean_box((v_res_421_) as usize);
    return v_r_422_;
}
pub unsafe fn l_Lean_Elab_isAbortException(mut v_ex_423_: *mut crate::leanh::LeanObject) -> u8 {
    if crate::leanh::lean_obj_tag(v_ex_423_) == 1 {
        let mut v_id_424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_425_: u8 = 0;
        v_id_424_ = crate::leanh::lean_ctor_get(v_ex_423_, 0);
        v___x_425_ = l_Lean_Elab_isAbortExceptionId(v_id_424_);
        return v___x_425_;
    } else {
        let mut v___x_426_: u8 = 0;
        v___x_426_ = 0;
        return v___x_426_;
    }
}
pub unsafe fn l_Lean_Elab_isAbortException___boxed(
    mut v_ex_427_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_428_: u8 = 0;
    let mut v_r_429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_428_ = l_Lean_Elab_isAbortException(v_ex_427_);
    crate::leanh::lean_dec_ref(v_ex_427_);
    v_r_429_ = crate::leanh::lean_box((v_res_428_) as usize);
    return v_r_429_;
}
pub unsafe fn l_Lean_Elab_mkMessageCore(
    mut v_fileName_431_: *mut crate::leanh::LeanObject,
    mut v_fileMap_432_: *mut crate::leanh::LeanObject,
    mut v_data_433_: *mut crate::leanh::LeanObject,
    mut v_severity_434_: u8,
    mut v_pos_435_: *mut crate::leanh::LeanObject,
    mut v_endPos_436_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pos_437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_440_: u8 = 0;
    let mut v___x_441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_fileMap_432_);
    v_pos_437_ = l_Lean_FileMap_toPosition(v_fileMap_432_, v_pos_435_);
    v_endPos_438_ = l_Lean_FileMap_toPosition(v_fileMap_432_, v_endPos_436_);
    v___x_439_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_439_, 0, v_endPos_438_);
    v___x_440_ = 0;
    v___x_441_ = l_Lean_Elab_mkMessageCore___closed__0;
    v___x_442_ = crate::leanh::lean_alloc_ctor(0, 5, (3) as u32);
    crate::leanh::lean_ctor_set(v___x_442_, 0, v_fileName_431_);
    crate::leanh::lean_ctor_set(v___x_442_, 1, v_pos_437_);
    crate::leanh::lean_ctor_set(v___x_442_, 2, v___x_439_);
    crate::leanh::lean_ctor_set(v___x_442_, 3, v___x_441_);
    crate::leanh::lean_ctor_set(v___x_442_, 4, v_data_433_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_442_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
        v___x_440_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_442_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
        v_severity_434_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_442_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 2) as u32,
        v___x_440_,
    );
    return v___x_442_;
}
pub unsafe fn l_Lean_Elab_mkMessageCore___boxed(
    mut v_fileName_443_: *mut crate::leanh::LeanObject,
    mut v_fileMap_444_: *mut crate::leanh::LeanObject,
    mut v_data_445_: *mut crate::leanh::LeanObject,
    mut v_severity_446_: *mut crate::leanh::LeanObject,
    mut v_pos_447_: *mut crate::leanh::LeanObject,
    mut v_endPos_448_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_449_: u8 = 0;
    let mut v_res_450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_449_ = (crate::leanh::lean_unbox(v_severity_446_) as u8);
    v_res_450_ = l_Lean_Elab_mkMessageCore(
        v_fileName_443_,
        v_fileMap_444_,
        v_data_445_,
        v_severity_boxed_449_,
        v_pos_447_,
        v_endPos_448_,
    );
    crate::leanh::lean_dec(v_endPos_448_);
    crate::leanh::lean_dec(v_pos_447_);
    return v_res_450_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Exception(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Exception(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Elab_postponeExceptionId = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Elab_postponeExceptionId);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Elab_unsupportedSyntaxExceptionId = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Elab_unsupportedSyntaxExceptionId);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Elab_abortCommandExceptionId = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Elab_abortCommandExceptionId);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Elab_abortTermExceptionId = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Elab_abortTermExceptionId);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Elab_abortTacticExceptionId = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Elab_abortTacticExceptionId);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Elab_autoBoundImplicitExceptionId = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Elab_autoBoundImplicitExceptionId);
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Exception(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Exception(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Exception(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Exception(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Exception(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Exception(builtin);
}
