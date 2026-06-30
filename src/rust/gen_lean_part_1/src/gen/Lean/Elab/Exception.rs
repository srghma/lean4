// Lean compiler output
// Module: Lean.Elab.Exception
// Imports: Lean.Exception
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
pub static l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [112, 111, 115, 116, 112, 111, 110, 101, 0]};
static mut l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2__value) as *mut leanh::LeanObject,14195790338645463942 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_postponeExceptionId: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2__value: leanh::LeanStringObject<18> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [117, 110, 115, 117, 112, 112, 111, 114, 116, 101, 100, 83, 121, 110, 116, 97, 120, 0]};
static mut l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5818550267645997922 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_unsupportedSyntaxExceptionId: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2__value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [97, 98, 111, 114, 116, 67, 111, 109, 109, 97, 110, 100, 69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2__value) as *mut leanh::LeanObject,4356718917055565152 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_abortCommandExceptionId: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2__value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [97, 98, 111, 114, 116, 84, 101, 114, 109, 69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2__value) as *mut leanh::LeanObject,9488515195678987403 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_abortTermExceptionId: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2__value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [97, 98, 111, 114, 116, 84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,14901901600741704791 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_abortTacticExceptionId: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2__value: leanh::LeanStringObject<18> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [97, 117, 116, 111, 66, 111, 117, 110, 100, 73, 109, 112, 108, 105, 99, 105, 116, 0]};
static mut l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2__value) as *mut leanh::LeanObject,16378790584025775847 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_autoBoundImplicitExceptionId: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_throwPostpone___redArg___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_throwPostpone___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_throwUnsupportedSyntax___redArg___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_throwUnsupportedSyntax___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_throwIllFormedSyntax___redArg___closed__0_value:
    leanh::LeanStringObject<18> = leanh::LeanStringObject {
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
        105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 115, 121, 110, 116, 97, 120, 0,
    ],
};
static mut l_Lean_Elab_throwIllFormedSyntax___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_throwIllFormedSyntax___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_throwIllFormedSyntax___redArg___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_throwIllFormedSyntax___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__0_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__1_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        3068268904682231766 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_isAutoBoundImplicitLocalException_x3f___closed__0_value:
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
    m_data: [120, 0],
};
static mut l_Lean_Elab_isAutoBoundImplicitLocalException_x3f___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_isAutoBoundImplicitLocalException_x3f___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_isAutoBoundImplicitLocalException_x3f___closed__1_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_isAutoBoundImplicitLocalException_x3f___closed__0_value)
            as *mut leanh::LeanObject,
        13655884332201764339 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_isAutoBoundImplicitLocalException_x3f___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_isAutoBoundImplicitLocalException_x3f___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__0_value:
    leanh::LeanStringObject<25> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__2_value:
    leanh::LeanStringObject<28> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_throwAbortCommand___redArg___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_throwAbortCommand___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_throwAbortTerm___redArg___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_throwAbortTerm___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_throwAbortTactic___redArg___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_throwAbortTactic___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_mkMessageCore___closed__0_value: leanh::LeanStringObject<1> =
    leanh::LeanStringObject {
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
static mut l_Lean_Elab_mkMessageCore___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkMessageCore___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_231_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_230_ = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2_;
    v___x_231_ = l_Lean_registerInternalExceptionId(v___x_230_);
    return v___x_231_;
}
pub unsafe fn l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2____boxed(
    mut v_a_232_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_233_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_233_ = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2_();
    return v_res_233_;
}
pub unsafe fn l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_239_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_238_ = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2_;
    v___x_239_ = l_Lean_registerInternalExceptionId(v___x_238_);
    return v___x_239_;
}
pub unsafe fn l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2____boxed(
    mut v_a_240_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_241_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_241_ = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2_();
    return v_res_241_;
}
pub unsafe fn l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_247_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_246_ = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2_;
    v___x_247_ = l_Lean_registerInternalExceptionId(v___x_246_);
    return v___x_247_;
}
pub unsafe fn l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2____boxed(
    mut v_a_248_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_249_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_249_ = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2_();
    return v_res_249_;
}
pub unsafe fn l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_255_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_254_ = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2_;
    v___x_255_ = l_Lean_registerInternalExceptionId(v___x_254_);
    return v___x_255_;
}
pub unsafe fn l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2____boxed(
    mut v_a_256_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_257_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_257_ = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2_();
    return v_res_257_;
}
pub unsafe fn l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_263_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_262_ = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2_;
    v___x_263_ = l_Lean_registerInternalExceptionId(v___x_262_);
    return v___x_263_;
}
pub unsafe fn l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2____boxed(
    mut v_a_264_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_265_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_265_ = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2_();
    return v_res_265_;
}
pub unsafe fn l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_271_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_270_ = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2_;
    v___x_271_ = l_Lean_registerInternalExceptionId(v___x_270_);
    return v___x_271_;
}
pub unsafe fn l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2____boxed(
    mut v_a_272_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_273_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_273_ = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2_();
    return v_res_273_;
}
pub unsafe fn _init_l_Lean_Elab_throwPostpone___redArg___closed__0() -> *mut leanh::LeanObject
{
    let mut v___x_274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_276_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_274_ = leanh::lean_box(0);
    v___x_275_ = l_Lean_Elab_postponeExceptionId;
    v___x_276_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_276_, 0, v___x_275_);
    leanh::lean_ctor_set(v___x_276_, 1, v___x_274_);
    return v___x_276_;
}
pub unsafe fn l_Lean_Elab_throwPostpone___redArg(
    mut v_inst_277_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_throw_278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_280_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_throw_278_ = leanh::lean_ctor_get(v_inst_277_, 0);
    leanh::lean_inc(v_throw_278_);
    leanh::lean_dec_ref(v_inst_277_);
    v___x_279_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_throwPostpone___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Elab_throwPostpone___redArg___closed__0_once),
        _init_l_Lean_Elab_throwPostpone___redArg___closed__0,
    );
    v___x_280_ = leanh::lean_apply_2(v_throw_278_, leanh::lean_box(0), v___x_279_);
    return v___x_280_;
}
pub unsafe fn l_Lean_Elab_throwPostpone(
    mut v_m_281_: *mut leanh::LeanObject,
    mut v_00_u03b1_282_: *mut leanh::LeanObject,
    mut v_inst_283_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_284_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_284_ = l_Lean_Elab_throwPostpone___redArg(v_inst_283_);
    return v___x_284_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_287_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_285_ = leanh::lean_box(0);
    v___x_286_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_287_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_287_, 0, v___x_286_);
    leanh::lean_ctor_set(v___x_287_, 1, v___x_285_);
    return v___x_287_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___redArg(
    mut v_inst_288_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_throw_289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_291_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_throw_289_ = leanh::lean_ctor_get(v_inst_288_, 0);
    leanh::lean_inc(v_throw_289_);
    leanh::lean_dec_ref(v_inst_288_);
    v___x_290_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___redArg___closed__0_once),
        _init_l_Lean_Elab_throwUnsupportedSyntax___redArg___closed__0,
    );
    v___x_291_ = leanh::lean_apply_2(v_throw_289_, leanh::lean_box(0), v___x_290_);
    return v___x_291_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax(
    mut v_m_292_: *mut leanh::LeanObject,
    mut v_00_u03b1_293_: *mut leanh::LeanObject,
    mut v_inst_294_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_295_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_295_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v_inst_294_);
    return v___x_295_;
}
pub unsafe fn _init_l_Lean_Elab_throwIllFormedSyntax___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_298_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_297_ = l_Lean_Elab_throwIllFormedSyntax___redArg___closed__0;
    v___x_298_ = l_Lean_stringToMessageData(v___x_297_);
    return v___x_298_;
}
pub unsafe fn l_Lean_Elab_throwIllFormedSyntax___redArg(
    mut v_inst_299_: *mut leanh::LeanObject,
    mut v_inst_300_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_302_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_301_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_throwIllFormedSyntax___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_throwIllFormedSyntax___redArg___closed__1_once),
        _init_l_Lean_Elab_throwIllFormedSyntax___redArg___closed__1,
    );
    v___x_302_ = l_Lean_throwError___redArg(v_inst_299_, v_inst_300_, v___x_301_);
    return v___x_302_;
}
pub unsafe fn l_Lean_Elab_throwIllFormedSyntax(
    mut v_m_303_: *mut leanh::LeanObject,
    mut v_00_u03b1_304_: *mut leanh::LeanObject,
    mut v_inst_305_: *mut leanh::LeanObject,
    mut v_inst_306_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_307_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_307_ = l_Lean_Elab_throwIllFormedSyntax___redArg(v_inst_305_, v_inst_306_);
    return v___x_307_;
}
pub unsafe fn l_Lean_Elab_throwAutoBoundImplicitLocal___redArg(
    mut v_inst_311_: *mut leanh::LeanObject,
    mut v_n_312_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_throw_313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_316_: u8 = 0;
    let mut v___x_317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_326_: u8 = 0;
    let mut v_unused_327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_throw_313_ = leanh::lean_ctor_get(v_inst_311_, 0);
                v_isSharedCheck_326_ = (!leanh::lean_is_exclusive(v_inst_311_)) as u8;
                if v_isSharedCheck_326_ == 0 {
                    v_unused_327_ = leanh::lean_ctor_get(v_inst_311_, 1);
                    leanh::lean_dec(v_unused_327_);
                    v___x_315_ = v_inst_311_;
                    v_isShared_316_ = v_isSharedCheck_326_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_throw_313_);
                    leanh::lean_dec(v_inst_311_);
                    v___x_315_ = leanh::lean_box(0);
                    v_isShared_316_ = v_isSharedCheck_326_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_317_ = l_Lean_Elab_autoBoundImplicitExceptionId;
                v___x_318_ = l_Lean_KVMap_empty;
                v___x_319_ = l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__1;
                v___x_320_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_320_, 0, v_n_312_);
                v___x_321_ = l_Lean_KVMap_insert(v___x_318_, v___x_319_, v___x_320_);
                if v_isShared_316_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_315_, 1);
                    leanh::lean_ctor_set(v___x_315_, 1, v___x_321_);
                    leanh::lean_ctor_set(v___x_315_, 0, v___x_317_);
                    v___x_323_ = v___x_315_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_325_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_325_, 0, v___x_317_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_325_, 1, v___x_321_);
                    v___x_323_ = v_reuseFailAlloc_325_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_324_ =
                    leanh::lean_apply_2(v_throw_313_, leanh::lean_box(0), v___x_323_);
                return v___x_324_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_throwAutoBoundImplicitLocal(
    mut v_m_328_: *mut leanh::LeanObject,
    mut v_00_u03b1_329_: *mut leanh::LeanObject,
    mut v_inst_330_: *mut leanh::LeanObject,
    mut v_n_331_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_332_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_332_ = l_Lean_Elab_throwAutoBoundImplicitLocal___redArg(v_inst_330_, v_n_331_);
    return v___x_332_;
}
pub unsafe fn l_Lean_Elab_isAutoBoundImplicitLocalException_x3f(
    mut v_ex_336_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_ex_336_) == 1 {
        let mut v_id_337_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_extra_338_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_339_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_340_: u8 = 0;
        v_id_337_ = leanh::lean_ctor_get(v_ex_336_, 0);
        v_extra_338_ = leanh::lean_ctor_get(v_ex_336_, 1);
        v___x_339_ = l_Lean_Elab_autoBoundImplicitExceptionId;
        v___x_340_ = l_Lean_instBEqInternalExceptionId_beq(v_id_337_, v___x_339_);
        if v___x_340_ == 0 {
            let mut v___x_341_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_341_ = leanh::lean_box(0);
            return v___x_341_;
        } else {
            let mut v___x_342_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_343_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_344_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_345_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_342_ = l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__1;
            v___x_343_ = l_Lean_Elab_isAutoBoundImplicitLocalException_x3f___closed__1;
            v___x_344_ = l_Lean_KVMap_getName(v_extra_338_, v___x_342_, v___x_343_);
            v___x_345_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_345_, 0, v___x_344_);
            return v___x_345_;
        }
    } else {
        let mut v___x_346_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_346_ = leanh::lean_box(0);
        return v___x_346_;
    }
}
pub unsafe fn l_Lean_Elab_isAutoBoundImplicitLocalException_x3f___boxed(
    mut v_ex_347_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_348_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_348_ = l_Lean_Elab_isAutoBoundImplicitLocalException_x3f(v_ex_347_);
    leanh::lean_dec_ref(v_ex_347_);
    return v_res_348_;
}
pub unsafe fn _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_351_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_350_ = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__0;
    v___x_351_ = l_Lean_stringToMessageData(v___x_350_);
    return v___x_351_;
}
pub unsafe fn _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_354_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_353_ = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__2;
    v___x_354_ = l_Lean_stringToMessageData(v___x_353_);
    return v___x_354_;
}
pub unsafe fn l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg(
    mut v_inst_355_: *mut leanh::LeanObject,
    mut v_inst_356_: *mut leanh::LeanObject,
    mut v_u_357_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_363_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_358_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__1_once
        ),
        _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__1,
    );
    v___x_359_ = l_Lean_MessageData_ofName(v_u_357_);
    v___x_360_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_360_, 0, v___x_358_);
    leanh::lean_ctor_set(v___x_360_, 1, v___x_359_);
    v___x_361_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__3_once
        ),
        _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__3,
    );
    v___x_362_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_362_, 0, v___x_360_);
    leanh::lean_ctor_set(v___x_362_, 1, v___x_361_);
    v___x_363_ = l_Lean_throwError___redArg(v_inst_355_, v_inst_356_, v___x_362_);
    return v___x_363_;
}
pub unsafe fn l_Lean_Elab_throwAlreadyDeclaredUniverseLevel(
    mut v_m_364_: *mut leanh::LeanObject,
    mut v_00_u03b1_365_: *mut leanh::LeanObject,
    mut v_inst_366_: *mut leanh::LeanObject,
    mut v_inst_367_: *mut leanh::LeanObject,
    mut v_u_368_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_369_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_369_ =
        l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg(v_inst_366_, v_inst_367_, v_u_368_);
    return v___x_369_;
}
pub unsafe fn _init_l_Lean_Elab_throwAbortCommand___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_372_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_370_ = leanh::lean_box(0);
    v___x_371_ = l_Lean_Elab_abortCommandExceptionId;
    v___x_372_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_372_, 0, v___x_371_);
    leanh::lean_ctor_set(v___x_372_, 1, v___x_370_);
    return v___x_372_;
}
pub unsafe fn l_Lean_Elab_throwAbortCommand___redArg(
    mut v_inst_373_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_throw_374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_376_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_throw_374_ = leanh::lean_ctor_get(v_inst_373_, 0);
    leanh::lean_inc(v_throw_374_);
    leanh::lean_dec_ref(v_inst_373_);
    v___x_375_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortCommand___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortCommand___redArg___closed__0_once),
        _init_l_Lean_Elab_throwAbortCommand___redArg___closed__0,
    );
    v___x_376_ = leanh::lean_apply_2(v_throw_374_, leanh::lean_box(0), v___x_375_);
    return v___x_376_;
}
pub unsafe fn l_Lean_Elab_throwAbortCommand(
    mut v_00_u03b1_377_: *mut leanh::LeanObject,
    mut v_m_378_: *mut leanh::LeanObject,
    mut v_inst_379_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_380_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_380_ = l_Lean_Elab_throwAbortCommand___redArg(v_inst_379_);
    return v___x_380_;
}
pub unsafe fn _init_l_Lean_Elab_throwAbortTerm___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_383_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_381_ = leanh::lean_box(0);
    v___x_382_ = l_Lean_Elab_abortTermExceptionId;
    v___x_383_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_383_, 0, v___x_382_);
    leanh::lean_ctor_set(v___x_383_, 1, v___x_381_);
    return v___x_383_;
}
pub unsafe fn l_Lean_Elab_throwAbortTerm___redArg(
    mut v_inst_384_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_throw_385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_387_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_throw_385_ = leanh::lean_ctor_get(v_inst_384_, 0);
    leanh::lean_inc(v_throw_385_);
    leanh::lean_dec_ref(v_inst_384_);
    v___x_386_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortTerm___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortTerm___redArg___closed__0_once),
        _init_l_Lean_Elab_throwAbortTerm___redArg___closed__0,
    );
    v___x_387_ = leanh::lean_apply_2(v_throw_385_, leanh::lean_box(0), v___x_386_);
    return v___x_387_;
}
pub unsafe fn l_Lean_Elab_throwAbortTerm(
    mut v_00_u03b1_388_: *mut leanh::LeanObject,
    mut v_m_389_: *mut leanh::LeanObject,
    mut v_inst_390_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_391_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_391_ = l_Lean_Elab_throwAbortTerm___redArg(v_inst_390_);
    return v___x_391_;
}
pub unsafe fn _init_l_Lean_Elab_throwAbortTactic___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_394_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_392_ = leanh::lean_box(0);
    v___x_393_ = l_Lean_Elab_abortTacticExceptionId;
    v___x_394_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_394_, 0, v___x_393_);
    leanh::lean_ctor_set(v___x_394_, 1, v___x_392_);
    return v___x_394_;
}
pub unsafe fn l_Lean_Elab_throwAbortTactic___redArg(
    mut v_inst_395_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_throw_396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_398_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_throw_396_ = leanh::lean_ctor_get(v_inst_395_, 0);
    leanh::lean_inc(v_throw_396_);
    leanh::lean_dec_ref(v_inst_395_);
    v___x_397_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortTactic___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortTactic___redArg___closed__0_once),
        _init_l_Lean_Elab_throwAbortTactic___redArg___closed__0,
    );
    v___x_398_ = leanh::lean_apply_2(v_throw_396_, leanh::lean_box(0), v___x_397_);
    return v___x_398_;
}
pub unsafe fn l_Lean_Elab_throwAbortTactic(
    mut v_00_u03b1_399_: *mut leanh::LeanObject,
    mut v_m_400_: *mut leanh::LeanObject,
    mut v_inst_401_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_402_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_402_ = l_Lean_Elab_throwAbortTactic___redArg(v_inst_401_);
    return v___x_402_;
}
pub unsafe fn l_Lean_Elab_isAbortTacticException(
    mut v_ex_403_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_ex_403_) == 1 {
        let mut v_id_404_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_405_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_406_: u8 = 0;
        v_id_404_ = leanh::lean_ctor_get(v_ex_403_, 0);
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
    mut v_ex_408_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_409_: u8 = 0;
    let mut v_r_410_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_409_ = l_Lean_Elab_isAbortTacticException(v_ex_408_);
    leanh::lean_dec_ref(v_ex_408_);
    v_r_410_ = leanh::lean_box((v_res_409_) as usize);
    return v_r_410_;
}
pub unsafe fn l_Lean_Elab_isAbortExceptionId(mut v_id_411_: *mut leanh::LeanObject) -> u8 {
    let mut v___y_413_: u8 = 0;
    let mut v___x_414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_415_: u8 = 0;
    let mut v___x_416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_417_: u8 = 0;
    let mut v___x_418_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_id_420_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_421_: u8 = 0;
    let mut v_r_422_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_421_ = l_Lean_Elab_isAbortExceptionId(v_id_420_);
    leanh::lean_dec(v_id_420_);
    v_r_422_ = leanh::lean_box((v_res_421_) as usize);
    return v_r_422_;
}
pub unsafe fn l_Lean_Elab_isAbortException(mut v_ex_423_: *mut leanh::LeanObject) -> u8 {
    if leanh::lean_obj_tag(v_ex_423_) == 1 {
        let mut v_id_424_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_425_: u8 = 0;
        v_id_424_ = leanh::lean_ctor_get(v_ex_423_, 0);
        v___x_425_ = l_Lean_Elab_isAbortExceptionId(v_id_424_);
        return v___x_425_;
    } else {
        let mut v___x_426_: u8 = 0;
        v___x_426_ = 0;
        return v___x_426_;
    }
}
pub unsafe fn l_Lean_Elab_isAbortException___boxed(
    mut v_ex_427_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_428_: u8 = 0;
    let mut v_r_429_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_428_ = l_Lean_Elab_isAbortException(v_ex_427_);
    leanh::lean_dec_ref(v_ex_427_);
    v_r_429_ = leanh::lean_box((v_res_428_) as usize);
    return v_r_429_;
}
pub unsafe fn l_Lean_Elab_mkMessageCore(
    mut v_fileName_431_: *mut leanh::LeanObject,
    mut v_fileMap_432_: *mut leanh::LeanObject,
    mut v_data_433_: *mut leanh::LeanObject,
    mut v_severity_434_: u8,
    mut v_pos_435_: *mut leanh::LeanObject,
    mut v_endPos_436_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pos_437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_440_: u8 = 0;
    let mut v___x_441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_442_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_fileMap_432_);
    v_pos_437_ = l_Lean_FileMap_toPosition(v_fileMap_432_, v_pos_435_);
    v_endPos_438_ = l_Lean_FileMap_toPosition(v_fileMap_432_, v_endPos_436_);
    v___x_439_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_439_, 0, v_endPos_438_);
    v___x_440_ = 0;
    v___x_441_ = l_Lean_Elab_mkMessageCore___closed__0;
    v___x_442_ = leanh::lean_alloc_ctor(0, 5, (3) as u32);
    leanh::lean_ctor_set(v___x_442_, 0, v_fileName_431_);
    leanh::lean_ctor_set(v___x_442_, 1, v_pos_437_);
    leanh::lean_ctor_set(v___x_442_, 2, v___x_439_);
    leanh::lean_ctor_set(v___x_442_, 3, v___x_441_);
    leanh::lean_ctor_set(v___x_442_, 4, v_data_433_);
    leanh::lean_ctor_set_uint8(
        v___x_442_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
        v___x_440_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_442_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
        v_severity_434_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_442_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 2) as u32,
        v___x_440_,
    );
    return v___x_442_;
}
pub unsafe fn l_Lean_Elab_mkMessageCore___boxed(
    mut v_fileName_443_: *mut leanh::LeanObject,
    mut v_fileMap_444_: *mut leanh::LeanObject,
    mut v_data_445_: *mut leanh::LeanObject,
    mut v_severity_446_: *mut leanh::LeanObject,
    mut v_pos_447_: *mut leanh::LeanObject,
    mut v_endPos_448_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_severity_boxed_449_: u8 = 0;
    let mut v_res_450_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_449_ = (leanh::lean_unbox(v_severity_446_) as u8);
    v_res_450_ = l_Lean_Elab_mkMessageCore(
        v_fileName_443_,
        v_fileMap_444_,
        v_data_445_,
        v_severity_boxed_449_,
        v_pos_447_,
        v_endPos_448_,
    );
    leanh::lean_dec(v_endPos_448_);
    leanh::lean_dec(v_pos_447_);
    return v_res_450_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Exception(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Exception(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Elab_postponeExceptionId = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_Elab_postponeExceptionId);
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Elab_unsupportedSyntaxExceptionId = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_Elab_unsupportedSyntaxExceptionId);
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Elab_abortCommandExceptionId = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_Elab_abortCommandExceptionId);
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Elab_abortTermExceptionId = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_Elab_abortTermExceptionId);
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Elab_abortTacticExceptionId = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_Elab_abortTacticExceptionId);
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Elab_autoBoundImplicitExceptionId = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_Elab_autoBoundImplicitExceptionId);
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Exception(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Exception(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Exception(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Exception(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Exception(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Exception(builtin);
}