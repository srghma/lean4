// Lean compiler output
// Module: Lean.Elab.Tactic.Congr
// Imports: Lean.Meta.Tactic.Congr Lean.Elab.Tactic.Basic
use crate::r#gen::Init::Meta::Defs::{l_Lean_Syntax_isNone, l_Lean_TSyntax_getNat};
use crate::r#gen::Init::Prelude::{
    l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull,
};
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    initialize_Lean_Elab_Tactic_Basic, l_Lean_Elab_Tactic_getMainGoal___redArg,
    l_Lean_Elab_Tactic_replaceMainGoal___redArg, l_Lean_Elab_Tactic_tacticElabAttribute,
    l_Lean_Elab_Tactic_withMainContext___redArg, runtime_initialize_Lean_Elab_Tactic_Basic,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Meta::Tactic::Congr::{
    initialize_Lean_Meta_Tactic_Congr, l_Lean_MVarId_congrN,
    runtime_initialize_Lean_Meta_Tactic_Congr,
};
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__0_value:
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
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__1_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [80, 97, 114, 115, 101, 114, 0],
};
static mut l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__2_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [84, 97, 99, 116, 105, 99, 0],
};
static mut l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__3_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [99, 111, 110, 103, 114, 0],
};
static mut l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__3_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__4_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__4_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__4_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__4_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__2_value)
            as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__4_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__4_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__3_value)
            as *mut leanh::LeanObject,
        7757010358911522857 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__4_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__1_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [101, 118, 97, 108, 67, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__1_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__2_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__0_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__2_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__2_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__2_value) as *mut leanh::LeanObject,12733524109236233889 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__2_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__2_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__0_value) as *mut leanh::LeanObject,8091555762121448132 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__2_value_aux_4: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__2_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__0_value) as *mut leanh::LeanObject,8241698261642232286 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__2_value_aux_5: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__2_value_aux_4) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__2_value) as *mut leanh::LeanObject,15114071845524100611 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__2_value_aux_5) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__1_value) as *mut leanh::LeanObject,4478290776814184064 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 13 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 38 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__1_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 19 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 31 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__2_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__0_value) as *mut leanh::LeanObject,((( 38 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__1_value) as *mut leanh::LeanObject,((( 31 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__3_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 13 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 42 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__4_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 13 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 51 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__5_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__3_value) as *mut leanh::LeanObject,((( 42 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__4_value) as *mut leanh::LeanObject,((( 51 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__6_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__2_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__5_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__6_value) as *mut leanh::LeanObject;
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_188_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_186_ = leanh::lean_box(0);
    v___x_187_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_188_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_188_, 0, v___x_187_);
    leanh::lean_ctor_set(v___x_188_, 1, v___x_186_);
    return v___x_188_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0___redArg()
-> *mut leanh::LeanObject {
    let mut v___x_190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_191_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_190_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0___redArg___closed__0);
    v___x_191_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_191_, 0, v___x_190_);
    return v___x_191_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0___redArg___boxed(
    mut v___y_192_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_193_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_193_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0___redArg();
    return v_res_193_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0(
    mut v_00_u03b1_194_: *mut leanh::LeanObject,
    mut v___y_195_: *mut leanh::LeanObject,
    mut v___y_196_: *mut leanh::LeanObject,
    mut v___y_197_: *mut leanh::LeanObject,
    mut v___y_198_: *mut leanh::LeanObject,
    mut v___y_199_: *mut leanh::LeanObject,
    mut v___y_200_: *mut leanh::LeanObject,
    mut v___y_201_: *mut leanh::LeanObject,
    mut v___y_202_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_204_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_204_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0___redArg();
    return v___x_204_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0___boxed(
    mut v_00_u03b1_205_: *mut leanh::LeanObject,
    mut v___y_206_: *mut leanh::LeanObject,
    mut v___y_207_: *mut leanh::LeanObject,
    mut v___y_208_: *mut leanh::LeanObject,
    mut v___y_209_: *mut leanh::LeanObject,
    mut v___y_210_: *mut leanh::LeanObject,
    mut v___y_211_: *mut leanh::LeanObject,
    mut v___y_212_: *mut leanh::LeanObject,
    mut v___y_213_: *mut leanh::LeanObject,
    mut v___y_214_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_215_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_215_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0(v_00_u03b1_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_);
    leanh::lean_dec(v___y_213_);
    leanh::lean_dec_ref(v___y_212_);
    leanh::lean_dec(v___y_211_);
    leanh::lean_dec_ref(v___y_210_);
    leanh::lean_dec(v___y_209_);
    leanh::lean_dec_ref(v___y_208_);
    leanh::lean_dec(v___y_207_);
    leanh::lean_dec_ref(v___y_206_);
    return v_res_215_;
}
pub unsafe fn l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___lam__0(
    mut v___y_216_: *mut leanh::LeanObject,
    mut v___x_217_: u8,
    mut v___y_218_: *mut leanh::LeanObject,
    mut v___y_219_: *mut leanh::LeanObject,
    mut v___y_220_: *mut leanh::LeanObject,
    mut v___y_221_: *mut leanh::LeanObject,
    mut v___y_222_: *mut leanh::LeanObject,
    mut v___y_223_: *mut leanh::LeanObject,
    mut v___y_224_: *mut leanh::LeanObject,
    mut v___y_225_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_234_: u8 = 0;
    let mut v___x_235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_239_: u8 = 0;
    let mut v_unused_240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_244_: u8 = 0;
    let mut v___x_246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_248_: u8 = 0;
    let mut v_a_249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_252_: u8 = 0;
    let mut v___x_254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_256_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_227_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v___y_219_, v___y_222_, v___y_223_, v___y_224_, v___y_225_,
                );
                if leanh::lean_obj_tag(v___x_227_) == 0 {
                    v_a_228_ = leanh::lean_ctor_get(v___x_227_, 0);
                    leanh::lean_inc(v_a_228_);
                    leanh::lean_dec_ref_known(v___x_227_, 1);
                    v___x_229_ = l_Lean_MVarId_congrN(
                        v_a_228_, v___y_216_, v___x_217_, v___x_217_, v___y_222_, v___y_223_,
                        v___y_224_, v___y_225_,
                    );
                    if leanh::lean_obj_tag(v___x_229_) == 0 {
                        v_a_230_ = leanh::lean_ctor_get(v___x_229_, 0);
                        leanh::lean_inc(v_a_230_);
                        leanh::lean_dec_ref_known(v___x_229_, 1);
                        v___x_231_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                            v_a_230_, v___y_219_, v___y_222_, v___y_223_, v___y_224_, v___y_225_,
                        );
                        if leanh::lean_obj_tag(v___x_231_) == 0 {
                            v_isSharedCheck_239_ =
                                (!leanh::lean_is_exclusive(v___x_231_)) as u8;
                            if v_isSharedCheck_239_ == 0 {
                                v_unused_240_ = leanh::lean_ctor_get(v___x_231_, 0);
                                leanh::lean_dec(v_unused_240_);
                                v___x_233_ = v___x_231_;
                                v_isShared_234_ = v_isSharedCheck_239_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_231_);
                                v___x_233_ = leanh::lean_box(0);
                                v_isShared_234_ = v_isSharedCheck_239_;
                                state = 1;
                                continue;
                            }
                        } else {
                            return v___x_231_;
                        }
                    } else {
                        v_a_241_ = leanh::lean_ctor_get(v___x_229_, 0);
                        v_isSharedCheck_248_ = (!leanh::lean_is_exclusive(v___x_229_)) as u8;
                        if v_isSharedCheck_248_ == 0 {
                            v___x_243_ = v___x_229_;
                            v_isShared_244_ = v_isSharedCheck_248_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_241_);
                            leanh::lean_dec(v___x_229_);
                            v___x_243_ = leanh::lean_box(0);
                            v_isShared_244_ = v_isSharedCheck_248_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_249_ = leanh::lean_ctor_get(v___x_227_, 0);
                    v_isSharedCheck_256_ = (!leanh::lean_is_exclusive(v___x_227_)) as u8;
                    if v_isSharedCheck_256_ == 0 {
                        v___x_251_ = v___x_227_;
                        v_isShared_252_ = v_isSharedCheck_256_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_249_);
                        leanh::lean_dec(v___x_227_);
                        v___x_251_ = leanh::lean_box(0);
                        v_isShared_252_ = v_isSharedCheck_256_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_235_ = leanh::lean_box(0);
                if v_isShared_234_ == 0 {
                    leanh::lean_ctor_set(v___x_233_, 0, v___x_235_);
                    v___x_237_ = v___x_233_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_238_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_238_, 0, v___x_235_);
                    v___x_237_ = v_reuseFailAlloc_238_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_237_;
            }
            3 => {
                if v_isShared_244_ == 0 {
                    v___x_246_ = v___x_243_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_247_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_247_, 0, v_a_241_);
                    v___x_246_ = v_reuseFailAlloc_247_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_246_;
            }
            5 => {
                if v_isShared_252_ == 0 {
                    v___x_254_ = v___x_251_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_255_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_255_, 0, v_a_249_);
                    v___x_254_ = v_reuseFailAlloc_255_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_254_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___lam__0___boxed(
    mut v___y_257_: *mut leanh::LeanObject,
    mut v___x_258_: *mut leanh::LeanObject,
    mut v___y_259_: *mut leanh::LeanObject,
    mut v___y_260_: *mut leanh::LeanObject,
    mut v___y_261_: *mut leanh::LeanObject,
    mut v___y_262_: *mut leanh::LeanObject,
    mut v___y_263_: *mut leanh::LeanObject,
    mut v___y_264_: *mut leanh::LeanObject,
    mut v___y_265_: *mut leanh::LeanObject,
    mut v___y_266_: *mut leanh::LeanObject,
    mut v___y_267_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_876__boxed_268_: u8 = 0;
    let mut v_res_269_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_876__boxed_268_ = (leanh::lean_unbox(v___x_258_) as u8);
    v_res_269_ = l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___lam__0(
        v___y_257_,
        v___x_876__boxed_268_,
        v___y_259_,
        v___y_260_,
        v___y_261_,
        v___y_262_,
        v___y_263_,
        v___y_264_,
        v___y_265_,
        v___y_266_,
    );
    leanh::lean_dec(v___y_266_);
    leanh::lean_dec_ref(v___y_265_);
    leanh::lean_dec(v___y_264_);
    leanh::lean_dec_ref(v___y_263_);
    leanh::lean_dec(v___y_262_);
    leanh::lean_dec_ref(v___y_261_);
    leanh::lean_dec(v___y_260_);
    leanh::lean_dec_ref(v___y_259_);
    leanh::lean_dec(v___y_257_);
    return v_res_269_;
}
pub unsafe fn l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr(
    mut v_stx_279_: *mut leanh::LeanObject,
    mut v_a_280_: *mut leanh::LeanObject,
    mut v_a_281_: *mut leanh::LeanObject,
    mut v_a_282_: *mut leanh::LeanObject,
    mut v_a_283_: *mut leanh::LeanObject,
    mut v_a_284_: *mut leanh::LeanObject,
    mut v_a_285_: *mut leanh::LeanObject,
    mut v_a_286_: *mut leanh::LeanObject,
    mut v_a_287_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_290_: u8 = 0;
    let mut v___y_292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_307_: u8 = 0;
    let mut v___x_308_: u8 = 0;
    let mut v___x_309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_x3f_311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hugeDepth_313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_289_ = l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__4;
                leanh::lean_inc(v_stx_279_);
                v___x_290_ = l_Lean_Syntax_isOfKind(v_stx_279_, v___x_289_);
                if v___x_290_ == 0 {
                    leanh::lean_dec(v_stx_279_);
                    v___x_304_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0___redArg();
                    return v___x_304_;
                } else {
                    v___x_305_ = leanh::lean_unsigned_to_nat(1);
                    v___x_306_ = l_Lean_Syntax_getArg(v_stx_279_, v___x_305_);
                    leanh::lean_dec(v_stx_279_);
                    v___x_307_ = l_Lean_Syntax_isNone(v___x_306_);
                    if v___x_307_ == 0 {
                        leanh::lean_inc(v___x_306_);
                        v___x_308_ = l_Lean_Syntax_matchesNull(v___x_306_, v___x_305_);
                        if v___x_308_ == 0 {
                            leanh::lean_dec(v___x_306_);
                            v___x_309_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_spec__0___redArg();
                            return v___x_309_;
                        } else {
                            v___x_310_ = leanh::lean_unsigned_to_nat(0);
                            v_n_x3f_311_ = l_Lean_Syntax_getArg(v___x_306_, v___x_310_);
                            leanh::lean_dec(v___x_306_);
                            v___x_312_ = l_Lean_TSyntax_getNat(v_n_x3f_311_);
                            leanh::lean_dec(v_n_x3f_311_);
                            v___y_292_ = v_a_281_;
                            v___y_293_ = v_a_286_;
                            v___y_294_ = v_a_285_;
                            v___y_295_ = v_a_284_;
                            v___y_296_ = v_a_287_;
                            v___y_297_ = v_a_282_;
                            v___y_298_ = v_a_280_;
                            v___y_299_ = v_a_283_;
                            v___y_300_ = v___x_312_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_306_);
                        v_hugeDepth_313_ = leanh::lean_unsigned_to_nat(1000000);
                        v___y_292_ = v_a_281_;
                        v___y_293_ = v_a_286_;
                        v___y_294_ = v_a_285_;
                        v___y_295_ = v_a_284_;
                        v___y_296_ = v_a_287_;
                        v___y_297_ = v_a_282_;
                        v___y_298_ = v_a_280_;
                        v___y_299_ = v_a_283_;
                        v___y_300_ = v_hugeDepth_313_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_301_ = leanh::lean_box((v___x_290_) as usize);
                v___f_302_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___lam__0___boxed
                        as *mut core::ffi::c_void,
                    11,
                    2,
                );
                leanh::lean_closure_set(v___f_302_, 0, v___y_300_);
                leanh::lean_closure_set(v___f_302_, 1, v___x_301_);
                v___x_303_ = l_Lean_Elab_Tactic_withMainContext___redArg(
                    v___f_302_, v___y_298_, v___y_292_, v___y_297_, v___y_299_, v___y_295_,
                    v___y_294_, v___y_293_, v___y_296_,
                );
                return v___x_303_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___boxed(
    mut v_stx_314_: *mut leanh::LeanObject,
    mut v_a_315_: *mut leanh::LeanObject,
    mut v_a_316_: *mut leanh::LeanObject,
    mut v_a_317_: *mut leanh::LeanObject,
    mut v_a_318_: *mut leanh::LeanObject,
    mut v_a_319_: *mut leanh::LeanObject,
    mut v_a_320_: *mut leanh::LeanObject,
    mut v_a_321_: *mut leanh::LeanObject,
    mut v_a_322_: *mut leanh::LeanObject,
    mut v_a_323_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_324_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_324_ = l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr(
        v_stx_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_,
    );
    leanh::lean_dec(v_a_322_);
    leanh::lean_dec_ref(v_a_321_);
    leanh::lean_dec(v_a_320_);
    leanh::lean_dec_ref(v_a_319_);
    leanh::lean_dec(v_a_318_);
    leanh::lean_dec_ref(v_a_317_);
    leanh::lean_dec(v_a_316_);
    leanh::lean_dec_ref(v_a_315_);
    return v_res_324_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1()
-> *mut leanh::LeanObject {
    let mut v___x_333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_337_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_333_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_334_ = l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___closed__4;
    v___x_335_ = l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__2;
    v___x_336_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_337_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_333_, v___x_334_, v___x_335_, v___x_336_,
    );
    return v___x_337_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___boxed(
    mut v_a_338_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_339_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_339_ = l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1();
    return v_res_339_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3()
-> *mut leanh::LeanObject {
    let mut v___x_366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_368_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_366_ = l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1___closed__2;
    v___x_367_ = l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___closed__6;
    v___x_368_ = l_Lean_addBuiltinDeclarationRanges(v___x_366_, v___x_367_);
    return v___x_368_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3___boxed(
    mut v_a_369_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_370_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_370_ = l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3();
    return v_res_370_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Congr(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Congr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Congr_0__Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr___regBuiltin_Lean_Elab_Tactic_Lean_Elab_Tactic_evalCongr_declRange__3();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Congr(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Congr(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Congr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Congr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Congr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Congr(builtin);
}