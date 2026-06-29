// Lean compiler output
// Module: Lean.Elab.Tactic.BVDecide.BVDecide
// Imports: Lean.Meta.Tactic.BVDecide.Main
use crate::ffi::{lean_io_create_tempfile, lean_io_remove_file};
use crate::r#gen::Init::Prelude::{l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind};
use crate::r#gen::Init::System::IOError::lean_io_error_to_string;
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    l_Lean_Elab_Tactic_getMainGoal___redArg, l_Lean_Elab_Tactic_replaceMainGoal___redArg,
    l_Lean_Elab_Tactic_tacticElabAttribute, l_Lean_Elab_Tactic_withMainContext___redArg,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Message::l_Lean_MessageData_ofFormat;
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Attr::l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg;
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Main::{
    initialize_Lean_Meta_Tactic_BVDecide_Main, l_Lean_Meta_Tactic_BVDecide_bvDecide,
    runtime_initialize_Lean_Meta_Tactic_BVDecide_Main,
};
use crate::r#gen::Lean::Meta::Tactic::BVDecide::TacticContext::l_Lean_Meta_Tactic_BVDecide_TacticContext_new;
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__0_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__1_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__2_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__3_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [98, 118, 68, 101, 99, 105, 100, 101, 0],
};
static mut l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__4_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__4_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__4_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__4_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__4_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__4_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__3_value)
            as *mut crate::leanh::LeanObject,
        5664884566237612082 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__5_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [111, 112, 116, 67, 111, 110, 102, 105, 103, 0],
};
static mut l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__5_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__6_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__6_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__6_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__6_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__6_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__6_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__6_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__5_value)
            as *mut crate::leanh::LeanObject,
        3488656302031949961 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_BVDecide_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_BVDecide_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_BVDecide_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__1_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [66, 86, 68, 101, 99, 105, 100, 101, 0]};
static mut l___private_Lean_Elab_Tactic_BVDecide_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_BVDecide_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__2_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 118, 97, 108, 66, 118, 68, 101, 99, 105, 100, 101, 0]};
static mut l___private_Lean_Elab_Tactic_BVDecide_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_BVDecide_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_BVDecide_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__0_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_BVDecide_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__2_value) as *mut crate::leanh::LeanObject,12733524109236233889 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_BVDecide_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__3_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__1_value) as *mut crate::leanh::LeanObject,11988787035136614332 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_BVDecide_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__3_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__2_value) as *mut crate::leanh::LeanObject,10210427704931983870 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_BVDecide_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_335_ = crate::leanh::lean_box(0);
    v___x_336_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_337_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_337_, 0, v___x_336_);
    crate::leanh::lean_ctor_set(v___x_337_, 1, v___x_335_);
    return v___x_337_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_339_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg___closed__0);
    v___x_340_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_340_, 0, v___x_339_);
    return v___x_340_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg___boxed(
    mut v___y_341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_342_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
    return v_res_342_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0(
    mut v_00_u03b1_343_: *mut crate::leanh::LeanObject,
    mut v___y_344_: *mut crate::leanh::LeanObject,
    mut v___y_345_: *mut crate::leanh::LeanObject,
    mut v___y_346_: *mut crate::leanh::LeanObject,
    mut v___y_347_: *mut crate::leanh::LeanObject,
    mut v___y_348_: *mut crate::leanh::LeanObject,
    mut v___y_349_: *mut crate::leanh::LeanObject,
    mut v___y_350_: *mut crate::leanh::LeanObject,
    mut v___y_351_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_353_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
    return v___x_353_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___boxed(
    mut v_00_u03b1_354_: *mut crate::leanh::LeanObject,
    mut v___y_355_: *mut crate::leanh::LeanObject,
    mut v___y_356_: *mut crate::leanh::LeanObject,
    mut v___y_357_: *mut crate::leanh::LeanObject,
    mut v___y_358_: *mut crate::leanh::LeanObject,
    mut v___y_359_: *mut crate::leanh::LeanObject,
    mut v___y_360_: *mut crate::leanh::LeanObject,
    mut v___y_361_: *mut crate::leanh::LeanObject,
    mut v___y_362_: *mut crate::leanh::LeanObject,
    mut v___y_363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_364_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0(
            v_00_u03b1_354_,
            v___y_355_,
            v___y_356_,
            v___y_357_,
            v___y_358_,
            v___y_359_,
            v___y_360_,
            v___y_361_,
            v___y_362_,
        );
    crate::leanh::lean_dec(v___y_362_);
    crate::leanh::lean_dec_ref(v___y_361_);
    crate::leanh::lean_dec(v___y_360_);
    crate::leanh::lean_dec_ref(v___y_359_);
    crate::leanh::lean_dec(v___y_358_);
    crate::leanh::lean_dec_ref(v___y_357_);
    crate::leanh::lean_dec(v___y_356_);
    crate::leanh::lean_dec_ref(v___y_355_);
    return v_res_364_;
}
pub unsafe fn l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg___lam__0(
    mut v_snd_365_: *mut crate::leanh::LeanObject,
    mut v___y_366_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_373_: u8 = 0;
    let mut v___x_375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_377_: u8 = 0;
    let mut v_a_378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_381_: u8 = 0;
    let mut v_ref_382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_390_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_369_ = lean_io_remove_file(v_snd_365_);
                if crate::leanh::lean_obj_tag(v___x_369_) == 0 {
                    v_a_370_ = crate::leanh::lean_ctor_get(v___x_369_, 0);
                    v_isSharedCheck_377_ = (!crate::leanh::lean_is_exclusive(v___x_369_)) as u8;
                    if v_isSharedCheck_377_ == 0 {
                        v___x_372_ = v___x_369_;
                        v_isShared_373_ = v_isSharedCheck_377_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_370_);
                        crate::leanh::lean_dec(v___x_369_);
                        v___x_372_ = crate::leanh::lean_box(0);
                        v_isShared_373_ = v_isSharedCheck_377_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_378_ = crate::leanh::lean_ctor_get(v___x_369_, 0);
                    v_isSharedCheck_390_ = (!crate::leanh::lean_is_exclusive(v___x_369_)) as u8;
                    if v_isSharedCheck_390_ == 0 {
                        v___x_380_ = v___x_369_;
                        v_isShared_381_ = v_isSharedCheck_390_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_378_);
                        crate::leanh::lean_dec(v___x_369_);
                        v___x_380_ = crate::leanh::lean_box(0);
                        v_isShared_381_ = v_isSharedCheck_390_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_373_ == 0 {
                    v___x_375_ = v___x_372_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_376_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_376_, 0, v_a_370_);
                    v___x_375_ = v_reuseFailAlloc_376_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_375_;
            }
            3 => {
                v_ref_382_ = crate::leanh::lean_ctor_get(v___y_366_, 5);
                v___x_383_ = lean_io_error_to_string(v_a_378_);
                v___x_384_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_384_, 0, v___x_383_);
                v___x_385_ = l_Lean_MessageData_ofFormat(v___x_384_);
                crate::leanh::lean_inc(v_ref_382_);
                v___x_386_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_386_, 0, v_ref_382_);
                crate::leanh::lean_ctor_set(v___x_386_, 1, v___x_385_);
                if v_isShared_381_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_380_, 0, v___x_386_);
                    v___x_388_ = v___x_380_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_389_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_389_, 0, v___x_386_);
                    v___x_388_ = v_reuseFailAlloc_389_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_388_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg___lam__0___boxed(
    mut v_snd_391_: *mut crate::leanh::LeanObject,
    mut v___y_392_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_393_: *mut crate::leanh::LeanObject,
    mut v___y_394_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_395_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg___lam__0(v_snd_391_, v___y_392_, v_a_x3f_393_);
    crate::leanh::lean_dec(v_a_x3f_393_);
    crate::leanh::lean_dec_ref(v___y_392_);
    crate::leanh::lean_dec_ref(v_snd_391_);
    return v_res_395_;
}
pub unsafe fn l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg(
    mut v_f_396_: *mut crate::leanh::LeanObject,
    mut v___y_397_: *mut crate::leanh::LeanObject,
    mut v___y_398_: *mut crate::leanh::LeanObject,
    mut v___y_399_: *mut crate::leanh::LeanObject,
    mut v___y_400_: *mut crate::leanh::LeanObject,
    mut v___y_401_: *mut crate::leanh::LeanObject,
    mut v___y_402_: *mut crate::leanh::LeanObject,
    mut v___y_403_: *mut crate::leanh::LeanObject,
    mut v___y_404_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_414_: u8 = 0;
    let mut v___x_416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_420_: u8 = 0;
    let mut v___x_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_424_: u8 = 0;
    let mut v_unused_425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_429_: u8 = 0;
    let mut v___x_431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_433_: u8 = 0;
    let mut v_reuseFailAlloc_434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_435_: u8 = 0;
    let mut v_a_436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_441_: u8 = 0;
    let mut v___x_443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_445_: u8 = 0;
    let mut v_unused_446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_450_: u8 = 0;
    let mut v___x_452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_454_: u8 = 0;
    let mut v_a_455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_458_: u8 = 0;
    let mut v_ref_459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_467_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_406_ = lean_io_create_tempfile();
                if crate::leanh::lean_obj_tag(v___x_406_) == 0 {
                    v_a_407_ = crate::leanh::lean_ctor_get(v___x_406_, 0);
                    crate::leanh::lean_inc(v_a_407_);
                    crate::leanh::lean_dec_ref_known(v___x_406_, 1);
                    v_fst_408_ = crate::leanh::lean_ctor_get(v_a_407_, 0);
                    crate::leanh::lean_inc(v_fst_408_);
                    v_snd_409_ = crate::leanh::lean_ctor_get(v_a_407_, 1);
                    crate::leanh::lean_inc_n(v_snd_409_, 2);
                    crate::leanh::lean_dec(v_a_407_);
                    crate::leanh::lean_inc(v___y_404_);
                    crate::leanh::lean_inc_ref(v___y_403_);
                    crate::leanh::lean_inc(v___y_402_);
                    crate::leanh::lean_inc_ref(v___y_401_);
                    crate::leanh::lean_inc(v___y_400_);
                    crate::leanh::lean_inc_ref(v___y_399_);
                    crate::leanh::lean_inc(v___y_398_);
                    crate::leanh::lean_inc_ref(v___y_397_);
                    v_r_410_ = crate::leanh::lean_apply_11(
                        v_f_396_,
                        v_fst_408_,
                        v_snd_409_,
                        v___y_397_,
                        v___y_398_,
                        v___y_399_,
                        v___y_400_,
                        v___y_401_,
                        v___y_402_,
                        v___y_403_,
                        v___y_404_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v_r_410_) == 0 {
                        v_a_411_ = crate::leanh::lean_ctor_get(v_r_410_, 0);
                        v_isSharedCheck_435_ = (!crate::leanh::lean_is_exclusive(v_r_410_)) as u8;
                        if v_isSharedCheck_435_ == 0 {
                            v___x_413_ = v_r_410_;
                            v_isShared_414_ = v_isSharedCheck_435_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_411_);
                            crate::leanh::lean_dec(v_r_410_);
                            v___x_413_ = crate::leanh::lean_box(0);
                            v_isShared_414_ = v_isSharedCheck_435_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_436_ = crate::leanh::lean_ctor_get(v_r_410_, 0);
                        crate::leanh::lean_inc(v_a_436_);
                        crate::leanh::lean_dec_ref_known(v_r_410_, 1);
                        v___x_437_ = crate::leanh::lean_box(0);
                        v___x_438_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg___lam__0(v_snd_409_, v___y_403_, v___x_437_);
                        crate::leanh::lean_dec(v_snd_409_);
                        if crate::leanh::lean_obj_tag(v___x_438_) == 0 {
                            v_isSharedCheck_445_ =
                                (!crate::leanh::lean_is_exclusive(v___x_438_)) as u8;
                            if v_isSharedCheck_445_ == 0 {
                                v_unused_446_ = crate::leanh::lean_ctor_get(v___x_438_, 0);
                                crate::leanh::lean_dec(v_unused_446_);
                                v___x_440_ = v___x_438_;
                                v_isShared_441_ = v_isSharedCheck_445_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_438_);
                                v___x_440_ = crate::leanh::lean_box(0);
                                v_isShared_441_ = v_isSharedCheck_445_;
                                state = 7;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_436_);
                            v_a_447_ = crate::leanh::lean_ctor_get(v___x_438_, 0);
                            v_isSharedCheck_454_ =
                                (!crate::leanh::lean_is_exclusive(v___x_438_)) as u8;
                            if v_isSharedCheck_454_ == 0 {
                                v___x_449_ = v___x_438_;
                                v_isShared_450_ = v_isSharedCheck_454_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_447_);
                                crate::leanh::lean_dec(v___x_438_);
                                v___x_449_ = crate::leanh::lean_box(0);
                                v_isShared_450_ = v_isSharedCheck_454_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_396_);
                    v_a_455_ = crate::leanh::lean_ctor_get(v___x_406_, 0);
                    v_isSharedCheck_467_ = (!crate::leanh::lean_is_exclusive(v___x_406_)) as u8;
                    if v_isSharedCheck_467_ == 0 {
                        v___x_457_ = v___x_406_;
                        v_isShared_458_ = v_isSharedCheck_467_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_455_);
                        crate::leanh::lean_dec(v___x_406_);
                        v___x_457_ = crate::leanh::lean_box(0);
                        v_isShared_458_ = v_isSharedCheck_467_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_a_411_);
                if v_isShared_414_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_413_, 1);
                    v___x_416_ = v___x_413_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_434_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_434_, 0, v_a_411_);
                    v___x_416_ = v_reuseFailAlloc_434_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_417_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg___lam__0(v_snd_409_, v___y_403_, v___x_416_);
                crate::leanh::lean_dec_ref(v___x_416_);
                crate::leanh::lean_dec(v_snd_409_);
                if crate::leanh::lean_obj_tag(v___x_417_) == 0 {
                    v_isSharedCheck_424_ = (!crate::leanh::lean_is_exclusive(v___x_417_)) as u8;
                    if v_isSharedCheck_424_ == 0 {
                        v_unused_425_ = crate::leanh::lean_ctor_get(v___x_417_, 0);
                        crate::leanh::lean_dec(v_unused_425_);
                        v___x_419_ = v___x_417_;
                        v_isShared_420_ = v_isSharedCheck_424_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_417_);
                        v___x_419_ = crate::leanh::lean_box(0);
                        v_isShared_420_ = v_isSharedCheck_424_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_411_);
                    v_a_426_ = crate::leanh::lean_ctor_get(v___x_417_, 0);
                    v_isSharedCheck_433_ = (!crate::leanh::lean_is_exclusive(v___x_417_)) as u8;
                    if v_isSharedCheck_433_ == 0 {
                        v___x_428_ = v___x_417_;
                        v_isShared_429_ = v_isSharedCheck_433_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_426_);
                        crate::leanh::lean_dec(v___x_417_);
                        v___x_428_ = crate::leanh::lean_box(0);
                        v_isShared_429_ = v_isSharedCheck_433_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_420_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_419_, 0, v_a_411_);
                    v___x_422_ = v___x_419_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_423_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_423_, 0, v_a_411_);
                    v___x_422_ = v_reuseFailAlloc_423_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_422_;
            }
            5 => {
                if v_isShared_429_ == 0 {
                    v___x_431_ = v___x_428_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_432_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_432_, 0, v_a_426_);
                    v___x_431_ = v_reuseFailAlloc_432_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_431_;
            }
            7 => {
                if v_isShared_441_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_440_, 1);
                    crate::leanh::lean_ctor_set(v___x_440_, 0, v_a_436_);
                    v___x_443_ = v___x_440_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_444_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_444_, 0, v_a_436_);
                    v___x_443_ = v_reuseFailAlloc_444_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_443_;
            }
            9 => {
                if v_isShared_450_ == 0 {
                    v___x_452_ = v___x_449_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_453_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_453_, 0, v_a_447_);
                    v___x_452_ = v_reuseFailAlloc_453_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_452_;
            }
            11 => {
                v_ref_459_ = crate::leanh::lean_ctor_get(v___y_403_, 5);
                v___x_460_ = lean_io_error_to_string(v_a_455_);
                v___x_461_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_461_, 0, v___x_460_);
                v___x_462_ = l_Lean_MessageData_ofFormat(v___x_461_);
                crate::leanh::lean_inc(v_ref_459_);
                v___x_463_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_463_, 0, v_ref_459_);
                crate::leanh::lean_ctor_set(v___x_463_, 1, v___x_462_);
                if v_isShared_458_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_457_, 0, v___x_463_);
                    v___x_465_ = v___x_457_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_466_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_466_, 0, v___x_463_);
                    v___x_465_ = v_reuseFailAlloc_466_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_465_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg___boxed(
    mut v_f_468_: *mut crate::leanh::LeanObject,
    mut v___y_469_: *mut crate::leanh::LeanObject,
    mut v___y_470_: *mut crate::leanh::LeanObject,
    mut v___y_471_: *mut crate::leanh::LeanObject,
    mut v___y_472_: *mut crate::leanh::LeanObject,
    mut v___y_473_: *mut crate::leanh::LeanObject,
    mut v___y_474_: *mut crate::leanh::LeanObject,
    mut v___y_475_: *mut crate::leanh::LeanObject,
    mut v___y_476_: *mut crate::leanh::LeanObject,
    mut v___y_477_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_478_ =
        l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg(
            v_f_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_,
            v___y_475_, v___y_476_,
        );
    crate::leanh::lean_dec(v___y_476_);
    crate::leanh::lean_dec_ref(v___y_475_);
    crate::leanh::lean_dec(v___y_474_);
    crate::leanh::lean_dec_ref(v___y_473_);
    crate::leanh::lean_dec(v___y_472_);
    crate::leanh::lean_dec_ref(v___y_471_);
    crate::leanh::lean_dec(v___y_470_);
    crate::leanh::lean_dec_ref(v___y_469_);
    return v_res_478_;
}
pub unsafe fn l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1(
    mut v_00_u03b1_479_: *mut crate::leanh::LeanObject,
    mut v_f_480_: *mut crate::leanh::LeanObject,
    mut v___y_481_: *mut crate::leanh::LeanObject,
    mut v___y_482_: *mut crate::leanh::LeanObject,
    mut v___y_483_: *mut crate::leanh::LeanObject,
    mut v___y_484_: *mut crate::leanh::LeanObject,
    mut v___y_485_: *mut crate::leanh::LeanObject,
    mut v___y_486_: *mut crate::leanh::LeanObject,
    mut v___y_487_: *mut crate::leanh::LeanObject,
    mut v___y_488_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_490_ =
        l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg(
            v_f_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_,
            v___y_487_, v___y_488_,
        );
    return v___x_490_;
}
pub unsafe fn l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___boxed(
    mut v_00_u03b1_491_: *mut crate::leanh::LeanObject,
    mut v_f_492_: *mut crate::leanh::LeanObject,
    mut v___y_493_: *mut crate::leanh::LeanObject,
    mut v___y_494_: *mut crate::leanh::LeanObject,
    mut v___y_495_: *mut crate::leanh::LeanObject,
    mut v___y_496_: *mut crate::leanh::LeanObject,
    mut v___y_497_: *mut crate::leanh::LeanObject,
    mut v___y_498_: *mut crate::leanh::LeanObject,
    mut v___y_499_: *mut crate::leanh::LeanObject,
    mut v___y_500_: *mut crate::leanh::LeanObject,
    mut v___y_501_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_502_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1(
        v_00_u03b1_491_,
        v_f_492_,
        v___y_493_,
        v___y_494_,
        v___y_495_,
        v___y_496_,
        v___y_497_,
        v___y_498_,
        v___y_499_,
        v___y_500_,
    );
    crate::leanh::lean_dec(v___y_500_);
    crate::leanh::lean_dec_ref(v___y_499_);
    crate::leanh::lean_dec(v___y_498_);
    crate::leanh::lean_dec_ref(v___y_497_);
    crate::leanh::lean_dec(v___y_496_);
    crate::leanh::lean_dec_ref(v___y_495_);
    crate::leanh::lean_dec(v___y_494_);
    crate::leanh::lean_dec_ref(v___y_493_);
    return v_res_502_;
}
pub unsafe fn l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__0(
    mut v_a_503_: *mut crate::leanh::LeanObject,
    mut v___y_504_: *mut crate::leanh::LeanObject,
    mut v___y_505_: *mut crate::leanh::LeanObject,
    mut v___y_506_: *mut crate::leanh::LeanObject,
    mut v___y_507_: *mut crate::leanh::LeanObject,
    mut v___y_508_: *mut crate::leanh::LeanObject,
    mut v___y_509_: *mut crate::leanh::LeanObject,
    mut v___y_510_: *mut crate::leanh::LeanObject,
    mut v___y_511_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_520_: u8 = 0;
    let mut v___x_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_525_: u8 = 0;
    let mut v_unused_526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_530_: u8 = 0;
    let mut v___x_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_534_: u8 = 0;
    let mut v_a_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_538_: u8 = 0;
    let mut v___x_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_542_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_513_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v___y_505_, v___y_508_, v___y_509_, v___y_510_, v___y_511_,
                );
                if crate::leanh::lean_obj_tag(v___x_513_) == 0 {
                    v_a_514_ = crate::leanh::lean_ctor_get(v___x_513_, 0);
                    crate::leanh::lean_inc(v_a_514_);
                    crate::leanh::lean_dec_ref_known(v___x_513_, 1);
                    v___x_515_ = l_Lean_Meta_Tactic_BVDecide_bvDecide(
                        v_a_514_, v_a_503_, v___y_508_, v___y_509_, v___y_510_, v___y_511_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_515_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_515_, 1);
                        v___x_516_ = crate::leanh::lean_box(0);
                        v___x_517_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                            v___x_516_, v___y_505_, v___y_508_, v___y_509_, v___y_510_, v___y_511_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_517_) == 0 {
                            v_isSharedCheck_525_ =
                                (!crate::leanh::lean_is_exclusive(v___x_517_)) as u8;
                            if v_isSharedCheck_525_ == 0 {
                                v_unused_526_ = crate::leanh::lean_ctor_get(v___x_517_, 0);
                                crate::leanh::lean_dec(v_unused_526_);
                                v___x_519_ = v___x_517_;
                                v_isShared_520_ = v_isSharedCheck_525_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_517_);
                                v___x_519_ = crate::leanh::lean_box(0);
                                v_isShared_520_ = v_isSharedCheck_525_;
                                state = 1;
                                continue;
                            }
                        } else {
                            return v___x_517_;
                        }
                    } else {
                        v_a_527_ = crate::leanh::lean_ctor_get(v___x_515_, 0);
                        v_isSharedCheck_534_ = (!crate::leanh::lean_is_exclusive(v___x_515_)) as u8;
                        if v_isSharedCheck_534_ == 0 {
                            v___x_529_ = v___x_515_;
                            v_isShared_530_ = v_isSharedCheck_534_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_527_);
                            crate::leanh::lean_dec(v___x_515_);
                            v___x_529_ = crate::leanh::lean_box(0);
                            v_isShared_530_ = v_isSharedCheck_534_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_a_503_);
                    v_a_535_ = crate::leanh::lean_ctor_get(v___x_513_, 0);
                    v_isSharedCheck_542_ = (!crate::leanh::lean_is_exclusive(v___x_513_)) as u8;
                    if v_isSharedCheck_542_ == 0 {
                        v___x_537_ = v___x_513_;
                        v_isShared_538_ = v_isSharedCheck_542_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_535_);
                        crate::leanh::lean_dec(v___x_513_);
                        v___x_537_ = crate::leanh::lean_box(0);
                        v_isShared_538_ = v_isSharedCheck_542_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_521_ = crate::leanh::lean_box(0);
                if v_isShared_520_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_519_, 0, v___x_521_);
                    v___x_523_ = v___x_519_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_524_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_524_, 0, v___x_521_);
                    v___x_523_ = v_reuseFailAlloc_524_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_523_;
            }
            3 => {
                if v_isShared_530_ == 0 {
                    v___x_532_ = v___x_529_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_533_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_533_, 0, v_a_527_);
                    v___x_532_ = v_reuseFailAlloc_533_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_532_;
            }
            5 => {
                if v_isShared_538_ == 0 {
                    v___x_540_ = v___x_537_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_541_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_541_, 0, v_a_535_);
                    v___x_540_ = v_reuseFailAlloc_541_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_540_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__0___boxed(
    mut v_a_543_: *mut crate::leanh::LeanObject,
    mut v___y_544_: *mut crate::leanh::LeanObject,
    mut v___y_545_: *mut crate::leanh::LeanObject,
    mut v___y_546_: *mut crate::leanh::LeanObject,
    mut v___y_547_: *mut crate::leanh::LeanObject,
    mut v___y_548_: *mut crate::leanh::LeanObject,
    mut v___y_549_: *mut crate::leanh::LeanObject,
    mut v___y_550_: *mut crate::leanh::LeanObject,
    mut v___y_551_: *mut crate::leanh::LeanObject,
    mut v___y_552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_553_ = l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__0(
        v_a_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_,
        v___y_550_, v___y_551_,
    );
    crate::leanh::lean_dec(v___y_551_);
    crate::leanh::lean_dec_ref(v___y_550_);
    crate::leanh::lean_dec(v___y_549_);
    crate::leanh::lean_dec_ref(v___y_548_);
    crate::leanh::lean_dec(v___y_547_);
    crate::leanh::lean_dec_ref(v___y_546_);
    crate::leanh::lean_dec(v___y_545_);
    crate::leanh::lean_dec_ref(v___y_544_);
    return v_res_553_;
}
pub unsafe fn l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__1(
    mut v_a_554_: *mut crate::leanh::LeanObject,
    mut v_x_555_: *mut crate::leanh::LeanObject,
    mut v_lratFile_556_: *mut crate::leanh::LeanObject,
    mut v___y_557_: *mut crate::leanh::LeanObject,
    mut v___y_558_: *mut crate::leanh::LeanObject,
    mut v___y_559_: *mut crate::leanh::LeanObject,
    mut v___y_560_: *mut crate::leanh::LeanObject,
    mut v___y_561_: *mut crate::leanh::LeanObject,
    mut v___y_562_: *mut crate::leanh::LeanObject,
    mut v___y_563_: *mut crate::leanh::LeanObject,
    mut v___y_564_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_573_: u8 = 0;
    let mut v___x_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_577_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_566_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_new(
                    v_lratFile_556_,
                    v_a_554_,
                    v___y_559_,
                    v___y_560_,
                    v___y_561_,
                    v___y_562_,
                    v___y_563_,
                    v___y_564_,
                );
                if crate::leanh::lean_obj_tag(v___x_566_) == 0 {
                    v_a_567_ = crate::leanh::lean_ctor_get(v___x_566_, 0);
                    crate::leanh::lean_inc(v_a_567_);
                    crate::leanh::lean_dec_ref_known(v___x_566_, 1);
                    v___f_568_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__0___boxed
                            as *mut core::ffi::c_void,
                        10,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_568_, 0, v_a_567_);
                    v___x_569_ = l_Lean_Elab_Tactic_withMainContext___redArg(
                        v___f_568_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_,
                        v___y_562_, v___y_563_, v___y_564_,
                    );
                    return v___x_569_;
                } else {
                    v_a_570_ = crate::leanh::lean_ctor_get(v___x_566_, 0);
                    v_isSharedCheck_577_ = (!crate::leanh::lean_is_exclusive(v___x_566_)) as u8;
                    if v_isSharedCheck_577_ == 0 {
                        v___x_572_ = v___x_566_;
                        v_isShared_573_ = v_isSharedCheck_577_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_570_);
                        crate::leanh::lean_dec(v___x_566_);
                        v___x_572_ = crate::leanh::lean_box(0);
                        v_isShared_573_ = v_isSharedCheck_577_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_573_ == 0 {
                    v___x_575_ = v___x_572_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_576_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_576_, 0, v_a_570_);
                    v___x_575_ = v_reuseFailAlloc_576_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_575_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__1___boxed(
    mut v_a_578_: *mut crate::leanh::LeanObject,
    mut v_x_579_: *mut crate::leanh::LeanObject,
    mut v_lratFile_580_: *mut crate::leanh::LeanObject,
    mut v___y_581_: *mut crate::leanh::LeanObject,
    mut v___y_582_: *mut crate::leanh::LeanObject,
    mut v___y_583_: *mut crate::leanh::LeanObject,
    mut v___y_584_: *mut crate::leanh::LeanObject,
    mut v___y_585_: *mut crate::leanh::LeanObject,
    mut v___y_586_: *mut crate::leanh::LeanObject,
    mut v___y_587_: *mut crate::leanh::LeanObject,
    mut v___y_588_: *mut crate::leanh::LeanObject,
    mut v___y_589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_590_ = l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__1(
        v_a_578_,
        v_x_579_,
        v_lratFile_580_,
        v___y_581_,
        v___y_582_,
        v___y_583_,
        v___y_584_,
        v___y_585_,
        v___y_586_,
        v___y_587_,
        v___y_588_,
    );
    crate::leanh::lean_dec(v___y_588_);
    crate::leanh::lean_dec_ref(v___y_587_);
    crate::leanh::lean_dec(v___y_586_);
    crate::leanh::lean_dec_ref(v___y_585_);
    crate::leanh::lean_dec(v___y_584_);
    crate::leanh::lean_dec_ref(v___y_583_);
    crate::leanh::lean_dec(v___y_582_);
    crate::leanh::lean_dec_ref(v___y_581_);
    crate::leanh::lean_dec(v_x_579_);
    return v_res_590_;
}
pub unsafe fn l_Lean_Elab_Tactic_BVDecide_evalBvDecide(
    mut v_x_606_: *mut crate::leanh::LeanObject,
    mut v_a_607_: *mut crate::leanh::LeanObject,
    mut v_a_608_: *mut crate::leanh::LeanObject,
    mut v_a_609_: *mut crate::leanh::LeanObject,
    mut v_a_610_: *mut crate::leanh::LeanObject,
    mut v_a_611_: *mut crate::leanh::LeanObject,
    mut v_a_612_: *mut crate::leanh::LeanObject,
    mut v_a_613_: *mut crate::leanh::LeanObject,
    mut v_a_614_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_617_: u8 = 0;
    let mut v___x_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_622_: u8 = 0;
    let mut v___x_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_625_: u8 = 0;
    let mut v___x_626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_627_: u8 = 0;
    let mut v___x_628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_636_: u8 = 0;
    let mut v___x_638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_640_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_616_ = l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__4;
                crate::leanh::lean_inc(v_x_606_);
                v___x_617_ = l_Lean_Syntax_isOfKind(v_x_606_, v___x_616_);
                if v___x_617_ == 0 {
                    crate::leanh::lean_dec(v_x_606_);
                    v___x_618_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
                    return v___x_618_;
                } else {
                    v___x_619_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_620_ = l_Lean_Syntax_getArg(v_x_606_, v___x_619_);
                    crate::leanh::lean_dec(v_x_606_);
                    v___x_621_ = l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__6;
                    crate::leanh::lean_inc(v___x_620_);
                    v___x_622_ = l_Lean_Syntax_isOfKind(v___x_620_, v___x_621_);
                    if v___x_622_ == 0 {
                        crate::leanh::lean_dec(v___x_620_);
                        v___x_623_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
                        return v___x_623_;
                    } else {
                        v___x_624_ = crate::leanh::lean_unsigned_to_nat(10);
                        v___x_625_ = 0;
                        v___x_626_ = crate::leanh::lean_unsigned_to_nat(100000);
                        v___x_627_ = 0;
                        v___x_628_ = crate::leanh::lean_alloc_ctor(0, 2, (11) as u32);
                        crate::leanh::lean_ctor_set(v___x_628_, 0, v___x_624_);
                        crate::leanh::lean_ctor_set(v___x_628_, 1, v___x_626_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_628_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                            v___x_622_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_628_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
                            v___x_622_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_628_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 2) as u32,
                            v___x_625_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_628_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 3) as u32,
                            v___x_622_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_628_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 4) as u32,
                            v___x_622_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_628_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 5) as u32,
                            v___x_622_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_628_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 6) as u32,
                            v___x_622_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_628_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 7) as u32,
                            v___x_622_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_628_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 8) as u32,
                            v___x_625_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_628_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 9) as u32,
                            v___x_625_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_628_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 10) as u32,
                            v___x_627_,
                        );
                        v___x_629_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(
                            v___x_620_, v___x_628_, v___x_622_, v_a_607_, v_a_613_, v_a_614_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_629_) == 0 {
                            v_a_630_ = crate::leanh::lean_ctor_get(v___x_629_, 0);
                            crate::leanh::lean_inc(v_a_630_);
                            crate::leanh::lean_dec_ref_known(v___x_629_, 1);
                            v___f_631_ = crate::leanh::lean_alloc_closure(
                                l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__1___boxed
                                    as *mut core::ffi::c_void,
                                12,
                                1,
                            );
                            crate::leanh::lean_closure_set(v___f_631_, 0, v_a_630_);
                            v___x_632_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg(v___f_631_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_);
                            return v___x_632_;
                        } else {
                            v_a_633_ = crate::leanh::lean_ctor_get(v___x_629_, 0);
                            v_isSharedCheck_640_ =
                                (!crate::leanh::lean_is_exclusive(v___x_629_)) as u8;
                            if v_isSharedCheck_640_ == 0 {
                                v___x_635_ = v___x_629_;
                                v_isShared_636_ = v_isSharedCheck_640_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_633_);
                                crate::leanh::lean_dec(v___x_629_);
                                v___x_635_ = crate::leanh::lean_box(0);
                                v_isShared_636_ = v_isSharedCheck_640_;
                                state = 1;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                if v_isShared_636_ == 0 {
                    v___x_638_ = v___x_635_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_639_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_639_, 0, v_a_633_);
                    v___x_638_ = v_reuseFailAlloc_639_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_638_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_BVDecide_evalBvDecide___boxed(
    mut v_x_641_: *mut crate::leanh::LeanObject,
    mut v_a_642_: *mut crate::leanh::LeanObject,
    mut v_a_643_: *mut crate::leanh::LeanObject,
    mut v_a_644_: *mut crate::leanh::LeanObject,
    mut v_a_645_: *mut crate::leanh::LeanObject,
    mut v_a_646_: *mut crate::leanh::LeanObject,
    mut v_a_647_: *mut crate::leanh::LeanObject,
    mut v_a_648_: *mut crate::leanh::LeanObject,
    mut v_a_649_: *mut crate::leanh::LeanObject,
    mut v_a_650_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_651_ = l_Lean_Elab_Tactic_BVDecide_evalBvDecide(
        v_x_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_,
    );
    crate::leanh::lean_dec(v_a_649_);
    crate::leanh::lean_dec_ref(v_a_648_);
    crate::leanh::lean_dec(v_a_647_);
    crate::leanh::lean_dec_ref(v_a_646_);
    crate::leanh::lean_dec(v_a_645_);
    crate::leanh::lean_dec_ref(v_a_644_);
    crate::leanh::lean_dec(v_a_643_);
    crate::leanh::lean_dec_ref(v_a_642_);
    return v_res_651_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_BVDecide_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_662_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_663_ = l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__4;
    v___x_664_ = l___private_Lean_Elab_Tactic_BVDecide_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__3;
    v___x_665_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_BVDecide_evalBvDecide___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_666_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_662_, v___x_663_, v___x_664_, v___x_665_,
    );
    return v___x_666_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_BVDecide_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___boxed(
    mut v_a_667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_668_ = l___private_Lean_Elab_Tactic_BVDecide_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1();
    return v_res_668_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_BVDecide_BVDecide(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Main(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_BVDecide_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_BVDecide_BVDecide(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_BVDecide_BVDecide(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_BVDecide_Main(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_BVDecide_BVDecide(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_BVDecide_BVDecide(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_BVDecide_BVDecide(builtin);
}
