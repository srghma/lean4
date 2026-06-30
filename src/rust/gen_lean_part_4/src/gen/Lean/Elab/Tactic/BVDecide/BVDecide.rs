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
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__0_value:
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
static mut l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__1_value:
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
static mut l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__2_value:
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
static mut l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__3_value:
    leanh::LeanStringObject<9> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__3_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__4_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__4_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__4_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__4_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__2_value)
            as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__4_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__4_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__3_value)
            as *mut leanh::LeanObject,
        5664884566237612082 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__5_value:
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
    m_data: [111, 112, 116, 67, 111, 110, 102, 105, 103, 0],
};
static mut l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__5_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__6_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__6_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__6_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__6_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__6_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__2_value)
            as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__6_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__6_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__5_value)
            as *mut leanh::LeanObject,
        3488656302031949961 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__6_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_BVDecide_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_BVDecide_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_BVDecide_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__1_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [66, 86, 68, 101, 99, 105, 100, 101, 0]};
static mut l___private_Lean_Elab_Tactic_BVDecide_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_BVDecide_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__2_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 118, 97, 108, 66, 118, 68, 101, 99, 105, 100, 101, 0]};
static mut l___private_Lean_Elab_Tactic_BVDecide_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__2_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_BVDecide_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_BVDecide_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__0_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_BVDecide_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__3_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__2_value) as *mut leanh::LeanObject,12733524109236233889 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_BVDecide_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__3_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__3_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__1_value) as *mut leanh::LeanObject,11988787035136614332 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_BVDecide_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__3_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__2_value) as *mut leanh::LeanObject,10210427704931983870 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_BVDecide_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__3_value) as *mut leanh::LeanObject;
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_337_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_335_ = leanh::lean_box(0);
    v___x_336_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_337_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_337_, 0, v___x_336_);
    leanh::lean_ctor_set(v___x_337_, 1, v___x_335_);
    return v___x_337_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg()
-> *mut leanh::LeanObject {
    let mut v___x_339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_340_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_339_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg___closed__0);
    v___x_340_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_340_, 0, v___x_339_);
    return v___x_340_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg___boxed(
    mut v___y_341_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_342_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_342_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
    return v_res_342_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0(
    mut v_00_u03b1_343_: *mut leanh::LeanObject,
    mut v___y_344_: *mut leanh::LeanObject,
    mut v___y_345_: *mut leanh::LeanObject,
    mut v___y_346_: *mut leanh::LeanObject,
    mut v___y_347_: *mut leanh::LeanObject,
    mut v___y_348_: *mut leanh::LeanObject,
    mut v___y_349_: *mut leanh::LeanObject,
    mut v___y_350_: *mut leanh::LeanObject,
    mut v___y_351_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_353_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_353_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
    return v___x_353_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___boxed(
    mut v_00_u03b1_354_: *mut leanh::LeanObject,
    mut v___y_355_: *mut leanh::LeanObject,
    mut v___y_356_: *mut leanh::LeanObject,
    mut v___y_357_: *mut leanh::LeanObject,
    mut v___y_358_: *mut leanh::LeanObject,
    mut v___y_359_: *mut leanh::LeanObject,
    mut v___y_360_: *mut leanh::LeanObject,
    mut v___y_361_: *mut leanh::LeanObject,
    mut v___y_362_: *mut leanh::LeanObject,
    mut v___y_363_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_364_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_362_);
    leanh::lean_dec_ref(v___y_361_);
    leanh::lean_dec(v___y_360_);
    leanh::lean_dec_ref(v___y_359_);
    leanh::lean_dec(v___y_358_);
    leanh::lean_dec_ref(v___y_357_);
    leanh::lean_dec(v___y_356_);
    leanh::lean_dec_ref(v___y_355_);
    return v_res_364_;
}
pub unsafe fn l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg___lam__0(
    mut v_snd_365_: *mut leanh::LeanObject,
    mut v___y_366_: *mut leanh::LeanObject,
    mut v_a_x3f_367_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_373_: u8 = 0;
    let mut v___x_375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_377_: u8 = 0;
    let mut v_a_378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_381_: u8 = 0;
    let mut v_ref_382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_390_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_369_ = lean_io_remove_file(v_snd_365_);
                if leanh::lean_obj_tag(v___x_369_) == 0 {
                    v_a_370_ = leanh::lean_ctor_get(v___x_369_, 0);
                    v_isSharedCheck_377_ = (!leanh::lean_is_exclusive(v___x_369_)) as u8;
                    if v_isSharedCheck_377_ == 0 {
                        v___x_372_ = v___x_369_;
                        v_isShared_373_ = v_isSharedCheck_377_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_370_);
                        leanh::lean_dec(v___x_369_);
                        v___x_372_ = leanh::lean_box(0);
                        v_isShared_373_ = v_isSharedCheck_377_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_378_ = leanh::lean_ctor_get(v___x_369_, 0);
                    v_isSharedCheck_390_ = (!leanh::lean_is_exclusive(v___x_369_)) as u8;
                    if v_isSharedCheck_390_ == 0 {
                        v___x_380_ = v___x_369_;
                        v_isShared_381_ = v_isSharedCheck_390_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_378_);
                        leanh::lean_dec(v___x_369_);
                        v___x_380_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_376_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_376_, 0, v_a_370_);
                    v___x_375_ = v_reuseFailAlloc_376_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_375_;
            }
            3 => {
                v_ref_382_ = leanh::lean_ctor_get(v___y_366_, 5);
                v___x_383_ = lean_io_error_to_string(v_a_378_);
                v___x_384_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_384_, 0, v___x_383_);
                v___x_385_ = l_Lean_MessageData_ofFormat(v___x_384_);
                leanh::lean_inc(v_ref_382_);
                v___x_386_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_386_, 0, v_ref_382_);
                leanh::lean_ctor_set(v___x_386_, 1, v___x_385_);
                if v_isShared_381_ == 0 {
                    leanh::lean_ctor_set(v___x_380_, 0, v___x_386_);
                    v___x_388_ = v___x_380_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_389_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_389_, 0, v___x_386_);
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
    mut v_snd_391_: *mut leanh::LeanObject,
    mut v___y_392_: *mut leanh::LeanObject,
    mut v_a_x3f_393_: *mut leanh::LeanObject,
    mut v___y_394_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_395_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_395_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg___lam__0(v_snd_391_, v___y_392_, v_a_x3f_393_);
    leanh::lean_dec(v_a_x3f_393_);
    leanh::lean_dec_ref(v___y_392_);
    leanh::lean_dec_ref(v_snd_391_);
    return v_res_395_;
}
pub unsafe fn l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg(
    mut v_f_396_: *mut leanh::LeanObject,
    mut v___y_397_: *mut leanh::LeanObject,
    mut v___y_398_: *mut leanh::LeanObject,
    mut v___y_399_: *mut leanh::LeanObject,
    mut v___y_400_: *mut leanh::LeanObject,
    mut v___y_401_: *mut leanh::LeanObject,
    mut v___y_402_: *mut leanh::LeanObject,
    mut v___y_403_: *mut leanh::LeanObject,
    mut v___y_404_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_414_: u8 = 0;
    let mut v___x_416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_420_: u8 = 0;
    let mut v___x_422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_424_: u8 = 0;
    let mut v_unused_425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_429_: u8 = 0;
    let mut v___x_431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_433_: u8 = 0;
    let mut v_reuseFailAlloc_434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_435_: u8 = 0;
    let mut v_a_436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_441_: u8 = 0;
    let mut v___x_443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_445_: u8 = 0;
    let mut v_unused_446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_450_: u8 = 0;
    let mut v___x_452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_454_: u8 = 0;
    let mut v_a_455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_458_: u8 = 0;
    let mut v_ref_459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_467_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_406_ = lean_io_create_tempfile();
                if leanh::lean_obj_tag(v___x_406_) == 0 {
                    v_a_407_ = leanh::lean_ctor_get(v___x_406_, 0);
                    leanh::lean_inc(v_a_407_);
                    leanh::lean_dec_ref_known(v___x_406_, 1);
                    v_fst_408_ = leanh::lean_ctor_get(v_a_407_, 0);
                    leanh::lean_inc(v_fst_408_);
                    v_snd_409_ = leanh::lean_ctor_get(v_a_407_, 1);
                    leanh::lean_inc_n(v_snd_409_, 2);
                    leanh::lean_dec(v_a_407_);
                    leanh::lean_inc(v___y_404_);
                    leanh::lean_inc_ref(v___y_403_);
                    leanh::lean_inc(v___y_402_);
                    leanh::lean_inc_ref(v___y_401_);
                    leanh::lean_inc(v___y_400_);
                    leanh::lean_inc_ref(v___y_399_);
                    leanh::lean_inc(v___y_398_);
                    leanh::lean_inc_ref(v___y_397_);
                    v_r_410_ = leanh::lean_apply_11(
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
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v_r_410_) == 0 {
                        v_a_411_ = leanh::lean_ctor_get(v_r_410_, 0);
                        v_isSharedCheck_435_ = (!leanh::lean_is_exclusive(v_r_410_)) as u8;
                        if v_isSharedCheck_435_ == 0 {
                            v___x_413_ = v_r_410_;
                            v_isShared_414_ = v_isSharedCheck_435_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_411_);
                            leanh::lean_dec(v_r_410_);
                            v___x_413_ = leanh::lean_box(0);
                            v_isShared_414_ = v_isSharedCheck_435_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_436_ = leanh::lean_ctor_get(v_r_410_, 0);
                        leanh::lean_inc(v_a_436_);
                        leanh::lean_dec_ref_known(v_r_410_, 1);
                        v___x_437_ = leanh::lean_box(0);
                        v___x_438_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg___lam__0(v_snd_409_, v___y_403_, v___x_437_);
                        leanh::lean_dec(v_snd_409_);
                        if leanh::lean_obj_tag(v___x_438_) == 0 {
                            v_isSharedCheck_445_ =
                                (!leanh::lean_is_exclusive(v___x_438_)) as u8;
                            if v_isSharedCheck_445_ == 0 {
                                v_unused_446_ = leanh::lean_ctor_get(v___x_438_, 0);
                                leanh::lean_dec(v_unused_446_);
                                v___x_440_ = v___x_438_;
                                v_isShared_441_ = v_isSharedCheck_445_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_438_);
                                v___x_440_ = leanh::lean_box(0);
                                v_isShared_441_ = v_isSharedCheck_445_;
                                state = 7;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_436_);
                            v_a_447_ = leanh::lean_ctor_get(v___x_438_, 0);
                            v_isSharedCheck_454_ =
                                (!leanh::lean_is_exclusive(v___x_438_)) as u8;
                            if v_isSharedCheck_454_ == 0 {
                                v___x_449_ = v___x_438_;
                                v_isShared_450_ = v_isSharedCheck_454_;
                                state = 9;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_447_);
                                leanh::lean_dec(v___x_438_);
                                v___x_449_ = leanh::lean_box(0);
                                v_isShared_450_ = v_isSharedCheck_454_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_f_396_);
                    v_a_455_ = leanh::lean_ctor_get(v___x_406_, 0);
                    v_isSharedCheck_467_ = (!leanh::lean_is_exclusive(v___x_406_)) as u8;
                    if v_isSharedCheck_467_ == 0 {
                        v___x_457_ = v___x_406_;
                        v_isShared_458_ = v_isSharedCheck_467_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_455_);
                        leanh::lean_dec(v___x_406_);
                        v___x_457_ = leanh::lean_box(0);
                        v_isShared_458_ = v_isSharedCheck_467_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_a_411_);
                if v_isShared_414_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_413_, 1);
                    v___x_416_ = v___x_413_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_434_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_434_, 0, v_a_411_);
                    v___x_416_ = v_reuseFailAlloc_434_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_417_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg___lam__0(v_snd_409_, v___y_403_, v___x_416_);
                leanh::lean_dec_ref(v___x_416_);
                leanh::lean_dec(v_snd_409_);
                if leanh::lean_obj_tag(v___x_417_) == 0 {
                    v_isSharedCheck_424_ = (!leanh::lean_is_exclusive(v___x_417_)) as u8;
                    if v_isSharedCheck_424_ == 0 {
                        v_unused_425_ = leanh::lean_ctor_get(v___x_417_, 0);
                        leanh::lean_dec(v_unused_425_);
                        v___x_419_ = v___x_417_;
                        v_isShared_420_ = v_isSharedCheck_424_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_417_);
                        v___x_419_ = leanh::lean_box(0);
                        v_isShared_420_ = v_isSharedCheck_424_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_411_);
                    v_a_426_ = leanh::lean_ctor_get(v___x_417_, 0);
                    v_isSharedCheck_433_ = (!leanh::lean_is_exclusive(v___x_417_)) as u8;
                    if v_isSharedCheck_433_ == 0 {
                        v___x_428_ = v___x_417_;
                        v_isShared_429_ = v_isSharedCheck_433_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_426_);
                        leanh::lean_dec(v___x_417_);
                        v___x_428_ = leanh::lean_box(0);
                        v_isShared_429_ = v_isSharedCheck_433_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_420_ == 0 {
                    leanh::lean_ctor_set(v___x_419_, 0, v_a_411_);
                    v___x_422_ = v___x_419_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_423_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_423_, 0, v_a_411_);
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
                    v_reuseFailAlloc_432_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_432_, 0, v_a_426_);
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
                    leanh::lean_ctor_set_tag(v___x_440_, 1);
                    leanh::lean_ctor_set(v___x_440_, 0, v_a_436_);
                    v___x_443_ = v___x_440_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_444_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_444_, 0, v_a_436_);
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
                    v_reuseFailAlloc_453_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_453_, 0, v_a_447_);
                    v___x_452_ = v_reuseFailAlloc_453_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_452_;
            }
            11 => {
                v_ref_459_ = leanh::lean_ctor_get(v___y_403_, 5);
                v___x_460_ = lean_io_error_to_string(v_a_455_);
                v___x_461_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_461_, 0, v___x_460_);
                v___x_462_ = l_Lean_MessageData_ofFormat(v___x_461_);
                leanh::lean_inc(v_ref_459_);
                v___x_463_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_463_, 0, v_ref_459_);
                leanh::lean_ctor_set(v___x_463_, 1, v___x_462_);
                if v_isShared_458_ == 0 {
                    leanh::lean_ctor_set(v___x_457_, 0, v___x_463_);
                    v___x_465_ = v___x_457_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_466_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_466_, 0, v___x_463_);
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
    mut v_f_468_: *mut leanh::LeanObject,
    mut v___y_469_: *mut leanh::LeanObject,
    mut v___y_470_: *mut leanh::LeanObject,
    mut v___y_471_: *mut leanh::LeanObject,
    mut v___y_472_: *mut leanh::LeanObject,
    mut v___y_473_: *mut leanh::LeanObject,
    mut v___y_474_: *mut leanh::LeanObject,
    mut v___y_475_: *mut leanh::LeanObject,
    mut v___y_476_: *mut leanh::LeanObject,
    mut v___y_477_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_478_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_478_ =
        l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg(
            v_f_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_,
            v___y_475_, v___y_476_,
        );
    leanh::lean_dec(v___y_476_);
    leanh::lean_dec_ref(v___y_475_);
    leanh::lean_dec(v___y_474_);
    leanh::lean_dec_ref(v___y_473_);
    leanh::lean_dec(v___y_472_);
    leanh::lean_dec_ref(v___y_471_);
    leanh::lean_dec(v___y_470_);
    leanh::lean_dec_ref(v___y_469_);
    return v_res_478_;
}
pub unsafe fn l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1(
    mut v_00_u03b1_479_: *mut leanh::LeanObject,
    mut v_f_480_: *mut leanh::LeanObject,
    mut v___y_481_: *mut leanh::LeanObject,
    mut v___y_482_: *mut leanh::LeanObject,
    mut v___y_483_: *mut leanh::LeanObject,
    mut v___y_484_: *mut leanh::LeanObject,
    mut v___y_485_: *mut leanh::LeanObject,
    mut v___y_486_: *mut leanh::LeanObject,
    mut v___y_487_: *mut leanh::LeanObject,
    mut v___y_488_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_490_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_490_ =
        l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg(
            v_f_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_,
            v___y_487_, v___y_488_,
        );
    return v___x_490_;
}
pub unsafe fn l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___boxed(
    mut v_00_u03b1_491_: *mut leanh::LeanObject,
    mut v_f_492_: *mut leanh::LeanObject,
    mut v___y_493_: *mut leanh::LeanObject,
    mut v___y_494_: *mut leanh::LeanObject,
    mut v___y_495_: *mut leanh::LeanObject,
    mut v___y_496_: *mut leanh::LeanObject,
    mut v___y_497_: *mut leanh::LeanObject,
    mut v___y_498_: *mut leanh::LeanObject,
    mut v___y_499_: *mut leanh::LeanObject,
    mut v___y_500_: *mut leanh::LeanObject,
    mut v___y_501_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_502_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_500_);
    leanh::lean_dec_ref(v___y_499_);
    leanh::lean_dec(v___y_498_);
    leanh::lean_dec_ref(v___y_497_);
    leanh::lean_dec(v___y_496_);
    leanh::lean_dec_ref(v___y_495_);
    leanh::lean_dec(v___y_494_);
    leanh::lean_dec_ref(v___y_493_);
    return v_res_502_;
}
pub unsafe fn l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__0(
    mut v_a_503_: *mut leanh::LeanObject,
    mut v___y_504_: *mut leanh::LeanObject,
    mut v___y_505_: *mut leanh::LeanObject,
    mut v___y_506_: *mut leanh::LeanObject,
    mut v___y_507_: *mut leanh::LeanObject,
    mut v___y_508_: *mut leanh::LeanObject,
    mut v___y_509_: *mut leanh::LeanObject,
    mut v___y_510_: *mut leanh::LeanObject,
    mut v___y_511_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_520_: u8 = 0;
    let mut v___x_521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_525_: u8 = 0;
    let mut v_unused_526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_530_: u8 = 0;
    let mut v___x_532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_534_: u8 = 0;
    let mut v_a_535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_538_: u8 = 0;
    let mut v___x_540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_542_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_513_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v___y_505_, v___y_508_, v___y_509_, v___y_510_, v___y_511_,
                );
                if leanh::lean_obj_tag(v___x_513_) == 0 {
                    v_a_514_ = leanh::lean_ctor_get(v___x_513_, 0);
                    leanh::lean_inc(v_a_514_);
                    leanh::lean_dec_ref_known(v___x_513_, 1);
                    v___x_515_ = l_Lean_Meta_Tactic_BVDecide_bvDecide(
                        v_a_514_, v_a_503_, v___y_508_, v___y_509_, v___y_510_, v___y_511_,
                    );
                    if leanh::lean_obj_tag(v___x_515_) == 0 {
                        leanh::lean_dec_ref_known(v___x_515_, 1);
                        v___x_516_ = leanh::lean_box(0);
                        v___x_517_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                            v___x_516_, v___y_505_, v___y_508_, v___y_509_, v___y_510_, v___y_511_,
                        );
                        if leanh::lean_obj_tag(v___x_517_) == 0 {
                            v_isSharedCheck_525_ =
                                (!leanh::lean_is_exclusive(v___x_517_)) as u8;
                            if v_isSharedCheck_525_ == 0 {
                                v_unused_526_ = leanh::lean_ctor_get(v___x_517_, 0);
                                leanh::lean_dec(v_unused_526_);
                                v___x_519_ = v___x_517_;
                                v_isShared_520_ = v_isSharedCheck_525_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_517_);
                                v___x_519_ = leanh::lean_box(0);
                                v_isShared_520_ = v_isSharedCheck_525_;
                                state = 1;
                                continue;
                            }
                        } else {
                            return v___x_517_;
                        }
                    } else {
                        v_a_527_ = leanh::lean_ctor_get(v___x_515_, 0);
                        v_isSharedCheck_534_ = (!leanh::lean_is_exclusive(v___x_515_)) as u8;
                        if v_isSharedCheck_534_ == 0 {
                            v___x_529_ = v___x_515_;
                            v_isShared_530_ = v_isSharedCheck_534_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_527_);
                            leanh::lean_dec(v___x_515_);
                            v___x_529_ = leanh::lean_box(0);
                            v_isShared_530_ = v_isSharedCheck_534_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_a_503_);
                    v_a_535_ = leanh::lean_ctor_get(v___x_513_, 0);
                    v_isSharedCheck_542_ = (!leanh::lean_is_exclusive(v___x_513_)) as u8;
                    if v_isSharedCheck_542_ == 0 {
                        v___x_537_ = v___x_513_;
                        v_isShared_538_ = v_isSharedCheck_542_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_535_);
                        leanh::lean_dec(v___x_513_);
                        v___x_537_ = leanh::lean_box(0);
                        v_isShared_538_ = v_isSharedCheck_542_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_521_ = leanh::lean_box(0);
                if v_isShared_520_ == 0 {
                    leanh::lean_ctor_set(v___x_519_, 0, v___x_521_);
                    v___x_523_ = v___x_519_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_524_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_524_, 0, v___x_521_);
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
                    v_reuseFailAlloc_533_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_533_, 0, v_a_527_);
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
                    v_reuseFailAlloc_541_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_541_, 0, v_a_535_);
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
    mut v_a_543_: *mut leanh::LeanObject,
    mut v___y_544_: *mut leanh::LeanObject,
    mut v___y_545_: *mut leanh::LeanObject,
    mut v___y_546_: *mut leanh::LeanObject,
    mut v___y_547_: *mut leanh::LeanObject,
    mut v___y_548_: *mut leanh::LeanObject,
    mut v___y_549_: *mut leanh::LeanObject,
    mut v___y_550_: *mut leanh::LeanObject,
    mut v___y_551_: *mut leanh::LeanObject,
    mut v___y_552_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_553_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_553_ = l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__0(
        v_a_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_,
        v___y_550_, v___y_551_,
    );
    leanh::lean_dec(v___y_551_);
    leanh::lean_dec_ref(v___y_550_);
    leanh::lean_dec(v___y_549_);
    leanh::lean_dec_ref(v___y_548_);
    leanh::lean_dec(v___y_547_);
    leanh::lean_dec_ref(v___y_546_);
    leanh::lean_dec(v___y_545_);
    leanh::lean_dec_ref(v___y_544_);
    return v_res_553_;
}
pub unsafe fn l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__1(
    mut v_a_554_: *mut leanh::LeanObject,
    mut v_x_555_: *mut leanh::LeanObject,
    mut v_lratFile_556_: *mut leanh::LeanObject,
    mut v___y_557_: *mut leanh::LeanObject,
    mut v___y_558_: *mut leanh::LeanObject,
    mut v___y_559_: *mut leanh::LeanObject,
    mut v___y_560_: *mut leanh::LeanObject,
    mut v___y_561_: *mut leanh::LeanObject,
    mut v___y_562_: *mut leanh::LeanObject,
    mut v___y_563_: *mut leanh::LeanObject,
    mut v___y_564_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_573_: u8 = 0;
    let mut v___x_575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_576_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                if leanh::lean_obj_tag(v___x_566_) == 0 {
                    v_a_567_ = leanh::lean_ctor_get(v___x_566_, 0);
                    leanh::lean_inc(v_a_567_);
                    leanh::lean_dec_ref_known(v___x_566_, 1);
                    v___f_568_ = leanh::lean_alloc_closure(
                        l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__0___boxed
                            as *mut core::ffi::c_void,
                        10,
                        1,
                    );
                    leanh::lean_closure_set(v___f_568_, 0, v_a_567_);
                    v___x_569_ = l_Lean_Elab_Tactic_withMainContext___redArg(
                        v___f_568_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_,
                        v___y_562_, v___y_563_, v___y_564_,
                    );
                    return v___x_569_;
                } else {
                    v_a_570_ = leanh::lean_ctor_get(v___x_566_, 0);
                    v_isSharedCheck_577_ = (!leanh::lean_is_exclusive(v___x_566_)) as u8;
                    if v_isSharedCheck_577_ == 0 {
                        v___x_572_ = v___x_566_;
                        v_isShared_573_ = v_isSharedCheck_577_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_570_);
                        leanh::lean_dec(v___x_566_);
                        v___x_572_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_576_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_576_, 0, v_a_570_);
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
    mut v_a_578_: *mut leanh::LeanObject,
    mut v_x_579_: *mut leanh::LeanObject,
    mut v_lratFile_580_: *mut leanh::LeanObject,
    mut v___y_581_: *mut leanh::LeanObject,
    mut v___y_582_: *mut leanh::LeanObject,
    mut v___y_583_: *mut leanh::LeanObject,
    mut v___y_584_: *mut leanh::LeanObject,
    mut v___y_585_: *mut leanh::LeanObject,
    mut v___y_586_: *mut leanh::LeanObject,
    mut v___y_587_: *mut leanh::LeanObject,
    mut v___y_588_: *mut leanh::LeanObject,
    mut v___y_589_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_590_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_588_);
    leanh::lean_dec_ref(v___y_587_);
    leanh::lean_dec(v___y_586_);
    leanh::lean_dec_ref(v___y_585_);
    leanh::lean_dec(v___y_584_);
    leanh::lean_dec_ref(v___y_583_);
    leanh::lean_dec(v___y_582_);
    leanh::lean_dec_ref(v___y_581_);
    leanh::lean_dec(v_x_579_);
    return v_res_590_;
}
pub unsafe fn l_Lean_Elab_Tactic_BVDecide_evalBvDecide(
    mut v_x_606_: *mut leanh::LeanObject,
    mut v_a_607_: *mut leanh::LeanObject,
    mut v_a_608_: *mut leanh::LeanObject,
    mut v_a_609_: *mut leanh::LeanObject,
    mut v_a_610_: *mut leanh::LeanObject,
    mut v_a_611_: *mut leanh::LeanObject,
    mut v_a_612_: *mut leanh::LeanObject,
    mut v_a_613_: *mut leanh::LeanObject,
    mut v_a_614_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_617_: u8 = 0;
    let mut v___x_618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_622_: u8 = 0;
    let mut v___x_623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_625_: u8 = 0;
    let mut v___x_626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_627_: u8 = 0;
    let mut v___x_628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_636_: u8 = 0;
    let mut v___x_638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_640_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_616_ = l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__4;
                leanh::lean_inc(v_x_606_);
                v___x_617_ = l_Lean_Syntax_isOfKind(v_x_606_, v___x_616_);
                if v___x_617_ == 0 {
                    leanh::lean_dec(v_x_606_);
                    v___x_618_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
                    return v___x_618_;
                } else {
                    v___x_619_ = leanh::lean_unsigned_to_nat(1);
                    v___x_620_ = l_Lean_Syntax_getArg(v_x_606_, v___x_619_);
                    leanh::lean_dec(v_x_606_);
                    v___x_621_ = l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__6;
                    leanh::lean_inc(v___x_620_);
                    v___x_622_ = l_Lean_Syntax_isOfKind(v___x_620_, v___x_621_);
                    if v___x_622_ == 0 {
                        leanh::lean_dec(v___x_620_);
                        v___x_623_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__0___redArg();
                        return v___x_623_;
                    } else {
                        v___x_624_ = leanh::lean_unsigned_to_nat(10);
                        v___x_625_ = 0;
                        v___x_626_ = leanh::lean_unsigned_to_nat(100000);
                        v___x_627_ = 0;
                        v___x_628_ = leanh::lean_alloc_ctor(0, 2, (11) as u32);
                        leanh::lean_ctor_set(v___x_628_, 0, v___x_624_);
                        leanh::lean_ctor_set(v___x_628_, 1, v___x_626_);
                        leanh::lean_ctor_set_uint8(
                            v___x_628_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                            v___x_622_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v___x_628_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                            v___x_622_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v___x_628_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 2) as u32,
                            v___x_625_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v___x_628_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 3) as u32,
                            v___x_622_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v___x_628_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 4) as u32,
                            v___x_622_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v___x_628_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 5) as u32,
                            v___x_622_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v___x_628_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 6) as u32,
                            v___x_622_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v___x_628_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 7) as u32,
                            v___x_622_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v___x_628_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 8) as u32,
                            v___x_625_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v___x_628_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 9) as u32,
                            v___x_625_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v___x_628_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 10) as u32,
                            v___x_627_,
                        );
                        v___x_629_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(
                            v___x_620_, v___x_628_, v___x_622_, v_a_607_, v_a_613_, v_a_614_,
                        );
                        if leanh::lean_obj_tag(v___x_629_) == 0 {
                            v_a_630_ = leanh::lean_ctor_get(v___x_629_, 0);
                            leanh::lean_inc(v_a_630_);
                            leanh::lean_dec_ref_known(v___x_629_, 1);
                            v___f_631_ = leanh::lean_alloc_closure(
                                l_Lean_Elab_Tactic_BVDecide_evalBvDecide___lam__1___boxed
                                    as *mut core::ffi::c_void,
                                12,
                                1,
                            );
                            leanh::lean_closure_set(v___f_631_, 0, v_a_630_);
                            v___x_632_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_evalBvDecide_spec__1___redArg(v___f_631_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_);
                            return v___x_632_;
                        } else {
                            v_a_633_ = leanh::lean_ctor_get(v___x_629_, 0);
                            v_isSharedCheck_640_ =
                                (!leanh::lean_is_exclusive(v___x_629_)) as u8;
                            if v_isSharedCheck_640_ == 0 {
                                v___x_635_ = v___x_629_;
                                v_isShared_636_ = v_isSharedCheck_640_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_633_);
                                leanh::lean_dec(v___x_629_);
                                v___x_635_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_639_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_639_, 0, v_a_633_);
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
    mut v_x_641_: *mut leanh::LeanObject,
    mut v_a_642_: *mut leanh::LeanObject,
    mut v_a_643_: *mut leanh::LeanObject,
    mut v_a_644_: *mut leanh::LeanObject,
    mut v_a_645_: *mut leanh::LeanObject,
    mut v_a_646_: *mut leanh::LeanObject,
    mut v_a_647_: *mut leanh::LeanObject,
    mut v_a_648_: *mut leanh::LeanObject,
    mut v_a_649_: *mut leanh::LeanObject,
    mut v_a_650_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_651_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_651_ = l_Lean_Elab_Tactic_BVDecide_evalBvDecide(
        v_x_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_,
    );
    leanh::lean_dec(v_a_649_);
    leanh::lean_dec_ref(v_a_648_);
    leanh::lean_dec(v_a_647_);
    leanh::lean_dec_ref(v_a_646_);
    leanh::lean_dec(v_a_645_);
    leanh::lean_dec_ref(v_a_644_);
    leanh::lean_dec(v_a_643_);
    leanh::lean_dec_ref(v_a_642_);
    return v_res_651_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_BVDecide_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1()
-> *mut leanh::LeanObject {
    let mut v___x_662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_662_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_663_ = l_Lean_Elab_Tactic_BVDecide_evalBvDecide___closed__4;
    v___x_664_ = l___private_Lean_Elab_Tactic_BVDecide_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1___closed__3;
    v___x_665_ = leanh::lean_alloc_closure(
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
    mut v_a_667_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_668_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_668_ = l___private_Lean_Elab_Tactic_BVDecide_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1();
    return v_res_668_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_BVDecide_BVDecide(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Main(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_BVDecide_BVDecide_0__Lean_Elab_Tactic_BVDecide_evalBvDecide___regBuiltin_Lean_Elab_Tactic_BVDecide_evalBvDecide__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_BVDecide_BVDecide(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_BVDecide_BVDecide(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_BVDecide_Main(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_BVDecide_BVDecide(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_BVDecide_BVDecide(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_BVDecide_BVDecide(builtin);
}