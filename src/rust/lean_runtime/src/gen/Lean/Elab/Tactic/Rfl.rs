// Lean compiler output
// Module: Lean.Elab.Tactic.Rfl
// Imports: Lean.Meta.Tactic.Rfl
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr4, l_Lean_Name_mkStr5, l_Lean_Syntax_isOfKind};
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::DocString::Extension::l_Lean_addBuiltinDocString;
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    l_Lean_Elab_Tactic_getMainGoal___redArg, l_Lean_Elab_Tactic_replaceMainGoal___redArg,
    l_Lean_Elab_Tactic_tacticElabAttribute, l_Lean_Elab_Tactic_withMainContext___redArg,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Meta::Tactic::Rfl::{
    initialize_Lean_Meta_Tactic_Rfl, l_Lean_MVarId_applyRfl,
    runtime_initialize_Lean_Meta_Tactic_Rfl,
};
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Rfl_evalApplyRfl_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Rfl_evalApplyRfl_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__0_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
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
static mut l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__1_value: crate::leanh::LeanStringObject<
    7,
> = crate::leanh::LeanStringObject {
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
static mut l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__2_value: crate::leanh::LeanStringObject<
    7,
> = crate::leanh::LeanStringObject {
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
static mut l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__3_value: crate::leanh::LeanStringObject<
    9,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [97, 112, 112, 108, 121, 82, 102, 108, 0],
};
static mut l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__4_value_aux_0: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__4_value_aux_1: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__4_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__4_value_aux_2: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__4_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__4_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__3_value)
                as *mut crate::leanh::LeanObject,
            18128203598290488495 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__5_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Tactic_Rfl_evalApplyRfl___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__6_value: crate::leanh::LeanClosureObject<
    1,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Tactic_Rfl_evalApplyRfl___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 10,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl__1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl__1___closed__1_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [82, 102, 108, 0]};
static mut l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl__1___closed__2_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 118, 97, 108, 65, 112, 112, 108, 121, 82, 102, 108, 0]};
static mut l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl__1___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl__1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl__1___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl__1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl__1___closed__0_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl__1___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl__1___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__2_value) as *mut crate::leanh::LeanObject,12733524109236233889 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl__1___closed__3_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl__1___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl__1___closed__1_value) as *mut crate::leanh::LeanObject,9736486422574606045 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl__1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl__1___closed__3_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl__1___closed__2_value) as *mut crate::leanh::LeanObject,16816156489251953870 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_docString__3___closed__0_value: crate::leanh::LeanStringObject<183> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 183, m_capacity: 183, m_length: 182, m_data: [84, 104, 105, 115, 32, 116, 97, 99, 116, 105, 99, 32, 97, 112, 112, 108, 105, 101, 115, 32, 116, 111, 32, 97, 32, 103, 111, 97, 108, 32, 119, 104, 111, 115, 101, 32, 116, 97, 114, 103, 101, 116, 32, 104, 97, 115, 32, 116, 104, 101, 32, 102, 111, 114, 109, 32, 96, 120, 32, 126, 32, 120, 96, 44, 32, 119, 104, 101, 114, 101, 32, 96, 126, 96, 32, 105, 115, 32, 97, 32, 114, 101, 102, 108, 101, 120, 105, 118, 101, 10, 114, 101, 108, 97, 116, 105, 111, 110, 44, 32, 116, 104, 97, 116, 32, 105, 115, 44, 32, 97, 32, 114, 101, 108, 97, 116, 105, 111, 110, 32, 119, 104, 105, 99, 104, 32, 104, 97, 115, 32, 97, 32, 114, 101, 102, 108, 101, 120, 105, 118, 101, 32, 108, 101, 109, 109, 97, 32, 116, 97, 103, 103, 101, 100, 32, 119, 105, 116, 104, 32, 116, 104, 101, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 91, 114, 101, 102, 108, 93, 46, 10, 0]};
static mut l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_docString__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_docString__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 19 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 46 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 22 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 31 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5___closed__0_value) as *mut crate::leanh::LeanObject,((( 46 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5___closed__1_value) as *mut crate::leanh::LeanObject,((( 31 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 19 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 50 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 19 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 62 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5___closed__3_value) as *mut crate::leanh::LeanObject,((( 50 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5___closed__4_value) as *mut crate::leanh::LeanObject,((( 62 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5___closed__6_value) as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Rfl_evalApplyRfl_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_187_ = crate::leanh::lean_box(0);
    v___x_188_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_189_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_189_, 0, v___x_188_);
    crate::leanh::lean_ctor_set(v___x_189_, 1, v___x_187_);
    return v___x_189_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Rfl_evalApplyRfl_spec__0___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_191_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Rfl_evalApplyRfl_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Rfl_evalApplyRfl_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Rfl_evalApplyRfl_spec__0___redArg___closed__0);
    v___x_192_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_192_, 0, v___x_191_);
    return v___x_192_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Rfl_evalApplyRfl_spec__0___redArg___boxed(
    mut v___y_193_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_194_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Rfl_evalApplyRfl_spec__0___redArg();
    return v_res_194_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Rfl_evalApplyRfl_spec__0(
    mut v_00_u03b1_195_: *mut crate::leanh::LeanObject,
    mut v___y_196_: *mut crate::leanh::LeanObject,
    mut v___y_197_: *mut crate::leanh::LeanObject,
    mut v___y_198_: *mut crate::leanh::LeanObject,
    mut v___y_199_: *mut crate::leanh::LeanObject,
    mut v___y_200_: *mut crate::leanh::LeanObject,
    mut v___y_201_: *mut crate::leanh::LeanObject,
    mut v___y_202_: *mut crate::leanh::LeanObject,
    mut v___y_203_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_205_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Rfl_evalApplyRfl_spec__0___redArg();
    return v___x_205_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Rfl_evalApplyRfl_spec__0___boxed(
    mut v_00_u03b1_206_: *mut crate::leanh::LeanObject,
    mut v___y_207_: *mut crate::leanh::LeanObject,
    mut v___y_208_: *mut crate::leanh::LeanObject,
    mut v___y_209_: *mut crate::leanh::LeanObject,
    mut v___y_210_: *mut crate::leanh::LeanObject,
    mut v___y_211_: *mut crate::leanh::LeanObject,
    mut v___y_212_: *mut crate::leanh::LeanObject,
    mut v___y_213_: *mut crate::leanh::LeanObject,
    mut v___y_214_: *mut crate::leanh::LeanObject,
    mut v___y_215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_216_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Rfl_evalApplyRfl_spec__0(
            v_00_u03b1_206_,
            v___y_207_,
            v___y_208_,
            v___y_209_,
            v___y_210_,
            v___y_211_,
            v___y_212_,
            v___y_213_,
            v___y_214_,
        );
    crate::leanh::lean_dec(v___y_214_);
    crate::leanh::lean_dec_ref(v___y_213_);
    crate::leanh::lean_dec(v___y_212_);
    crate::leanh::lean_dec_ref(v___y_211_);
    crate::leanh::lean_dec(v___y_210_);
    crate::leanh::lean_dec_ref(v___y_209_);
    crate::leanh::lean_dec(v___y_208_);
    crate::leanh::lean_dec_ref(v___y_207_);
    return v_res_216_;
}
pub unsafe fn l_Lean_Elab_Tactic_Rfl_evalApplyRfl___lam__0(
    mut v___y_217_: *mut crate::leanh::LeanObject,
    mut v___y_218_: *mut crate::leanh::LeanObject,
    mut v___y_219_: *mut crate::leanh::LeanObject,
    mut v___y_220_: *mut crate::leanh::LeanObject,
    mut v___y_221_: *mut crate::leanh::LeanObject,
    mut v___y_222_: *mut crate::leanh::LeanObject,
    mut v___y_223_: *mut crate::leanh::LeanObject,
    mut v___y_224_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_233_: u8 = 0;
    let mut v___x_234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_238_: u8 = 0;
    let mut v_unused_239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_243_: u8 = 0;
    let mut v___x_245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_247_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_226_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v___y_218_, v___y_221_, v___y_222_, v___y_223_, v___y_224_,
                );
                if crate::leanh::lean_obj_tag(v___x_226_) == 0 {
                    v_a_227_ = crate::leanh::lean_ctor_get(v___x_226_, 0);
                    crate::leanh::lean_inc(v_a_227_);
                    crate::leanh::lean_dec_ref_known(v___x_226_, 1);
                    v___x_228_ = l_Lean_MVarId_applyRfl(
                        v_a_227_, v___y_221_, v___y_222_, v___y_223_, v___y_224_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_228_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_228_, 1);
                        v___x_229_ = crate::leanh::lean_box(0);
                        v___x_230_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                            v___x_229_, v___y_218_, v___y_221_, v___y_222_, v___y_223_, v___y_224_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_230_) == 0 {
                            v_isSharedCheck_238_ =
                                (!crate::leanh::lean_is_exclusive(v___x_230_)) as u8;
                            if v_isSharedCheck_238_ == 0 {
                                v_unused_239_ = crate::leanh::lean_ctor_get(v___x_230_, 0);
                                crate::leanh::lean_dec(v_unused_239_);
                                v___x_232_ = v___x_230_;
                                v_isShared_233_ = v_isSharedCheck_238_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_230_);
                                v___x_232_ = crate::leanh::lean_box(0);
                                v_isShared_233_ = v_isSharedCheck_238_;
                                state = 1;
                                continue;
                            }
                        } else {
                            return v___x_230_;
                        }
                    } else {
                        return v___x_228_;
                    }
                } else {
                    v_a_240_ = crate::leanh::lean_ctor_get(v___x_226_, 0);
                    v_isSharedCheck_247_ = (!crate::leanh::lean_is_exclusive(v___x_226_)) as u8;
                    if v_isSharedCheck_247_ == 0 {
                        v___x_242_ = v___x_226_;
                        v_isShared_243_ = v_isSharedCheck_247_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_240_);
                        crate::leanh::lean_dec(v___x_226_);
                        v___x_242_ = crate::leanh::lean_box(0);
                        v_isShared_243_ = v_isSharedCheck_247_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_234_ = crate::leanh::lean_box(0);
                if v_isShared_233_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_232_, 0, v___x_234_);
                    v___x_236_ = v___x_232_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_237_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_237_, 0, v___x_234_);
                    v___x_236_ = v_reuseFailAlloc_237_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_236_;
            }
            3 => {
                if v_isShared_243_ == 0 {
                    v___x_245_ = v___x_242_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_246_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_246_, 0, v_a_240_);
                    v___x_245_ = v_reuseFailAlloc_246_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_245_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Rfl_evalApplyRfl___lam__0___boxed(
    mut v___y_248_: *mut crate::leanh::LeanObject,
    mut v___y_249_: *mut crate::leanh::LeanObject,
    mut v___y_250_: *mut crate::leanh::LeanObject,
    mut v___y_251_: *mut crate::leanh::LeanObject,
    mut v___y_252_: *mut crate::leanh::LeanObject,
    mut v___y_253_: *mut crate::leanh::LeanObject,
    mut v___y_254_: *mut crate::leanh::LeanObject,
    mut v___y_255_: *mut crate::leanh::LeanObject,
    mut v___y_256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_257_ = l_Lean_Elab_Tactic_Rfl_evalApplyRfl___lam__0(
        v___y_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_,
        v___y_255_,
    );
    crate::leanh::lean_dec(v___y_255_);
    crate::leanh::lean_dec_ref(v___y_254_);
    crate::leanh::lean_dec(v___y_253_);
    crate::leanh::lean_dec_ref(v___y_252_);
    crate::leanh::lean_dec(v___y_251_);
    crate::leanh::lean_dec_ref(v___y_250_);
    crate::leanh::lean_dec(v___y_249_);
    crate::leanh::lean_dec_ref(v___y_248_);
    return v_res_257_;
}
pub unsafe fn l_Lean_Elab_Tactic_Rfl_evalApplyRfl___lam__1(
    mut v___f_258_: *mut crate::leanh::LeanObject,
    mut v___y_259_: *mut crate::leanh::LeanObject,
    mut v___y_260_: *mut crate::leanh::LeanObject,
    mut v___y_261_: *mut crate::leanh::LeanObject,
    mut v___y_262_: *mut crate::leanh::LeanObject,
    mut v___y_263_: *mut crate::leanh::LeanObject,
    mut v___y_264_: *mut crate::leanh::LeanObject,
    mut v___y_265_: *mut crate::leanh::LeanObject,
    mut v___y_266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_268_ = l_Lean_Elab_Tactic_withMainContext___redArg(
        v___f_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_,
        v___y_265_, v___y_266_,
    );
    return v___x_268_;
}
pub unsafe fn l_Lean_Elab_Tactic_Rfl_evalApplyRfl___lam__1___boxed(
    mut v___f_269_: *mut crate::leanh::LeanObject,
    mut v___y_270_: *mut crate::leanh::LeanObject,
    mut v___y_271_: *mut crate::leanh::LeanObject,
    mut v___y_272_: *mut crate::leanh::LeanObject,
    mut v___y_273_: *mut crate::leanh::LeanObject,
    mut v___y_274_: *mut crate::leanh::LeanObject,
    mut v___y_275_: *mut crate::leanh::LeanObject,
    mut v___y_276_: *mut crate::leanh::LeanObject,
    mut v___y_277_: *mut crate::leanh::LeanObject,
    mut v___y_278_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_279_ = l_Lean_Elab_Tactic_Rfl_evalApplyRfl___lam__1(
        v___f_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_,
        v___y_276_, v___y_277_,
    );
    crate::leanh::lean_dec(v___y_277_);
    crate::leanh::lean_dec_ref(v___y_276_);
    crate::leanh::lean_dec(v___y_275_);
    crate::leanh::lean_dec_ref(v___y_274_);
    crate::leanh::lean_dec(v___y_273_);
    crate::leanh::lean_dec_ref(v___y_272_);
    crate::leanh::lean_dec(v___y_271_);
    crate::leanh::lean_dec_ref(v___y_270_);
    return v_res_279_;
}
pub unsafe fn l_Lean_Elab_Tactic_Rfl_evalApplyRfl(
    mut v_stx_292_: *mut crate::leanh::LeanObject,
    mut v_a_293_: *mut crate::leanh::LeanObject,
    mut v_a_294_: *mut crate::leanh::LeanObject,
    mut v_a_295_: *mut crate::leanh::LeanObject,
    mut v_a_296_: *mut crate::leanh::LeanObject,
    mut v_a_297_: *mut crate::leanh::LeanObject,
    mut v_a_298_: *mut crate::leanh::LeanObject,
    mut v_a_299_: *mut crate::leanh::LeanObject,
    mut v_a_300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_303_: u8 = 0;
    v___x_302_ = l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__4;
    v___x_303_ = l_Lean_Syntax_isOfKind(v_stx_292_, v___x_302_);
    if v___x_303_ == 0 {
        let mut v___x_304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_304_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Rfl_evalApplyRfl_spec__0___redArg();
        return v___x_304_;
    } else {
        let mut v___f_305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_305_ = l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__6;
        v___x_306_ = l_Lean_Elab_Tactic_withMainContext___redArg(
            v___f_305_, v_a_293_, v_a_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_,
            v_a_300_,
        );
        return v___x_306_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Rfl_evalApplyRfl___boxed(
    mut v_stx_307_: *mut crate::leanh::LeanObject,
    mut v_a_308_: *mut crate::leanh::LeanObject,
    mut v_a_309_: *mut crate::leanh::LeanObject,
    mut v_a_310_: *mut crate::leanh::LeanObject,
    mut v_a_311_: *mut crate::leanh::LeanObject,
    mut v_a_312_: *mut crate::leanh::LeanObject,
    mut v_a_313_: *mut crate::leanh::LeanObject,
    mut v_a_314_: *mut crate::leanh::LeanObject,
    mut v_a_315_: *mut crate::leanh::LeanObject,
    mut v_a_316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_317_ = l_Lean_Elab_Tactic_Rfl_evalApplyRfl(
        v_stx_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_, v_a_314_, v_a_315_,
    );
    crate::leanh::lean_dec(v_a_315_);
    crate::leanh::lean_dec_ref(v_a_314_);
    crate::leanh::lean_dec(v_a_313_);
    crate::leanh::lean_dec_ref(v_a_312_);
    crate::leanh::lean_dec(v_a_311_);
    crate::leanh::lean_dec_ref(v_a_310_);
    crate::leanh::lean_dec(v_a_309_);
    crate::leanh::lean_dec_ref(v_a_308_);
    return v_res_317_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_328_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_329_ = l_Lean_Elab_Tactic_Rfl_evalApplyRfl___closed__4;
    v___x_330_ = l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl__1___closed__3;
    v___x_331_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Rfl_evalApplyRfl___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_332_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_328_, v___x_329_, v___x_330_, v___x_331_,
    );
    return v___x_332_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl__1___boxed(
    mut v_a_333_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_334_ = l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl__1();
    return v_res_334_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_docString__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_337_ = l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl__1___closed__3;
    v___x_338_ = l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_docString__3___closed__0;
    v___x_339_ = l_Lean_addBuiltinDocString(v___x_337_, v___x_338_);
    return v___x_339_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_docString__3___boxed(
    mut v_a_340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_341_ = l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_docString__3();
    return v_res_341_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_368_ = l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl__1___closed__3;
    v___x_369_ = l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5___closed__6;
    v___x_370_ = l_Lean_addBuiltinDeclarationRanges(v___x_368_, v___x_369_);
    return v___x_370_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5___boxed(
    mut v_a_371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_372_ = l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5();
    return v_res_372_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Rfl(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Rfl(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_docString__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Rfl_0__Lean_Elab_Tactic_Rfl_evalApplyRfl___regBuiltin_Lean_Elab_Tactic_Rfl_evalApplyRfl_declRange__5();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Rfl(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Rfl(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Rfl(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Rfl(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Rfl(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Rfl(builtin);
}
