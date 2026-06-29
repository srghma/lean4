// Lean compiler output
// Module: Lean.Elab.Tactic.Conv.Change
// Imports: Lean.Elab.Tactic.Change Lean.Elab.Tactic.Conv.Basic
use crate::ffi::lean_st_ref_get;
use crate::r#gen::Init::Prelude::{l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind};
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    l_Lean_Elab_Tactic_tacticElabAttribute, l_Lean_Elab_Tactic_withMainContext___redArg,
};
use crate::r#gen::Lean::Elab::Tactic::Change::{
    initialize_Lean_Elab_Tactic_Change, l_Lean_Elab_Tactic_elabChange,
    l_Lean_Elab_Tactic_elabChangeDefaultError___boxed, runtime_initialize_Lean_Elab_Tactic_Change,
};
use crate::r#gen::Lean::Elab::Tactic::Conv::Basic::{
    initialize_Lean_Elab_Tactic_Conv_Basic, l_Lean_Elab_Tactic_Conv_changeLhs,
    l_Lean_Elab_Tactic_Conv_getLhs___redArg, runtime_initialize_Lean_Elab_Tactic_Conv_Basic,
};
use crate::r#gen::Lean::Elab::Tactic::ElabTerm::{
    l_Lean_Elab_Tactic_filterOldMVars___redArg, l_Lean_Elab_Tactic_logUnassignedAndAbort,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Meta::CollectMVars::l_Lean_Meta_getMVars;
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalChange_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalChange_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Conv_evalChange___lam__0___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Tactic_elabChangeDefaultError___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Conv_evalChange___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalChange___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalChange___closed__0_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
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
static mut l_Lean_Elab_Tactic_Conv_evalChange___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalChange___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalChange___closed__1_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
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
static mut l_Lean_Elab_Tactic_Conv_evalChange___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalChange___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalChange___closed__2_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
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
static mut l_Lean_Elab_Tactic_Conv_evalChange___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalChange___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalChange___closed__3_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [67, 111, 110, 118, 0],
    };
static mut l_Lean_Elab_Tactic_Conv_evalChange___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalChange___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalChange___closed__4_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [99, 104, 97, 110, 103, 101, 0],
    };
static mut l_Lean_Elab_Tactic_Conv_evalChange___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalChange___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Conv_evalChange___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalChange___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Conv_evalChange___closed__5_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalChange___closed__5_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalChange___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Conv_evalChange___closed__5_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalChange___closed__5_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalChange___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Conv_evalChange___closed__5_value_aux_3: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalChange___closed__5_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalChange___closed__3_value)
                as *mut crate::leanh::LeanObject,
            2622230176999461939 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Conv_evalChange___closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalChange___closed__5_value_aux_3)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalChange___closed__4_value)
                as *mut crate::leanh::LeanObject,
            1203263152968118357 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Conv_evalChange___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalChange___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__1_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [101, 118, 97, 108, 67, 104, 97, 110, 103, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__1_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalChange___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__2_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__0_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__2_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__2_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalChange___closed__2_value) as *mut crate::leanh::LeanObject,12733524109236233889 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__2_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__2_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalChange___closed__3_value) as *mut crate::leanh::LeanObject,9299793053028177184 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__2_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__1_value) as *mut crate::leanh::LeanObject,12854273918554071889 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 13 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 49 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 23 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 31 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject,((( 49 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject,((( 31 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 13 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 53 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 13 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 63 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject,((( 53 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject,((( 63 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__6_value) as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalChange_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_185_ = crate::leanh::lean_box(0);
    v___x_186_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_187_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_187_, 0, v___x_186_);
    crate::leanh::lean_ctor_set(v___x_187_, 1, v___x_185_);
    return v___x_187_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalChange_spec__0___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_189_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalChange_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalChange_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalChange_spec__0___redArg___closed__0);
    v___x_190_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_190_, 0, v___x_189_);
    return v___x_190_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalChange_spec__0___redArg___boxed(
    mut v___y_191_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_192_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalChange_spec__0___redArg();
    return v_res_192_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalChange_spec__0(
    mut v_00_u03b1_193_: *mut crate::leanh::LeanObject,
    mut v___y_194_: *mut crate::leanh::LeanObject,
    mut v___y_195_: *mut crate::leanh::LeanObject,
    mut v___y_196_: *mut crate::leanh::LeanObject,
    mut v___y_197_: *mut crate::leanh::LeanObject,
    mut v___y_198_: *mut crate::leanh::LeanObject,
    mut v___y_199_: *mut crate::leanh::LeanObject,
    mut v___y_200_: *mut crate::leanh::LeanObject,
    mut v___y_201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_203_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalChange_spec__0___redArg();
    return v___x_203_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalChange_spec__0___boxed(
    mut v_00_u03b1_204_: *mut crate::leanh::LeanObject,
    mut v___y_205_: *mut crate::leanh::LeanObject,
    mut v___y_206_: *mut crate::leanh::LeanObject,
    mut v___y_207_: *mut crate::leanh::LeanObject,
    mut v___y_208_: *mut crate::leanh::LeanObject,
    mut v___y_209_: *mut crate::leanh::LeanObject,
    mut v___y_210_: *mut crate::leanh::LeanObject,
    mut v___y_211_: *mut crate::leanh::LeanObject,
    mut v___y_212_: *mut crate::leanh::LeanObject,
    mut v___y_213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_214_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalChange_spec__0(
            v_00_u03b1_204_,
            v___y_205_,
            v___y_206_,
            v___y_207_,
            v___y_208_,
            v___y_209_,
            v___y_210_,
            v___y_211_,
            v___y_212_,
        );
    crate::leanh::lean_dec(v___y_212_);
    crate::leanh::lean_dec_ref(v___y_211_);
    crate::leanh::lean_dec(v___y_210_);
    crate::leanh::lean_dec_ref(v___y_209_);
    crate::leanh::lean_dec(v___y_208_);
    crate::leanh::lean_dec_ref(v___y_207_);
    crate::leanh::lean_dec(v___y_206_);
    crate::leanh::lean_dec_ref(v___y_205_);
    return v_res_214_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalChange___lam__0(
    mut v_e_216_: *mut crate::leanh::LeanObject,
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
    let mut v_a_231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_243_: u8 = 0;
    let mut v___x_245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_247_: u8 = 0;
    let mut v_a_248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_251_: u8 = 0;
    let mut v___x_253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_255_: u8 = 0;
    let mut v_a_256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_259_: u8 = 0;
    let mut v___x_261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_263_: u8 = 0;
    let mut v_a_264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_267_: u8 = 0;
    let mut v___x_269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_271_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_226_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(
                    v___y_218_, v___y_221_, v___y_222_, v___y_223_, v___y_224_,
                );
                if crate::leanh::lean_obj_tag(v___x_226_) == 0 {
                    v_a_227_ = crate::leanh::lean_ctor_get(v___x_226_, 0);
                    crate::leanh::lean_inc(v_a_227_);
                    crate::leanh::lean_dec_ref_known(v___x_226_, 1);
                    v___x_228_ = lean_st_ref_get(v___y_222_);
                    v___x_229_ = l_Lean_Elab_Tactic_Conv_evalChange___lam__0___closed__0;
                    v___x_230_ = l_Lean_Elab_Tactic_elabChange(
                        v_a_227_, v_e_216_, v___x_229_, v___y_217_, v___y_218_, v___y_219_,
                        v___y_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_230_) == 0 {
                        v_a_231_ = crate::leanh::lean_ctor_get(v___x_230_, 0);
                        crate::leanh::lean_inc_n(v_a_231_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_230_, 1);
                        v___x_232_ = l_Lean_Meta_getMVars(
                            v_a_231_, v___y_221_, v___y_222_, v___y_223_, v___y_224_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_232_) == 0 {
                            v_mctx_233_ = crate::leanh::lean_ctor_get(v___x_228_, 0);
                            crate::leanh::lean_inc_ref(v_mctx_233_);
                            crate::leanh::lean_dec(v___x_228_);
                            v_a_234_ = crate::leanh::lean_ctor_get(v___x_232_, 0);
                            crate::leanh::lean_inc(v_a_234_);
                            crate::leanh::lean_dec_ref_known(v___x_232_, 1);
                            v_mvarCounter_235_ = crate::leanh::lean_ctor_get(v_mctx_233_, 3);
                            crate::leanh::lean_inc(v_mvarCounter_235_);
                            crate::leanh::lean_dec_ref(v_mctx_233_);
                            v___x_236_ = l_Lean_Elab_Tactic_filterOldMVars___redArg(
                                v_a_234_,
                                v_mvarCounter_235_,
                                v___y_222_,
                            );
                            crate::leanh::lean_dec(v_mvarCounter_235_);
                            crate::leanh::lean_dec(v_a_234_);
                            if crate::leanh::lean_obj_tag(v___x_236_) == 0 {
                                v_a_237_ = crate::leanh::lean_ctor_get(v___x_236_, 0);
                                crate::leanh::lean_inc(v_a_237_);
                                crate::leanh::lean_dec_ref_known(v___x_236_, 1);
                                v___x_238_ = l_Lean_Elab_Tactic_logUnassignedAndAbort(
                                    v_a_237_, v___y_217_, v___y_218_, v___y_219_, v___y_220_,
                                    v___y_221_, v___y_222_, v___y_223_, v___y_224_,
                                );
                                crate::leanh::lean_dec(v_a_237_);
                                if crate::leanh::lean_obj_tag(v___x_238_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_238_, 1);
                                    v___x_239_ = l_Lean_Elab_Tactic_Conv_changeLhs(
                                        v_a_231_, v___y_217_, v___y_218_, v___y_219_, v___y_220_,
                                        v___y_221_, v___y_222_, v___y_223_, v___y_224_,
                                    );
                                    return v___x_239_;
                                } else {
                                    crate::leanh::lean_dec(v_a_231_);
                                    return v___x_238_;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_231_);
                                v_a_240_ = crate::leanh::lean_ctor_get(v___x_236_, 0);
                                v_isSharedCheck_247_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_236_)) as u8;
                                if v_isSharedCheck_247_ == 0 {
                                    v___x_242_ = v___x_236_;
                                    v_isShared_243_ = v_isSharedCheck_247_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_240_);
                                    crate::leanh::lean_dec(v___x_236_);
                                    v___x_242_ = crate::leanh::lean_box(0);
                                    v_isShared_243_ = v_isSharedCheck_247_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_231_);
                            crate::leanh::lean_dec(v___x_228_);
                            v_a_248_ = crate::leanh::lean_ctor_get(v___x_232_, 0);
                            v_isSharedCheck_255_ =
                                (!crate::leanh::lean_is_exclusive(v___x_232_)) as u8;
                            if v_isSharedCheck_255_ == 0 {
                                v___x_250_ = v___x_232_;
                                v_isShared_251_ = v_isSharedCheck_255_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_248_);
                                crate::leanh::lean_dec(v___x_232_);
                                v___x_250_ = crate::leanh::lean_box(0);
                                v_isShared_251_ = v_isSharedCheck_255_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_228_);
                        v_a_256_ = crate::leanh::lean_ctor_get(v___x_230_, 0);
                        v_isSharedCheck_263_ = (!crate::leanh::lean_is_exclusive(v___x_230_)) as u8;
                        if v_isSharedCheck_263_ == 0 {
                            v___x_258_ = v___x_230_;
                            v_isShared_259_ = v_isSharedCheck_263_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_256_);
                            crate::leanh::lean_dec(v___x_230_);
                            v___x_258_ = crate::leanh::lean_box(0);
                            v_isShared_259_ = v_isSharedCheck_263_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_e_216_);
                    v_a_264_ = crate::leanh::lean_ctor_get(v___x_226_, 0);
                    v_isSharedCheck_271_ = (!crate::leanh::lean_is_exclusive(v___x_226_)) as u8;
                    if v_isSharedCheck_271_ == 0 {
                        v___x_266_ = v___x_226_;
                        v_isShared_267_ = v_isSharedCheck_271_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_264_);
                        crate::leanh::lean_dec(v___x_226_);
                        v___x_266_ = crate::leanh::lean_box(0);
                        v_isShared_267_ = v_isSharedCheck_271_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_243_ == 0 {
                    v___x_245_ = v___x_242_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_246_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_246_, 0, v_a_240_);
                    v___x_245_ = v_reuseFailAlloc_246_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_245_;
            }
            3 => {
                if v_isShared_251_ == 0 {
                    v___x_253_ = v___x_250_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_254_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_254_, 0, v_a_248_);
                    v___x_253_ = v_reuseFailAlloc_254_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_253_;
            }
            5 => {
                if v_isShared_259_ == 0 {
                    v___x_261_ = v___x_258_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_262_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_262_, 0, v_a_256_);
                    v___x_261_ = v_reuseFailAlloc_262_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_261_;
            }
            7 => {
                if v_isShared_267_ == 0 {
                    v___x_269_ = v___x_266_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_270_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_270_, 0, v_a_264_);
                    v___x_269_ = v_reuseFailAlloc_270_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_269_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalChange___lam__0___boxed(
    mut v_e_272_: *mut crate::leanh::LeanObject,
    mut v___y_273_: *mut crate::leanh::LeanObject,
    mut v___y_274_: *mut crate::leanh::LeanObject,
    mut v___y_275_: *mut crate::leanh::LeanObject,
    mut v___y_276_: *mut crate::leanh::LeanObject,
    mut v___y_277_: *mut crate::leanh::LeanObject,
    mut v___y_278_: *mut crate::leanh::LeanObject,
    mut v___y_279_: *mut crate::leanh::LeanObject,
    mut v___y_280_: *mut crate::leanh::LeanObject,
    mut v___y_281_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_282_ = l_Lean_Elab_Tactic_Conv_evalChange___lam__0(
        v_e_272_, v___y_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_,
        v___y_279_, v___y_280_,
    );
    crate::leanh::lean_dec(v___y_280_);
    crate::leanh::lean_dec_ref(v___y_279_);
    crate::leanh::lean_dec(v___y_278_);
    crate::leanh::lean_dec_ref(v___y_277_);
    crate::leanh::lean_dec(v___y_276_);
    crate::leanh::lean_dec_ref(v___y_275_);
    crate::leanh::lean_dec(v___y_274_);
    crate::leanh::lean_dec_ref(v___y_273_);
    return v_res_282_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalChange(
    mut v_stx_294_: *mut crate::leanh::LeanObject,
    mut v_a_295_: *mut crate::leanh::LeanObject,
    mut v_a_296_: *mut crate::leanh::LeanObject,
    mut v_a_297_: *mut crate::leanh::LeanObject,
    mut v_a_298_: *mut crate::leanh::LeanObject,
    mut v_a_299_: *mut crate::leanh::LeanObject,
    mut v_a_300_: *mut crate::leanh::LeanObject,
    mut v_a_301_: *mut crate::leanh::LeanObject,
    mut v_a_302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_305_: u8 = 0;
    v___x_304_ = l_Lean_Elab_Tactic_Conv_evalChange___closed__5;
    crate::leanh::lean_inc(v_stx_294_);
    v___x_305_ = l_Lean_Syntax_isOfKind(v_stx_294_, v___x_304_);
    if v___x_305_ == 0 {
        let mut v___x_306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_stx_294_);
        v___x_306_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalChange_spec__0___redArg();
        return v___x_306_;
    } else {
        let mut v___x_307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_e_308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_307_ = crate::leanh::lean_unsigned_to_nat(1);
        v_e_308_ = l_Lean_Syntax_getArg(v_stx_294_, v___x_307_);
        crate::leanh::lean_dec(v_stx_294_);
        v___f_309_ = crate::leanh::lean_alloc_closure(
            l_Lean_Elab_Tactic_Conv_evalChange___lam__0___boxed as *mut core::ffi::c_void,
            10,
            1,
        );
        crate::leanh::lean_closure_set(v___f_309_, 0, v_e_308_);
        v___x_310_ = l_Lean_Elab_Tactic_withMainContext___redArg(
            v___f_309_, v_a_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_,
            v_a_302_,
        );
        return v___x_310_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalChange___boxed(
    mut v_stx_311_: *mut crate::leanh::LeanObject,
    mut v_a_312_: *mut crate::leanh::LeanObject,
    mut v_a_313_: *mut crate::leanh::LeanObject,
    mut v_a_314_: *mut crate::leanh::LeanObject,
    mut v_a_315_: *mut crate::leanh::LeanObject,
    mut v_a_316_: *mut crate::leanh::LeanObject,
    mut v_a_317_: *mut crate::leanh::LeanObject,
    mut v_a_318_: *mut crate::leanh::LeanObject,
    mut v_a_319_: *mut crate::leanh::LeanObject,
    mut v_a_320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_321_ = l_Lean_Elab_Tactic_Conv_evalChange(
        v_stx_311_, v_a_312_, v_a_313_, v_a_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_,
    );
    crate::leanh::lean_dec(v_a_319_);
    crate::leanh::lean_dec_ref(v_a_318_);
    crate::leanh::lean_dec(v_a_317_);
    crate::leanh::lean_dec_ref(v_a_316_);
    crate::leanh::lean_dec(v_a_315_);
    crate::leanh::lean_dec_ref(v_a_314_);
    crate::leanh::lean_dec(v_a_313_);
    crate::leanh::lean_dec_ref(v_a_312_);
    return v_res_321_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_331_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_332_ = l_Lean_Elab_Tactic_Conv_evalChange___closed__5;
    v___x_333_ = l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__2;
    v___x_334_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Conv_evalChange___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_335_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_331_, v___x_332_, v___x_333_, v___x_334_,
    );
    return v___x_335_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___boxed(
    mut v_a_336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_337_ = l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1();
    return v_res_337_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_364_ = l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__2;
    v___x_365_ = l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___closed__6;
    v___x_366_ = l_Lean_addBuiltinDeclarationRanges(v___x_364_, v___x_365_);
    return v___x_366_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3___boxed(
    mut v_a_367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_368_ = l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3();
    return v_res_368_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Conv_Change(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Change(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Conv_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Change_0__Lean_Elab_Tactic_Conv_evalChange___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Conv_Change(
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
pub unsafe fn initialize_Lean_Elab_Tactic_Conv_Change(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Change(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Conv_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Conv_Change(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Conv_Change(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Conv_Change(builtin);
}
