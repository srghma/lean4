// Lean compiler output
// Module: Lean.Elab.Tactic.Change
// Imports: Lean.Meta.Tactic.Replace Lean.Elab.Tactic.Location
use crate::r#gen::Init::Meta::Defs::{l_Lean_Syntax_isNone, l_Lean_mkOptionalNode};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull,
};
use crate::r#gen::Lean::DocString::Extension::l_Lean_addBuiltinDocString;
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::SyntheticMVars::l_Lean_Elab_Term_synthesizeSyntheticMVars;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    l_Lean_Elab_Tactic_getMainGoal___redArg, l_Lean_Elab_Tactic_getMainTag___redArg,
    l_Lean_Elab_Tactic_getMainTarget, l_Lean_Elab_Tactic_replaceMainGoal___redArg,
    l_Lean_Elab_Tactic_tacticElabAttribute, l_Lean_Elab_Tactic_withMainContext___redArg,
};
use crate::r#gen::Lean::Elab::Tactic::ElabTerm::{
    l_Lean_Elab_Tactic_runTermElab___redArg, l_Lean_Elab_Tactic_withCollectingNewGoalsFrom,
};
use crate::r#gen::Lean::Elab::Tactic::Location::{
    initialize_Lean_Elab_Tactic_Location, l_Lean_Elab_Tactic_expandOptLocation,
    l_Lean_Elab_Tactic_withLocation, runtime_initialize_Lean_Elab_Tactic_Location,
};
use crate::r#gen::Lean::Elab::Term::TermElabM::l_Lean_Elab_Term_elabTermEnsuringType;
use crate::r#gen::Lean::Expr::l_Lean_Expr_hasMVar;
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Message::{l_Lean_indentExpr, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey, l_Lean_FVarId_getType___redArg,
    l_Lean_MessageData_ofLazyM, l_Lean_Meta_Context_config, l_Lean_Meta_isExprDefEq,
};
use crate::r#gen::Lean::Meta::Check::l_Lean_Meta_addPPExplicitToExposeDiff;
use crate::r#gen::Lean::Meta::Tactic::Replace::{
    initialize_Lean_Meta_Tactic_Replace, l_Lean_MVarId_changeLocalDecl,
    l_Lean_MVarId_replaceTargetDefEq, runtime_initialize_Lean_Meta_Tactic_Replace,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::lean_imports_rs::Init::Prelude::{lean_array_push, lean_mk_empty_array_with_capacity};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
pub static l_Lean_Elab_Tactic_elabChangeDefaultError___redArg___closed__0_value:
    crate::leanh::LeanStringObject<32> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 32,
    m_capacity: 32,
    m_length: 31,
    m_data: [
        39, 99, 104, 97, 110, 103, 101, 39, 32, 116, 97, 99, 116, 105, 99, 32, 102, 97, 105, 108,
        101, 100, 44, 32, 112, 97, 116, 116, 101, 114, 110, 0,
    ],
};
static mut l_Lean_Elab_Tactic_elabChangeDefaultError___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_elabChangeDefaultError___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_elabChangeDefaultError___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_elabChangeDefaultError___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_elabChangeDefaultError___redArg___closed__2_value:
    crate::leanh::LeanStringObject<39> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 39,
    m_capacity: 39,
    m_length: 38,
    m_data: [
        10, 105, 115, 32, 110, 111, 116, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 97,
        108, 108, 121, 32, 101, 113, 117, 97, 108, 32, 116, 111, 32, 116, 97, 114, 103, 101, 116,
        0,
    ],
};
static mut l_Lean_Elab_Tactic_elabChangeDefaultError___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_elabChangeDefaultError___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_elabChangeDefaultError___redArg___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_elabChangeDefaultError___redArg___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalChange_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalChange_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_evalChange___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        39, 99, 104, 97, 110, 103, 101, 39, 32, 116, 97, 99, 116, 105, 99, 32, 102, 97, 105, 108,
        101, 100, 0,
    ],
};
static mut l_Lean_Elab_Tactic_evalChange___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalChange___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_evalChange___lam__0___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_evalChange___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_evalChange___lam__2___closed__0_value:
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
static mut l_Lean_Elab_Tactic_evalChange___lam__2___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalChange___lam__2___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_evalChange___closed__0_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Lean_Elab_Tactic_evalChange___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalChange___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_evalChange___closed__1_value: crate::leanh::LeanStringObject<7> =
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
static mut l_Lean_Elab_Tactic_evalChange___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalChange___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_evalChange___closed__2_value: crate::leanh::LeanStringObject<7> =
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
static mut l_Lean_Elab_Tactic_evalChange___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalChange___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_evalChange___closed__3_value: crate::leanh::LeanStringObject<7> =
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
static mut l_Lean_Elab_Tactic_evalChange___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalChange___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_evalChange___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalChange___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_evalChange___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalChange___closed__4_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalChange___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_evalChange___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalChange___closed__4_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalChange___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_evalChange___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalChange___closed__4_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalChange___closed__3_value)
                as *mut crate::leanh::LeanObject,
            16580879115603664356 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_evalChange___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalChange___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_evalChange___closed__5_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Elab_Tactic_evalChange___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 10,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Tactic_evalChange___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalChange___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_evalChange___closed__6_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [108, 111, 99, 97, 116, 105, 111, 110, 0],
    };
static mut l_Lean_Elab_Tactic_evalChange___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalChange___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_evalChange___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalChange___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_evalChange___closed__7_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalChange___closed__7_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalChange___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_evalChange___closed__7_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalChange___closed__7_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalChange___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_evalChange___closed__7_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalChange___closed__7_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalChange___closed__6_value)
                as *mut crate::leanh::LeanObject,
            1767494567867404924 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_evalChange___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalChange___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange__1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange__1___closed__1_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [101, 118, 97, 108, 67, 104, 97, 110, 103, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange__1___closed__1_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange__1___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalChange___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange__1___closed__2_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange__1___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange__1___closed__0_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange__1___closed__2_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange__1___closed__2_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalChange___closed__2_value) as *mut crate::leanh::LeanObject,12733524109236233889 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange__1___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange__1___closed__2_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange__1___closed__1_value) as *mut crate::leanh::LeanObject,10601168373339553852 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange_docString__3___closed__0_value: crate::leanh::LeanStringObject<758> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 758, m_capacity: 758, m_length: 753, m_data: [96, 99, 104, 97, 110, 103, 101, 96, 32, 99, 97, 110, 32, 98, 101, 32, 117, 115, 101, 100, 32, 116, 111, 32, 114, 101, 112, 108, 97, 99, 101, 32, 116, 104, 101, 32, 109, 97, 105, 110, 32, 103, 111, 97, 108, 32, 111, 114, 32, 105, 116, 115, 32, 104, 121, 112, 111, 116, 104, 101, 115, 101, 115, 32, 119, 105, 116, 104, 10, 100, 105, 102, 102, 101, 114, 101, 110, 116, 44, 32, 121, 101, 116, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 97, 108, 108, 121, 32, 101, 113, 117, 97, 108, 44, 32, 103, 111, 97, 108, 32, 111, 114, 32, 104, 121, 112, 111, 116, 104, 101, 115, 101, 115, 46, 10, 10, 70, 111, 114, 32, 101, 120, 97, 109, 112, 108, 101, 44, 32, 105, 102, 32, 96, 110, 32, 58, 32, 78, 97, 116, 96, 32, 97, 110, 100, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 103, 111, 97, 108, 32, 105, 115, 32, 96, 226, 138, 162, 32, 110, 32, 43, 32, 50, 32, 61, 32, 50, 96, 44, 32, 116, 104, 101, 110, 10, 96, 96, 96, 108, 101, 97, 110, 10, 99, 104, 97, 110, 103, 101, 32, 95, 32, 43, 32, 49, 32, 61, 32, 95, 10, 96, 96, 96, 10, 99, 104, 97, 110, 103, 101, 115, 32, 116, 104, 101, 32, 103, 111, 97, 108, 32, 116, 111, 32, 96, 226, 138, 162, 32, 110, 32, 43, 32, 49, 32, 43, 32, 49, 32, 61, 32, 50, 96, 46, 10, 10, 84, 104, 101, 32, 116, 97, 99, 116, 105, 99, 32, 97, 108, 115, 111, 32, 97, 112, 112, 108, 105, 101, 115, 32, 116, 111, 32, 104, 121, 112, 111, 116, 104, 101, 115, 101, 115, 46, 32, 73, 102, 32, 96, 104, 32, 58, 32, 110, 32, 43, 32, 50, 32, 61, 32, 50, 96, 32, 97, 110, 100, 32, 96, 104, 39, 32, 58, 32, 110, 32, 43, 32, 51, 32, 61, 32, 52, 96, 10, 97, 114, 101, 32, 104, 121, 112, 111, 116, 104, 101, 115, 101, 115, 44, 32, 116, 104, 101, 110, 10, 96, 96, 96, 108, 101, 97, 110, 10, 99, 104, 97, 110, 103, 101, 32, 95, 32, 43, 32, 49, 32, 61, 32, 95, 32, 97, 116, 32, 104, 32, 104, 39, 10, 96, 96, 96, 10, 99, 104, 97, 110, 103, 101, 115, 32, 116, 104, 101, 105, 114, 32, 116, 121, 112, 101, 115, 32, 116, 111, 32, 98, 101, 32, 96, 104, 32, 58, 32, 110, 32, 43, 32, 49, 32, 43, 32, 49, 32, 61, 32, 50, 96, 32, 97, 110, 100, 32, 96, 104, 39, 32, 58, 32, 110, 32, 43, 32, 50, 32, 43, 32, 49, 32, 61, 32, 52, 96, 46, 10, 10, 67, 104, 97, 110, 103, 101, 32, 105, 115, 32, 108, 105, 107, 101, 32, 96, 114, 101, 102, 105, 110, 101, 96, 32, 105, 110, 32, 116, 104, 97, 116, 32, 101, 118, 101, 114, 121, 32, 112, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 32, 110, 101, 101, 100, 115, 32, 116, 111, 32, 98, 101, 32, 115, 111, 108, 118, 101, 100, 32, 102, 111, 114, 32, 98, 121, 32, 117, 110, 105, 102, 105, 99, 97, 116, 105, 111, 110, 44, 10, 98, 117, 116, 32, 117, 115, 105, 110, 103, 32, 110, 97, 109, 101, 100, 32, 112, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 115, 32, 111, 114, 32, 96, 63, 95, 96, 32, 114, 101, 115, 117, 108, 116, 115, 32, 105, 110, 32, 96, 99, 104, 97, 110, 103, 101, 96, 32, 116, 111, 32, 99, 114, 101, 97, 116, 105, 110, 103, 32, 110, 101, 119, 32, 103, 111, 97, 108, 115, 46, 10, 10, 84, 104, 101, 32, 116, 97, 99, 116, 105, 99, 32, 96, 115, 104, 111, 119, 32, 101, 96, 32, 105, 115, 32, 105, 110, 116, 101, 114, 99, 104, 97, 110, 103, 101, 97, 98, 108, 101, 32, 119, 105, 116, 104, 32, 96, 99, 104, 97, 110, 103, 101, 32, 101, 96, 44, 32, 119, 104, 101, 114, 101, 32, 116, 104, 101, 32, 112, 97, 116, 116, 101, 114, 110, 32, 96, 101, 96, 32, 105, 115, 32, 97, 112, 112, 108, 105, 101, 100, 32, 116, 111, 10, 116, 104, 101, 32, 109, 97, 105, 110, 32, 103, 111, 97, 108, 46, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange_docString__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange_docString__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Lean_Elab_Tactic_elabChangeDefaultError___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_768_ = l_Lean_Elab_Tactic_elabChangeDefaultError___redArg___closed__0;
    v___x_769_ = l_Lean_stringToMessageData(v___x_768_);
    return v___x_769_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_elabChangeDefaultError___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_771_ = l_Lean_Elab_Tactic_elabChangeDefaultError___redArg___closed__2;
    v___x_772_ = l_Lean_stringToMessageData(v___x_771_);
    return v___x_772_;
}
pub unsafe fn l_Lean_Elab_Tactic_elabChangeDefaultError___redArg(
    mut v_p_773_: *mut crate::leanh::LeanObject,
    mut v_tgt_774_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_776_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_elabChangeDefaultError___redArg___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_elabChangeDefaultError___redArg___closed__1_once
        ),
        _init_l_Lean_Elab_Tactic_elabChangeDefaultError___redArg___closed__1,
    );
    v___x_777_ = l_Lean_indentExpr(v_p_773_);
    v___x_778_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_778_, 0, v___x_776_);
    crate::leanh::lean_ctor_set(v___x_778_, 1, v___x_777_);
    v___x_779_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_elabChangeDefaultError___redArg___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_elabChangeDefaultError___redArg___closed__3_once
        ),
        _init_l_Lean_Elab_Tactic_elabChangeDefaultError___redArg___closed__3,
    );
    v___x_780_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_780_, 0, v___x_778_);
    crate::leanh::lean_ctor_set(v___x_780_, 1, v___x_779_);
    v___x_781_ = l_Lean_indentExpr(v_tgt_774_);
    v___x_782_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_782_, 0, v___x_780_);
    crate::leanh::lean_ctor_set(v___x_782_, 1, v___x_781_);
    v___x_783_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_783_, 0, v___x_782_);
    return v___x_783_;
}
pub unsafe fn l_Lean_Elab_Tactic_elabChangeDefaultError___redArg___boxed(
    mut v_p_784_: *mut crate::leanh::LeanObject,
    mut v_tgt_785_: *mut crate::leanh::LeanObject,
    mut v_a_786_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_787_ = l_Lean_Elab_Tactic_elabChangeDefaultError___redArg(v_p_784_, v_tgt_785_);
    return v_res_787_;
}
pub unsafe fn l_Lean_Elab_Tactic_elabChangeDefaultError(
    mut v_p_788_: *mut crate::leanh::LeanObject,
    mut v_tgt_789_: *mut crate::leanh::LeanObject,
    mut v_a_790_: *mut crate::leanh::LeanObject,
    mut v_a_791_: *mut crate::leanh::LeanObject,
    mut v_a_792_: *mut crate::leanh::LeanObject,
    mut v_a_793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_795_ = l_Lean_Elab_Tactic_elabChangeDefaultError___redArg(v_p_788_, v_tgt_789_);
    return v___x_795_;
}
pub unsafe fn l_Lean_Elab_Tactic_elabChangeDefaultError___boxed(
    mut v_p_796_: *mut crate::leanh::LeanObject,
    mut v_tgt_797_: *mut crate::leanh::LeanObject,
    mut v_a_798_: *mut crate::leanh::LeanObject,
    mut v_a_799_: *mut crate::leanh::LeanObject,
    mut v_a_800_: *mut crate::leanh::LeanObject,
    mut v_a_801_: *mut crate::leanh::LeanObject,
    mut v_a_802_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_803_ = l_Lean_Elab_Tactic_elabChangeDefaultError(
        v_p_796_, v_tgt_797_, v_a_798_, v_a_799_, v_a_800_, v_a_801_,
    );
    crate::leanh::lean_dec(v_a_801_);
    crate::leanh::lean_dec_ref(v_a_800_);
    crate::leanh::lean_dec(v_a_799_);
    crate::leanh::lean_dec_ref(v_a_798_);
    return v_res_803_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabChange_spec__1___redArg(
    mut v_e_804_: *mut crate::leanh::LeanObject,
    mut v___y_805_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_807_: u8 = 0;
    let mut v___x_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_821_: u8 = 0;
    let mut v___x_823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_827_: u8 = 0;
    let mut v_unused_828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_807_ = l_Lean_Expr_hasMVar(v_e_804_);
                if v___x_807_ == 0 {
                    v___x_808_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_808_, 0, v_e_804_);
                    return v___x_808_;
                } else {
                    v___x_809_ = lean_st_ref_get(v___y_805_);
                    v_mctx_810_ = crate::leanh::lean_ctor_get(v___x_809_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_810_);
                    crate::leanh::lean_dec(v___x_809_);
                    v___x_811_ = l_Lean_instantiateMVarsCore(v_mctx_810_, v_e_804_);
                    v_fst_812_ = crate::leanh::lean_ctor_get(v___x_811_, 0);
                    crate::leanh::lean_inc(v_fst_812_);
                    v_snd_813_ = crate::leanh::lean_ctor_get(v___x_811_, 1);
                    crate::leanh::lean_inc(v_snd_813_);
                    crate::leanh::lean_dec_ref(v___x_811_);
                    v___x_814_ = lean_st_ref_take(v___y_805_);
                    v_cache_815_ = crate::leanh::lean_ctor_get(v___x_814_, 1);
                    v_zetaDeltaFVarIds_816_ = crate::leanh::lean_ctor_get(v___x_814_, 2);
                    v_postponed_817_ = crate::leanh::lean_ctor_get(v___x_814_, 3);
                    v_diag_818_ = crate::leanh::lean_ctor_get(v___x_814_, 4);
                    v_isSharedCheck_827_ = (!crate::leanh::lean_is_exclusive(v___x_814_)) as u8;
                    if v_isSharedCheck_827_ == 0 {
                        v_unused_828_ = crate::leanh::lean_ctor_get(v___x_814_, 0);
                        crate::leanh::lean_dec(v_unused_828_);
                        v___x_820_ = v___x_814_;
                        v_isShared_821_ = v_isSharedCheck_827_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_818_);
                        crate::leanh::lean_inc(v_postponed_817_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_816_);
                        crate::leanh::lean_inc(v_cache_815_);
                        crate::leanh::lean_dec(v___x_814_);
                        v___x_820_ = crate::leanh::lean_box(0);
                        v_isShared_821_ = v_isSharedCheck_827_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_821_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_820_, 0, v_snd_813_);
                    v___x_823_ = v___x_820_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_826_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_826_, 0, v_snd_813_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_826_, 1, v_cache_815_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_826_, 2, v_zetaDeltaFVarIds_816_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_826_, 3, v_postponed_817_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_826_, 4, v_diag_818_);
                    v___x_823_ = v_reuseFailAlloc_826_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_824_ = lean_st_ref_set(v___y_805_, v___x_823_);
                v___x_825_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_825_, 0, v_fst_812_);
                return v___x_825_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabChange_spec__1___redArg___boxed(
    mut v_e_829_: *mut crate::leanh::LeanObject,
    mut v___y_830_: *mut crate::leanh::LeanObject,
    mut v___y_831_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_832_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabChange_spec__1___redArg(
        v_e_829_, v___y_830_,
    );
    crate::leanh::lean_dec(v___y_830_);
    return v_res_832_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabChange_spec__1(
    mut v_e_833_: *mut crate::leanh::LeanObject,
    mut v___y_834_: *mut crate::leanh::LeanObject,
    mut v___y_835_: *mut crate::leanh::LeanObject,
    mut v___y_836_: *mut crate::leanh::LeanObject,
    mut v___y_837_: *mut crate::leanh::LeanObject,
    mut v___y_838_: *mut crate::leanh::LeanObject,
    mut v___y_839_: *mut crate::leanh::LeanObject,
    mut v___y_840_: *mut crate::leanh::LeanObject,
    mut v___y_841_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_843_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabChange_spec__1___redArg(
        v_e_833_, v___y_839_,
    );
    return v___x_843_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabChange_spec__1___boxed(
    mut v_e_844_: *mut crate::leanh::LeanObject,
    mut v___y_845_: *mut crate::leanh::LeanObject,
    mut v___y_846_: *mut crate::leanh::LeanObject,
    mut v___y_847_: *mut crate::leanh::LeanObject,
    mut v___y_848_: *mut crate::leanh::LeanObject,
    mut v___y_849_: *mut crate::leanh::LeanObject,
    mut v___y_850_: *mut crate::leanh::LeanObject,
    mut v___y_851_: *mut crate::leanh::LeanObject,
    mut v___y_852_: *mut crate::leanh::LeanObject,
    mut v___y_853_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_854_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabChange_spec__1(
        v_e_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_,
        v___y_851_, v___y_852_,
    );
    crate::leanh::lean_dec(v___y_852_);
    crate::leanh::lean_dec_ref(v___y_851_);
    crate::leanh::lean_dec(v___y_850_);
    crate::leanh::lean_dec_ref(v___y_849_);
    crate::leanh::lean_dec(v___y_848_);
    crate::leanh::lean_dec_ref(v___y_847_);
    crate::leanh::lean_dec(v___y_846_);
    crate::leanh::lean_dec_ref(v___y_845_);
    return v_res_854_;
}
pub unsafe fn l_Lean_Elab_Tactic_elabChange___lam__0(
    mut v_e_855_: *mut crate::leanh::LeanObject,
    mut v_p_856_: *mut crate::leanh::LeanObject,
    mut v___y_857_: *mut crate::leanh::LeanObject,
    mut v___y_858_: *mut crate::leanh::LeanObject,
    mut v___y_859_: *mut crate::leanh::LeanObject,
    mut v___y_860_: *mut crate::leanh::LeanObject,
    mut v___y_861_: *mut crate::leanh::LeanObject,
    mut v___y_862_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_868_: u8 = 0;
    let mut v___x_870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_871_: u8 = 0;
    let mut v___x_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_879_: u8 = 0;
    let mut v___x_880_: u8 = 0;
    let mut v___x_881_: u8 = 0;
    let mut v___x_882_: u8 = 0;
    let mut v___x_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_887_: u8 = 0;
    let mut v___x_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_891_: u8 = 0;
    let mut v_unused_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_896_: u8 = 0;
    let mut v___x_898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_900_: u8 = 0;
    let mut v_a_901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_904_: u8 = 0;
    let mut v___x_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_908_: u8 = 0;
    let mut v___x_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_912_: u8 = 0;
    let mut v_a_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_916_: u8 = 0;
    let mut v___x_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_920_: u8 = 0;
    let mut v_reuseFailAlloc_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_922_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_862_);
                crate::leanh::lean_inc_ref(v___y_861_);
                crate::leanh::lean_inc(v___y_860_);
                crate::leanh::lean_inc_ref(v___y_859_);
                crate::leanh::lean_inc_ref(v_e_855_);
                v___x_864_ =
                    lean_infer_type(v_e_855_, v___y_859_, v___y_860_, v___y_861_, v___y_862_);
                if crate::leanh::lean_obj_tag(v___x_864_) == 0 {
                    v_a_865_ = crate::leanh::lean_ctor_get(v___x_864_, 0);
                    v_isSharedCheck_922_ = (!crate::leanh::lean_is_exclusive(v___x_864_)) as u8;
                    if v_isSharedCheck_922_ == 0 {
                        v___x_867_ = v___x_864_;
                        v_isShared_868_ = v_isSharedCheck_922_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_865_);
                        crate::leanh::lean_dec(v___x_864_);
                        v___x_867_ = crate::leanh::lean_box(0);
                        v_isShared_868_ = v_isSharedCheck_922_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___y_862_);
                    crate::leanh::lean_dec_ref(v___y_861_);
                    crate::leanh::lean_dec(v___y_860_);
                    crate::leanh::lean_dec_ref(v___y_859_);
                    crate::leanh::lean_dec(v_p_856_);
                    crate::leanh::lean_dec_ref(v_e_855_);
                    return v___x_864_;
                }
            }
            1 => {
                if v_isShared_868_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_867_, 1);
                    v___x_870_ = v___x_867_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_921_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_921_, 0, v_a_865_);
                    v___x_870_ = v_reuseFailAlloc_921_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_871_ = 1;
                v___x_872_ = crate::leanh::lean_box(0);
                v___x_873_ = l_Lean_Elab_Term_elabTermEnsuringType(
                    v_p_856_, v___x_870_, v___x_871_, v___x_871_, v___x_872_, v___y_857_,
                    v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_,
                );
                if crate::leanh::lean_obj_tag(v___x_873_) == 0 {
                    v_a_874_ = crate::leanh::lean_ctor_get(v___x_873_, 0);
                    crate::leanh::lean_inc_n(v_a_874_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_873_, 1);
                    crate::leanh::lean_inc_ref(v_e_855_);
                    v___x_875_ = l_Lean_Meta_isExprDefEq(
                        v_a_874_, v_e_855_, v___y_859_, v___y_860_, v___y_861_, v___y_862_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_875_) == 0 {
                        v_a_876_ = crate::leanh::lean_ctor_get(v___x_875_, 0);
                        v_isSharedCheck_912_ = (!crate::leanh::lean_is_exclusive(v___x_875_)) as u8;
                        if v_isSharedCheck_912_ == 0 {
                            v___x_878_ = v___x_875_;
                            v_isShared_879_ = v_isSharedCheck_912_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_876_);
                            crate::leanh::lean_dec(v___x_875_);
                            v___x_878_ = crate::leanh::lean_box(0);
                            v_isShared_879_ = v_isSharedCheck_912_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_874_);
                        crate::leanh::lean_dec(v___y_862_);
                        crate::leanh::lean_dec_ref(v___y_861_);
                        crate::leanh::lean_dec(v___y_860_);
                        crate::leanh::lean_dec_ref(v___y_859_);
                        crate::leanh::lean_dec_ref(v_e_855_);
                        v_a_913_ = crate::leanh::lean_ctor_get(v___x_875_, 0);
                        v_isSharedCheck_920_ = (!crate::leanh::lean_is_exclusive(v___x_875_)) as u8;
                        if v_isSharedCheck_920_ == 0 {
                            v___x_915_ = v___x_875_;
                            v_isShared_916_ = v_isSharedCheck_920_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_913_);
                            crate::leanh::lean_dec(v___x_875_);
                            v___x_915_ = crate::leanh::lean_box(0);
                            v_isShared_916_ = v_isSharedCheck_920_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_862_);
                    crate::leanh::lean_dec_ref(v___y_861_);
                    crate::leanh::lean_dec(v___y_860_);
                    crate::leanh::lean_dec_ref(v___y_859_);
                    crate::leanh::lean_dec_ref(v_e_855_);
                    return v___x_873_;
                }
            }
            3 => {
                v___x_880_ = (crate::leanh::lean_unbox(v_a_876_) as u8);
                if v___x_880_ == 0 {
                    crate::leanh::lean_del_object(v___x_878_);
                    v___x_881_ = 2;
                    v___x_882_ = (crate::leanh::lean_unbox(v_a_876_) as u8);
                    crate::leanh::lean_dec(v_a_876_);
                    v___x_883_ = l_Lean_Elab_Term_synthesizeSyntheticMVars(
                        v___x_881_, v___x_882_, v___y_857_, v___y_858_, v___y_859_, v___y_860_,
                        v___y_861_, v___y_862_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_883_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_883_, 1);
                        crate::leanh::lean_inc(v_a_874_);
                        v___x_884_ = l_Lean_Meta_isExprDefEq(
                            v_a_874_, v_e_855_, v___y_859_, v___y_860_, v___y_861_, v___y_862_,
                        );
                        crate::leanh::lean_dec(v___y_862_);
                        crate::leanh::lean_dec_ref(v___y_861_);
                        crate::leanh::lean_dec(v___y_860_);
                        crate::leanh::lean_dec_ref(v___y_859_);
                        if crate::leanh::lean_obj_tag(v___x_884_) == 0 {
                            v_isSharedCheck_891_ =
                                (!crate::leanh::lean_is_exclusive(v___x_884_)) as u8;
                            if v_isSharedCheck_891_ == 0 {
                                v_unused_892_ = crate::leanh::lean_ctor_get(v___x_884_, 0);
                                crate::leanh::lean_dec(v_unused_892_);
                                v___x_886_ = v___x_884_;
                                v_isShared_887_ = v_isSharedCheck_891_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_884_);
                                v___x_886_ = crate::leanh::lean_box(0);
                                v_isShared_887_ = v_isSharedCheck_891_;
                                state = 4;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_874_);
                            v_a_893_ = crate::leanh::lean_ctor_get(v___x_884_, 0);
                            v_isSharedCheck_900_ =
                                (!crate::leanh::lean_is_exclusive(v___x_884_)) as u8;
                            if v_isSharedCheck_900_ == 0 {
                                v___x_895_ = v___x_884_;
                                v_isShared_896_ = v_isSharedCheck_900_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_893_);
                                crate::leanh::lean_dec(v___x_884_);
                                v___x_895_ = crate::leanh::lean_box(0);
                                v_isShared_896_ = v_isSharedCheck_900_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_874_);
                        crate::leanh::lean_dec(v___y_862_);
                        crate::leanh::lean_dec_ref(v___y_861_);
                        crate::leanh::lean_dec(v___y_860_);
                        crate::leanh::lean_dec_ref(v___y_859_);
                        crate::leanh::lean_dec_ref(v_e_855_);
                        v_a_901_ = crate::leanh::lean_ctor_get(v___x_883_, 0);
                        v_isSharedCheck_908_ = (!crate::leanh::lean_is_exclusive(v___x_883_)) as u8;
                        if v_isSharedCheck_908_ == 0 {
                            v___x_903_ = v___x_883_;
                            v_isShared_904_ = v_isSharedCheck_908_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_901_);
                            crate::leanh::lean_dec(v___x_883_);
                            v___x_903_ = crate::leanh::lean_box(0);
                            v_isShared_904_ = v_isSharedCheck_908_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_876_);
                    crate::leanh::lean_dec(v___y_862_);
                    crate::leanh::lean_dec_ref(v___y_861_);
                    crate::leanh::lean_dec(v___y_860_);
                    crate::leanh::lean_dec_ref(v___y_859_);
                    crate::leanh::lean_dec_ref(v_e_855_);
                    if v_isShared_879_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_878_, 0, v_a_874_);
                        v___x_910_ = v___x_878_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_911_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_911_, 0, v_a_874_);
                        v___x_910_ = v_reuseFailAlloc_911_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_887_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_886_, 0, v_a_874_);
                    v___x_889_ = v___x_886_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_890_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_890_, 0, v_a_874_);
                    v___x_889_ = v_reuseFailAlloc_890_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_889_;
            }
            6 => {
                if v_isShared_896_ == 0 {
                    v___x_898_ = v___x_895_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_899_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_899_, 0, v_a_893_);
                    v___x_898_ = v_reuseFailAlloc_899_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_898_;
            }
            8 => {
                if v_isShared_904_ == 0 {
                    v___x_906_ = v___x_903_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_907_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_907_, 0, v_a_901_);
                    v___x_906_ = v_reuseFailAlloc_907_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_906_;
            }
            10 => {
                return v___x_910_;
            }
            11 => {
                if v_isShared_916_ == 0 {
                    v___x_918_ = v___x_915_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_919_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_919_, 0, v_a_913_);
                    v___x_918_ = v_reuseFailAlloc_919_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_918_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_elabChange___lam__0___boxed(
    mut v_e_923_: *mut crate::leanh::LeanObject,
    mut v_p_924_: *mut crate::leanh::LeanObject,
    mut v___y_925_: *mut crate::leanh::LeanObject,
    mut v___y_926_: *mut crate::leanh::LeanObject,
    mut v___y_927_: *mut crate::leanh::LeanObject,
    mut v___y_928_: *mut crate::leanh::LeanObject,
    mut v___y_929_: *mut crate::leanh::LeanObject,
    mut v___y_930_: *mut crate::leanh::LeanObject,
    mut v___y_931_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_932_ = l_Lean_Elab_Tactic_elabChange___lam__0(
        v_e_923_, v_p_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_,
    );
    crate::leanh::lean_dec(v___y_926_);
    crate::leanh::lean_dec_ref(v___y_925_);
    return v_res_932_;
}
pub unsafe fn l_Lean_Elab_Tactic_elabChange___lam__1(
    mut v_a_933_: *mut crate::leanh::LeanObject,
    mut v_e_934_: *mut crate::leanh::LeanObject,
    mut v_mkDefeqError_935_: *mut crate::leanh::LeanObject,
    mut v___y_936_: *mut crate::leanh::LeanObject,
    mut v___y_937_: *mut crate::leanh::LeanObject,
    mut v___y_938_: *mut crate::leanh::LeanObject,
    mut v___y_939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_949_: u8 = 0;
    let mut v___x_951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_953_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_941_ = l_Lean_Meta_addPPExplicitToExposeDiff(
                    v_a_933_, v_e_934_, v___y_936_, v___y_937_, v___y_938_, v___y_939_,
                );
                if crate::leanh::lean_obj_tag(v___x_941_) == 0 {
                    v_a_942_ = crate::leanh::lean_ctor_get(v___x_941_, 0);
                    crate::leanh::lean_inc(v_a_942_);
                    crate::leanh::lean_dec_ref_known(v___x_941_, 1);
                    v_fst_943_ = crate::leanh::lean_ctor_get(v_a_942_, 0);
                    crate::leanh::lean_inc(v_fst_943_);
                    v_snd_944_ = crate::leanh::lean_ctor_get(v_a_942_, 1);
                    crate::leanh::lean_inc(v_snd_944_);
                    crate::leanh::lean_dec(v_a_942_);
                    v___x_945_ = crate::leanh::lean_apply_7(
                        v_mkDefeqError_935_,
                        v_fst_943_,
                        v_snd_944_,
                        v___y_936_,
                        v___y_937_,
                        v___y_938_,
                        v___y_939_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_945_;
                } else {
                    crate::leanh::lean_dec(v___y_939_);
                    crate::leanh::lean_dec_ref(v___y_938_);
                    crate::leanh::lean_dec(v___y_937_);
                    crate::leanh::lean_dec_ref(v___y_936_);
                    crate::leanh::lean_dec_ref(v_mkDefeqError_935_);
                    v_a_946_ = crate::leanh::lean_ctor_get(v___x_941_, 0);
                    v_isSharedCheck_953_ = (!crate::leanh::lean_is_exclusive(v___x_941_)) as u8;
                    if v_isSharedCheck_953_ == 0 {
                        v___x_948_ = v___x_941_;
                        v_isShared_949_ = v_isSharedCheck_953_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_946_);
                        crate::leanh::lean_dec(v___x_941_);
                        v___x_948_ = crate::leanh::lean_box(0);
                        v_isShared_949_ = v_isSharedCheck_953_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_949_ == 0 {
                    v___x_951_ = v___x_948_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_952_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_952_, 0, v_a_946_);
                    v___x_951_ = v_reuseFailAlloc_952_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_951_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_elabChange___lam__1___boxed(
    mut v_a_954_: *mut crate::leanh::LeanObject,
    mut v_e_955_: *mut crate::leanh::LeanObject,
    mut v_mkDefeqError_956_: *mut crate::leanh::LeanObject,
    mut v___y_957_: *mut crate::leanh::LeanObject,
    mut v___y_958_: *mut crate::leanh::LeanObject,
    mut v___y_959_: *mut crate::leanh::LeanObject,
    mut v___y_960_: *mut crate::leanh::LeanObject,
    mut v___y_961_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_962_ = l_Lean_Elab_Tactic_elabChange___lam__1(
        v_a_954_,
        v_e_955_,
        v_mkDefeqError_956_,
        v___y_957_,
        v___y_958_,
        v___y_959_,
        v___y_960_,
    );
    return v_res_962_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabChange_spec__0_spec__0(
    mut v_msgData_963_: *mut crate::leanh::LeanObject,
    mut v___y_964_: *mut crate::leanh::LeanObject,
    mut v___y_965_: *mut crate::leanh::LeanObject,
    mut v___y_966_: *mut crate::leanh::LeanObject,
    mut v___y_967_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_969_ = lean_st_ref_get(v___y_967_);
    v_env_970_ = crate::leanh::lean_ctor_get(v___x_969_, 0);
    crate::leanh::lean_inc_ref(v_env_970_);
    crate::leanh::lean_dec(v___x_969_);
    v___x_971_ = lean_st_ref_get(v___y_965_);
    v_mctx_972_ = crate::leanh::lean_ctor_get(v___x_971_, 0);
    crate::leanh::lean_inc_ref(v_mctx_972_);
    crate::leanh::lean_dec(v___x_971_);
    v_lctx_973_ = crate::leanh::lean_ctor_get(v___y_964_, 2);
    v_options_974_ = crate::leanh::lean_ctor_get(v___y_966_, 2);
    crate::leanh::lean_inc_ref(v_options_974_);
    crate::leanh::lean_inc_ref(v_lctx_973_);
    v___x_975_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_975_, 0, v_env_970_);
    crate::leanh::lean_ctor_set(v___x_975_, 1, v_mctx_972_);
    crate::leanh::lean_ctor_set(v___x_975_, 2, v_lctx_973_);
    crate::leanh::lean_ctor_set(v___x_975_, 3, v_options_974_);
    v___x_976_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_976_, 0, v___x_975_);
    crate::leanh::lean_ctor_set(v___x_976_, 1, v_msgData_963_);
    v___x_977_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_977_, 0, v___x_976_);
    return v___x_977_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabChange_spec__0_spec__0___boxed(
    mut v_msgData_978_: *mut crate::leanh::LeanObject,
    mut v___y_979_: *mut crate::leanh::LeanObject,
    mut v___y_980_: *mut crate::leanh::LeanObject,
    mut v___y_981_: *mut crate::leanh::LeanObject,
    mut v___y_982_: *mut crate::leanh::LeanObject,
    mut v___y_983_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_984_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabChange_spec__0_spec__0(v_msgData_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_);
    crate::leanh::lean_dec(v___y_982_);
    crate::leanh::lean_dec_ref(v___y_981_);
    crate::leanh::lean_dec(v___y_980_);
    crate::leanh::lean_dec_ref(v___y_979_);
    return v_res_984_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_elabChange_spec__0___redArg(
    mut v_msg_985_: *mut crate::leanh::LeanObject,
    mut v___y_986_: *mut crate::leanh::LeanObject,
    mut v___y_987_: *mut crate::leanh::LeanObject,
    mut v___y_988_: *mut crate::leanh::LeanObject,
    mut v___y_989_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_996_: u8 = 0;
    let mut v___x_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1001_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_991_ = crate::leanh::lean_ctor_get(v___y_988_, 5);
                v___x_992_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabChange_spec__0_spec__0(v_msg_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_);
                v_a_993_ = crate::leanh::lean_ctor_get(v___x_992_, 0);
                v_isSharedCheck_1001_ = (!crate::leanh::lean_is_exclusive(v___x_992_)) as u8;
                if v_isSharedCheck_1001_ == 0 {
                    v___x_995_ = v___x_992_;
                    v_isShared_996_ = v_isSharedCheck_1001_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_993_);
                    crate::leanh::lean_dec(v___x_992_);
                    v___x_995_ = crate::leanh::lean_box(0);
                    v_isShared_996_ = v_isSharedCheck_1001_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_991_);
                v___x_997_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_997_, 0, v_ref_991_);
                crate::leanh::lean_ctor_set(v___x_997_, 1, v_a_993_);
                if v_isShared_996_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_995_, 1);
                    crate::leanh::lean_ctor_set(v___x_995_, 0, v___x_997_);
                    v___x_999_ = v___x_995_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1000_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1000_, 0, v___x_997_);
                    v___x_999_ = v_reuseFailAlloc_1000_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_999_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_elabChange_spec__0___redArg___boxed(
    mut v_msg_1002_: *mut crate::leanh::LeanObject,
    mut v___y_1003_: *mut crate::leanh::LeanObject,
    mut v___y_1004_: *mut crate::leanh::LeanObject,
    mut v___y_1005_: *mut crate::leanh::LeanObject,
    mut v___y_1006_: *mut crate::leanh::LeanObject,
    mut v___y_1007_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1008_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabChange_spec__0___redArg(
        v_msg_1002_,
        v___y_1003_,
        v___y_1004_,
        v___y_1005_,
        v___y_1006_,
    );
    crate::leanh::lean_dec(v___y_1006_);
    crate::leanh::lean_dec_ref(v___y_1005_);
    crate::leanh::lean_dec(v___y_1004_);
    crate::leanh::lean_dec_ref(v___y_1003_);
    return v_res_1008_;
}
pub unsafe fn l_Lean_Elab_Tactic_elabChange(
    mut v_e_1009_: *mut crate::leanh::LeanObject,
    mut v_p_1010_: *mut crate::leanh::LeanObject,
    mut v_mkDefeqError_1011_: *mut crate::leanh::LeanObject,
    mut v_a_1012_: *mut crate::leanh::LeanObject,
    mut v_a_1013_: *mut crate::leanh::LeanObject,
    mut v_a_1014_: *mut crate::leanh::LeanObject,
    mut v_a_1015_: *mut crate::leanh::LeanObject,
    mut v_a_1016_: *mut crate::leanh::LeanObject,
    mut v_a_1017_: *mut crate::leanh::LeanObject,
    mut v_a_1018_: *mut crate::leanh::LeanObject,
    mut v_a_1019_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1026_: u8 = 0;
    let mut v___x_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1030_: u8 = 0;
    let mut v___f_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: u8 = 0;
    let mut v___x_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_1036_: u8 = 0;
    let mut v_ctxApprox_1037_: u8 = 0;
    let mut v_quasiPatternApprox_1038_: u8 = 0;
    let mut v_constApprox_1039_: u8 = 0;
    let mut v_isDefEqStuckEx_1040_: u8 = 0;
    let mut v_unificationHints_1041_: u8 = 0;
    let mut v_proofIrrelevance_1042_: u8 = 0;
    let mut v_offsetCnstrs_1043_: u8 = 0;
    let mut v_transparency_1044_: u8 = 0;
    let mut v_etaStruct_1045_: u8 = 0;
    let mut v_univApprox_1046_: u8 = 0;
    let mut v_iota_1047_: u8 = 0;
    let mut v_beta_1048_: u8 = 0;
    let mut v_proj_1049_: u8 = 0;
    let mut v_zeta_1050_: u8 = 0;
    let mut v_zetaDelta_1051_: u8 = 0;
    let mut v_zetaUnused_1052_: u8 = 0;
    let mut v_zetaHave_1053_: u8 = 0;
    let mut v___x_1055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1056_: u8 = 0;
    let mut v_trackZetaDelta_1057_: u8 = 0;
    let mut v_zetaDeltaSet_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_1064_: u8 = 0;
    let mut v_inTypeClassResolution_1065_: u8 = 0;
    let mut v_cacheInferType_1066_: u8 = 0;
    let mut v___x_1067_: u8 = 0;
    let mut v___x_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: u64 = 0;
    let mut v___x_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: u8 = 0;
    let mut v___f_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1086_: u8 = 0;
    let mut v___x_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1090_: u8 = 0;
    let mut v___x_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1095_: u8 = 0;
    let mut v___x_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1099_: u8 = 0;
    let mut v_reuseFailAlloc_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1101_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_1009_);
                v___f_1031_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_Tactic_elabChange___lam__0___boxed as *mut core::ffi::c_void,
                    9,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_1031_, 0, v_e_1009_);
                crate::leanh::lean_closure_set(v___f_1031_, 1, v_p_1010_);
                v___x_1032_ = 0;
                v___x_1033_ = l_Lean_Elab_Tactic_runTermElab___redArg(
                    v___f_1031_,
                    v___x_1032_,
                    v_a_1012_,
                    v_a_1013_,
                    v_a_1014_,
                    v_a_1015_,
                    v_a_1016_,
                    v_a_1017_,
                    v_a_1018_,
                    v_a_1019_,
                );
                if crate::leanh::lean_obj_tag(v___x_1033_) == 0 {
                    v_a_1034_ = crate::leanh::lean_ctor_get(v___x_1033_, 0);
                    crate::leanh::lean_inc(v_a_1034_);
                    crate::leanh::lean_dec_ref_known(v___x_1033_, 1);
                    v___x_1035_ = l_Lean_Meta_Context_config(v_a_1016_);
                    v_foApprox_1036_ = crate::leanh::lean_ctor_get_uint8(v___x_1035_, 0 as u32);
                    v_ctxApprox_1037_ = crate::leanh::lean_ctor_get_uint8(v___x_1035_, 1 as u32);
                    v_quasiPatternApprox_1038_ =
                        crate::leanh::lean_ctor_get_uint8(v___x_1035_, 2 as u32);
                    v_constApprox_1039_ = crate::leanh::lean_ctor_get_uint8(v___x_1035_, 3 as u32);
                    v_isDefEqStuckEx_1040_ =
                        crate::leanh::lean_ctor_get_uint8(v___x_1035_, 4 as u32);
                    v_unificationHints_1041_ =
                        crate::leanh::lean_ctor_get_uint8(v___x_1035_, 5 as u32);
                    v_proofIrrelevance_1042_ =
                        crate::leanh::lean_ctor_get_uint8(v___x_1035_, 6 as u32);
                    v_offsetCnstrs_1043_ = crate::leanh::lean_ctor_get_uint8(v___x_1035_, 8 as u32);
                    v_transparency_1044_ = crate::leanh::lean_ctor_get_uint8(v___x_1035_, 9 as u32);
                    v_etaStruct_1045_ = crate::leanh::lean_ctor_get_uint8(v___x_1035_, 10 as u32);
                    v_univApprox_1046_ = crate::leanh::lean_ctor_get_uint8(v___x_1035_, 11 as u32);
                    v_iota_1047_ = crate::leanh::lean_ctor_get_uint8(v___x_1035_, 12 as u32);
                    v_beta_1048_ = crate::leanh::lean_ctor_get_uint8(v___x_1035_, 13 as u32);
                    v_proj_1049_ = crate::leanh::lean_ctor_get_uint8(v___x_1035_, 14 as u32);
                    v_zeta_1050_ = crate::leanh::lean_ctor_get_uint8(v___x_1035_, 15 as u32);
                    v_zetaDelta_1051_ = crate::leanh::lean_ctor_get_uint8(v___x_1035_, 16 as u32);
                    v_zetaUnused_1052_ = crate::leanh::lean_ctor_get_uint8(v___x_1035_, 17 as u32);
                    v_zetaHave_1053_ = crate::leanh::lean_ctor_get_uint8(v___x_1035_, 18 as u32);
                    v_isSharedCheck_1101_ = (!crate::leanh::lean_is_exclusive(v___x_1035_)) as u8;
                    if v_isSharedCheck_1101_ == 0 {
                        v___x_1055_ = v___x_1035_;
                        v_isShared_1056_ = v_isSharedCheck_1101_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_1035_);
                        v___x_1055_ = crate::leanh::lean_box(0);
                        v_isShared_1056_ = v_isSharedCheck_1101_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_mkDefeqError_1011_);
                    crate::leanh::lean_dec_ref(v_e_1009_);
                    return v___x_1033_;
                }
            }
            1 => {
                v_a_1023_ = crate::leanh::lean_ctor_get(v___y_1022_, 0);
                v_isSharedCheck_1030_ = (!crate::leanh::lean_is_exclusive(v___y_1022_)) as u8;
                if v_isSharedCheck_1030_ == 0 {
                    v___x_1025_ = v___y_1022_;
                    v_isShared_1026_ = v_isSharedCheck_1030_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1023_);
                    crate::leanh::lean_dec(v___y_1022_);
                    v___x_1025_ = crate::leanh::lean_box(0);
                    v_isShared_1026_ = v_isSharedCheck_1030_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_1026_ == 0 {
                    v___x_1028_ = v___x_1025_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1029_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_a_1023_);
                    v___x_1028_ = v_reuseFailAlloc_1029_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1028_;
            }
            4 => {
                v_trackZetaDelta_1057_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_1016_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_1058_ = crate::leanh::lean_ctor_get(v_a_1016_, 1);
                v_lctx_1059_ = crate::leanh::lean_ctor_get(v_a_1016_, 2);
                v_localInstances_1060_ = crate::leanh::lean_ctor_get(v_a_1016_, 3);
                v_defEqCtx_x3f_1061_ = crate::leanh::lean_ctor_get(v_a_1016_, 4);
                v_synthPendingDepth_1062_ = crate::leanh::lean_ctor_get(v_a_1016_, 5);
                v_canUnfold_x3f_1063_ = crate::leanh::lean_ctor_get(v_a_1016_, 6);
                v_univApprox_1064_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_1016_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_1065_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_1016_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_1066_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_1016_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_1067_ = 1;
                if v_isShared_1056_ == 0 {
                    v___x_1069_ = v___x_1055_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1100_ = crate::leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1100_,
                        0 as u32,
                        v_foApprox_1036_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1100_,
                        1 as u32,
                        v_ctxApprox_1037_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1100_,
                        2 as u32,
                        v_quasiPatternApprox_1038_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1100_,
                        3 as u32,
                        v_constApprox_1039_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1100_,
                        4 as u32,
                        v_isDefEqStuckEx_1040_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1100_,
                        5 as u32,
                        v_unificationHints_1041_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1100_,
                        6 as u32,
                        v_proofIrrelevance_1042_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1100_,
                        8 as u32,
                        v_offsetCnstrs_1043_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1100_,
                        9 as u32,
                        v_transparency_1044_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1100_,
                        10 as u32,
                        v_etaStruct_1045_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1100_,
                        11 as u32,
                        v_univApprox_1046_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1100_,
                        12 as u32,
                        v_iota_1047_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1100_,
                        13 as u32,
                        v_beta_1048_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1100_,
                        14 as u32,
                        v_proj_1049_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1100_,
                        15 as u32,
                        v_zeta_1050_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1100_,
                        16 as u32,
                        v_zetaDelta_1051_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1100_,
                        17 as u32,
                        v_zetaUnused_1052_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1100_,
                        18 as u32,
                        v_zetaHave_1053_,
                    );
                    v___x_1069_ = v_reuseFailAlloc_1100_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_ctor_set_uint8(v___x_1069_, 7 as u32, v___x_1067_);
                v___x_1070_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1069_);
                v___x_1071_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                crate::leanh::lean_ctor_set(v___x_1071_, 0, v___x_1069_);
                crate::leanh::lean_ctor_set_uint64(
                    v___x_1071_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1070_,
                );
                crate::leanh::lean_inc(v_canUnfold_x3f_1063_);
                crate::leanh::lean_inc(v_synthPendingDepth_1062_);
                crate::leanh::lean_inc(v_defEqCtx_x3f_1061_);
                crate::leanh::lean_inc_ref(v_localInstances_1060_);
                crate::leanh::lean_inc_ref(v_lctx_1059_);
                crate::leanh::lean_inc(v_zetaDeltaSet_1058_);
                v___x_1072_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                crate::leanh::lean_ctor_set(v___x_1072_, 0, v___x_1071_);
                crate::leanh::lean_ctor_set(v___x_1072_, 1, v_zetaDeltaSet_1058_);
                crate::leanh::lean_ctor_set(v___x_1072_, 2, v_lctx_1059_);
                crate::leanh::lean_ctor_set(v___x_1072_, 3, v_localInstances_1060_);
                crate::leanh::lean_ctor_set(v___x_1072_, 4, v_defEqCtx_x3f_1061_);
                crate::leanh::lean_ctor_set(v___x_1072_, 5, v_synthPendingDepth_1062_);
                crate::leanh::lean_ctor_set(v___x_1072_, 6, v_canUnfold_x3f_1063_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1072_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_1057_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1072_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_1064_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1072_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_1065_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1072_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_1066_,
                );
                crate::leanh::lean_inc_ref(v_e_1009_);
                crate::leanh::lean_inc(v_a_1034_);
                v___x_1073_ = l_Lean_Meta_isExprDefEq(
                    v_a_1034_,
                    v_e_1009_,
                    v___x_1072_,
                    v_a_1017_,
                    v_a_1018_,
                    v_a_1019_,
                );
                if crate::leanh::lean_obj_tag(v___x_1073_) == 0 {
                    v_a_1074_ = crate::leanh::lean_ctor_get(v___x_1073_, 0);
                    crate::leanh::lean_inc(v_a_1074_);
                    crate::leanh::lean_dec_ref_known(v___x_1073_, 1);
                    v___x_1075_ = (crate::leanh::lean_unbox(v_a_1074_) as u8);
                    crate::leanh::lean_dec(v_a_1074_);
                    if v___x_1075_ == 0 {
                        crate::leanh::lean_inc_ref(v_e_1009_);
                        crate::leanh::lean_inc(v_a_1034_);
                        v___f_1076_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Elab_Tactic_elabChange___lam__1___boxed
                                as *mut core::ffi::c_void,
                            8,
                            3,
                        );
                        crate::leanh::lean_closure_set(v___f_1076_, 0, v_a_1034_);
                        crate::leanh::lean_closure_set(v___f_1076_, 1, v_e_1009_);
                        crate::leanh::lean_closure_set(v___f_1076_, 2, v_mkDefeqError_1011_);
                        v___x_1077_ = crate::leanh::lean_unsigned_to_nat(2);
                        v___x_1078_ = lean_mk_empty_array_with_capacity(v___x_1077_);
                        v___x_1079_ = lean_array_push(v___x_1078_, v_a_1034_);
                        v___x_1080_ = lean_array_push(v___x_1079_, v_e_1009_);
                        v___x_1081_ = l_Lean_MessageData_ofLazyM(v___f_1076_, v___x_1080_);
                        v___x_1082_ =
                            l_Lean_throwError___at___00Lean_Elab_Tactic_elabChange_spec__0___redArg(
                                v___x_1081_,
                                v___x_1072_,
                                v_a_1017_,
                                v_a_1018_,
                                v_a_1019_,
                            );
                        crate::leanh::lean_dec_ref_known(v___x_1072_, 7);
                        v_a_1083_ = crate::leanh::lean_ctor_get(v___x_1082_, 0);
                        v_isSharedCheck_1090_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1082_)) as u8;
                        if v_isSharedCheck_1090_ == 0 {
                            v___x_1085_ = v___x_1082_;
                            v_isShared_1086_ = v_isSharedCheck_1090_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1083_);
                            crate::leanh::lean_dec(v___x_1082_);
                            v___x_1085_ = crate::leanh::lean_box(0);
                            v_isShared_1086_ = v_isSharedCheck_1090_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___x_1072_, 7);
                        crate::leanh::lean_dec_ref(v_mkDefeqError_1011_);
                        crate::leanh::lean_dec_ref(v_e_1009_);
                        v___x_1091_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabChange_spec__1___redArg(v_a_1034_, v_a_1017_);
                        v___y_1022_ = v___x_1091_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_1072_, 7);
                    crate::leanh::lean_dec(v_a_1034_);
                    crate::leanh::lean_dec_ref(v_mkDefeqError_1011_);
                    crate::leanh::lean_dec_ref(v_e_1009_);
                    v_a_1092_ = crate::leanh::lean_ctor_get(v___x_1073_, 0);
                    v_isSharedCheck_1099_ = (!crate::leanh::lean_is_exclusive(v___x_1073_)) as u8;
                    if v_isSharedCheck_1099_ == 0 {
                        v___x_1094_ = v___x_1073_;
                        v_isShared_1095_ = v_isSharedCheck_1099_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1092_);
                        crate::leanh::lean_dec(v___x_1073_);
                        v___x_1094_ = crate::leanh::lean_box(0);
                        v_isShared_1095_ = v_isSharedCheck_1099_;
                        state = 8;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_1086_ == 0 {
                    v___x_1088_ = v___x_1085_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1089_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_a_1083_);
                    v___x_1088_ = v_reuseFailAlloc_1089_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1088_;
            }
            8 => {
                if v_isShared_1095_ == 0 {
                    v___x_1097_ = v___x_1094_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1098_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_a_1092_);
                    v___x_1097_ = v_reuseFailAlloc_1098_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1097_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_elabChange___boxed(
    mut v_e_1102_: *mut crate::leanh::LeanObject,
    mut v_p_1103_: *mut crate::leanh::LeanObject,
    mut v_mkDefeqError_1104_: *mut crate::leanh::LeanObject,
    mut v_a_1105_: *mut crate::leanh::LeanObject,
    mut v_a_1106_: *mut crate::leanh::LeanObject,
    mut v_a_1107_: *mut crate::leanh::LeanObject,
    mut v_a_1108_: *mut crate::leanh::LeanObject,
    mut v_a_1109_: *mut crate::leanh::LeanObject,
    mut v_a_1110_: *mut crate::leanh::LeanObject,
    mut v_a_1111_: *mut crate::leanh::LeanObject,
    mut v_a_1112_: *mut crate::leanh::LeanObject,
    mut v_a_1113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1114_ = l_Lean_Elab_Tactic_elabChange(
        v_e_1102_,
        v_p_1103_,
        v_mkDefeqError_1104_,
        v_a_1105_,
        v_a_1106_,
        v_a_1107_,
        v_a_1108_,
        v_a_1109_,
        v_a_1110_,
        v_a_1111_,
        v_a_1112_,
    );
    crate::leanh::lean_dec(v_a_1112_);
    crate::leanh::lean_dec_ref(v_a_1111_);
    crate::leanh::lean_dec(v_a_1110_);
    crate::leanh::lean_dec_ref(v_a_1109_);
    crate::leanh::lean_dec(v_a_1108_);
    crate::leanh::lean_dec_ref(v_a_1107_);
    crate::leanh::lean_dec(v_a_1106_);
    crate::leanh::lean_dec_ref(v_a_1105_);
    return v_res_1114_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_elabChange_spec__0(
    mut v_00_u03b1_1115_: *mut crate::leanh::LeanObject,
    mut v_msg_1116_: *mut crate::leanh::LeanObject,
    mut v___y_1117_: *mut crate::leanh::LeanObject,
    mut v___y_1118_: *mut crate::leanh::LeanObject,
    mut v___y_1119_: *mut crate::leanh::LeanObject,
    mut v___y_1120_: *mut crate::leanh::LeanObject,
    mut v___y_1121_: *mut crate::leanh::LeanObject,
    mut v___y_1122_: *mut crate::leanh::LeanObject,
    mut v___y_1123_: *mut crate::leanh::LeanObject,
    mut v___y_1124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1126_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabChange_spec__0___redArg(
        v_msg_1116_,
        v___y_1121_,
        v___y_1122_,
        v___y_1123_,
        v___y_1124_,
    );
    return v___x_1126_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_elabChange_spec__0___boxed(
    mut v_00_u03b1_1127_: *mut crate::leanh::LeanObject,
    mut v_msg_1128_: *mut crate::leanh::LeanObject,
    mut v___y_1129_: *mut crate::leanh::LeanObject,
    mut v___y_1130_: *mut crate::leanh::LeanObject,
    mut v___y_1131_: *mut crate::leanh::LeanObject,
    mut v___y_1132_: *mut crate::leanh::LeanObject,
    mut v___y_1133_: *mut crate::leanh::LeanObject,
    mut v___y_1134_: *mut crate::leanh::LeanObject,
    mut v___y_1135_: *mut crate::leanh::LeanObject,
    mut v___y_1136_: *mut crate::leanh::LeanObject,
    mut v___y_1137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1138_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabChange_spec__0(
        v_00_u03b1_1127_,
        v_msg_1128_,
        v___y_1129_,
        v___y_1130_,
        v___y_1131_,
        v___y_1132_,
        v___y_1133_,
        v___y_1134_,
        v___y_1135_,
        v___y_1136_,
    );
    crate::leanh::lean_dec(v___y_1136_);
    crate::leanh::lean_dec_ref(v___y_1135_);
    crate::leanh::lean_dec(v___y_1134_);
    crate::leanh::lean_dec_ref(v___y_1133_);
    crate::leanh::lean_dec(v___y_1132_);
    crate::leanh::lean_dec_ref(v___y_1131_);
    crate::leanh::lean_dec(v___y_1130_);
    crate::leanh::lean_dec_ref(v___y_1129_);
    return v_res_1138_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalChange_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1139_ = crate::leanh::lean_box(0);
    v___x_1140_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_1141_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1141_, 0, v___x_1140_);
    crate::leanh::lean_ctor_set(v___x_1141_, 1, v___x_1139_);
    return v___x_1141_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalChange_spec__0___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1143_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalChange_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalChange_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalChange_spec__0___redArg___closed__0);
    v___x_1144_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1144_, 0, v___x_1143_);
    return v___x_1144_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalChange_spec__0___redArg___boxed(
    mut v___y_1145_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1146_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalChange_spec__0___redArg();
    return v_res_1146_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalChange_spec__0(
    mut v_00_u03b1_1147_: *mut crate::leanh::LeanObject,
    mut v___y_1148_: *mut crate::leanh::LeanObject,
    mut v___y_1149_: *mut crate::leanh::LeanObject,
    mut v___y_1150_: *mut crate::leanh::LeanObject,
    mut v___y_1151_: *mut crate::leanh::LeanObject,
    mut v___y_1152_: *mut crate::leanh::LeanObject,
    mut v___y_1153_: *mut crate::leanh::LeanObject,
    mut v___y_1154_: *mut crate::leanh::LeanObject,
    mut v___y_1155_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1157_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalChange_spec__0___redArg();
    return v___x_1157_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalChange_spec__0___boxed(
    mut v_00_u03b1_1158_: *mut crate::leanh::LeanObject,
    mut v___y_1159_: *mut crate::leanh::LeanObject,
    mut v___y_1160_: *mut crate::leanh::LeanObject,
    mut v___y_1161_: *mut crate::leanh::LeanObject,
    mut v___y_1162_: *mut crate::leanh::LeanObject,
    mut v___y_1163_: *mut crate::leanh::LeanObject,
    mut v___y_1164_: *mut crate::leanh::LeanObject,
    mut v___y_1165_: *mut crate::leanh::LeanObject,
    mut v___y_1166_: *mut crate::leanh::LeanObject,
    mut v___y_1167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1168_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalChange_spec__0(
        v_00_u03b1_1158_,
        v___y_1159_,
        v___y_1160_,
        v___y_1161_,
        v___y_1162_,
        v___y_1163_,
        v___y_1164_,
        v___y_1165_,
        v___y_1166_,
    );
    crate::leanh::lean_dec(v___y_1166_);
    crate::leanh::lean_dec_ref(v___y_1165_);
    crate::leanh::lean_dec(v___y_1164_);
    crate::leanh::lean_dec_ref(v___y_1163_);
    crate::leanh::lean_dec(v___y_1162_);
    crate::leanh::lean_dec_ref(v___y_1161_);
    crate::leanh::lean_dec(v___y_1160_);
    crate::leanh::lean_dec_ref(v___y_1159_);
    return v_res_1168_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_evalChange___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1170_ = l_Lean_Elab_Tactic_evalChange___lam__0___closed__0;
    v___x_1171_ = l_Lean_stringToMessageData(v___x_1170_);
    return v___x_1171_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalChange___lam__0(
    mut v_x_1172_: *mut crate::leanh::LeanObject,
    mut v___y_1173_: *mut crate::leanh::LeanObject,
    mut v___y_1174_: *mut crate::leanh::LeanObject,
    mut v___y_1175_: *mut crate::leanh::LeanObject,
    mut v___y_1176_: *mut crate::leanh::LeanObject,
    mut v___y_1177_: *mut crate::leanh::LeanObject,
    mut v___y_1178_: *mut crate::leanh::LeanObject,
    mut v___y_1179_: *mut crate::leanh::LeanObject,
    mut v___y_1180_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1182_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_evalChange___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_evalChange___lam__0___closed__1_once),
        _init_l_Lean_Elab_Tactic_evalChange___lam__0___closed__1,
    );
    v___x_1183_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabChange_spec__0___redArg(
        v___x_1182_,
        v___y_1177_,
        v___y_1178_,
        v___y_1179_,
        v___y_1180_,
    );
    return v___x_1183_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalChange___lam__0___boxed(
    mut v_x_1184_: *mut crate::leanh::LeanObject,
    mut v___y_1185_: *mut crate::leanh::LeanObject,
    mut v___y_1186_: *mut crate::leanh::LeanObject,
    mut v___y_1187_: *mut crate::leanh::LeanObject,
    mut v___y_1188_: *mut crate::leanh::LeanObject,
    mut v___y_1189_: *mut crate::leanh::LeanObject,
    mut v___y_1190_: *mut crate::leanh::LeanObject,
    mut v___y_1191_: *mut crate::leanh::LeanObject,
    mut v___y_1192_: *mut crate::leanh::LeanObject,
    mut v___y_1193_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1194_ = l_Lean_Elab_Tactic_evalChange___lam__0(
        v_x_1184_,
        v___y_1185_,
        v___y_1186_,
        v___y_1187_,
        v___y_1188_,
        v___y_1189_,
        v___y_1190_,
        v___y_1191_,
        v___y_1192_,
    );
    crate::leanh::lean_dec(v___y_1192_);
    crate::leanh::lean_dec_ref(v___y_1191_);
    crate::leanh::lean_dec(v___y_1190_);
    crate::leanh::lean_dec_ref(v___y_1189_);
    crate::leanh::lean_dec(v___y_1188_);
    crate::leanh::lean_dec_ref(v___y_1187_);
    crate::leanh::lean_dec(v___y_1186_);
    crate::leanh::lean_dec_ref(v___y_1185_);
    crate::leanh::lean_dec(v_x_1184_);
    return v_res_1194_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalChange___lam__1(
    mut v_fst_1195_: *mut crate::leanh::LeanObject,
    mut v_snd_1196_: *mut crate::leanh::LeanObject,
    mut v___y_1197_: *mut crate::leanh::LeanObject,
    mut v___y_1198_: *mut crate::leanh::LeanObject,
    mut v___y_1199_: *mut crate::leanh::LeanObject,
    mut v___y_1200_: *mut crate::leanh::LeanObject,
    mut v___y_1201_: *mut crate::leanh::LeanObject,
    mut v___y_1202_: *mut crate::leanh::LeanObject,
    mut v___y_1203_: *mut crate::leanh::LeanObject,
    mut v___y_1204_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1214_: u8 = 0;
    let mut v___x_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1219_: u8 = 0;
    let mut v_unused_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1224_: u8 = 0;
    let mut v___x_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1228_: u8 = 0;
    let mut v_a_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1232_: u8 = 0;
    let mut v___x_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1236_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1206_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v___y_1198_,
                    v___y_1201_,
                    v___y_1202_,
                    v___y_1203_,
                    v___y_1204_,
                );
                if crate::leanh::lean_obj_tag(v___x_1206_) == 0 {
                    v_a_1207_ = crate::leanh::lean_ctor_get(v___x_1206_, 0);
                    crate::leanh::lean_inc(v_a_1207_);
                    crate::leanh::lean_dec_ref_known(v___x_1206_, 1);
                    v___x_1208_ = l_Lean_MVarId_replaceTargetDefEq(
                        v_a_1207_,
                        v_fst_1195_,
                        v___y_1201_,
                        v___y_1202_,
                        v___y_1203_,
                        v___y_1204_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1208_) == 0 {
                        v_a_1209_ = crate::leanh::lean_ctor_get(v___x_1208_, 0);
                        crate::leanh::lean_inc(v_a_1209_);
                        crate::leanh::lean_dec_ref_known(v___x_1208_, 1);
                        v___x_1210_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1210_, 0, v_a_1209_);
                        crate::leanh::lean_ctor_set(v___x_1210_, 1, v_snd_1196_);
                        v___x_1211_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                            v___x_1210_,
                            v___y_1198_,
                            v___y_1201_,
                            v___y_1202_,
                            v___y_1203_,
                            v___y_1204_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1211_) == 0 {
                            v_isSharedCheck_1219_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1211_)) as u8;
                            if v_isSharedCheck_1219_ == 0 {
                                v_unused_1220_ = crate::leanh::lean_ctor_get(v___x_1211_, 0);
                                crate::leanh::lean_dec(v_unused_1220_);
                                v___x_1213_ = v___x_1211_;
                                v_isShared_1214_ = v_isSharedCheck_1219_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_1211_);
                                v___x_1213_ = crate::leanh::lean_box(0);
                                v_isShared_1214_ = v_isSharedCheck_1219_;
                                state = 1;
                                continue;
                            }
                        } else {
                            return v___x_1211_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_snd_1196_);
                        v_a_1221_ = crate::leanh::lean_ctor_get(v___x_1208_, 0);
                        v_isSharedCheck_1228_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1208_)) as u8;
                        if v_isSharedCheck_1228_ == 0 {
                            v___x_1223_ = v___x_1208_;
                            v_isShared_1224_ = v_isSharedCheck_1228_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1221_);
                            crate::leanh::lean_dec(v___x_1208_);
                            v___x_1223_ = crate::leanh::lean_box(0);
                            v_isShared_1224_ = v_isSharedCheck_1228_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_snd_1196_);
                    crate::leanh::lean_dec_ref(v_fst_1195_);
                    v_a_1229_ = crate::leanh::lean_ctor_get(v___x_1206_, 0);
                    v_isSharedCheck_1236_ = (!crate::leanh::lean_is_exclusive(v___x_1206_)) as u8;
                    if v_isSharedCheck_1236_ == 0 {
                        v___x_1231_ = v___x_1206_;
                        v_isShared_1232_ = v_isSharedCheck_1236_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1229_);
                        crate::leanh::lean_dec(v___x_1206_);
                        v___x_1231_ = crate::leanh::lean_box(0);
                        v_isShared_1232_ = v_isSharedCheck_1236_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1215_ = crate::leanh::lean_box(0);
                if v_isShared_1214_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1213_, 0, v___x_1215_);
                    v___x_1217_ = v___x_1213_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1218_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1218_, 0, v___x_1215_);
                    v___x_1217_ = v_reuseFailAlloc_1218_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1217_;
            }
            3 => {
                if v_isShared_1224_ == 0 {
                    v___x_1226_ = v___x_1223_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1227_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_a_1221_);
                    v___x_1226_ = v_reuseFailAlloc_1227_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1226_;
            }
            5 => {
                if v_isShared_1232_ == 0 {
                    v___x_1234_ = v___x_1231_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1235_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_a_1229_);
                    v___x_1234_ = v_reuseFailAlloc_1235_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1234_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalChange___lam__1___boxed(
    mut v_fst_1237_: *mut crate::leanh::LeanObject,
    mut v_snd_1238_: *mut crate::leanh::LeanObject,
    mut v___y_1239_: *mut crate::leanh::LeanObject,
    mut v___y_1240_: *mut crate::leanh::LeanObject,
    mut v___y_1241_: *mut crate::leanh::LeanObject,
    mut v___y_1242_: *mut crate::leanh::LeanObject,
    mut v___y_1243_: *mut crate::leanh::LeanObject,
    mut v___y_1244_: *mut crate::leanh::LeanObject,
    mut v___y_1245_: *mut crate::leanh::LeanObject,
    mut v___y_1246_: *mut crate::leanh::LeanObject,
    mut v___y_1247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1248_ = l_Lean_Elab_Tactic_evalChange___lam__1(
        v_fst_1237_,
        v_snd_1238_,
        v___y_1239_,
        v___y_1240_,
        v___y_1241_,
        v___y_1242_,
        v___y_1243_,
        v___y_1244_,
        v___y_1245_,
        v___y_1246_,
    );
    crate::leanh::lean_dec(v___y_1246_);
    crate::leanh::lean_dec_ref(v___y_1245_);
    crate::leanh::lean_dec(v___y_1244_);
    crate::leanh::lean_dec_ref(v___y_1243_);
    crate::leanh::lean_dec(v___y_1242_);
    crate::leanh::lean_dec_ref(v___y_1241_);
    crate::leanh::lean_dec(v___y_1240_);
    crate::leanh::lean_dec_ref(v___y_1239_);
    return v_res_1248_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalChange___lam__2(
    mut v_newType_1250_: *mut crate::leanh::LeanObject,
    mut v___x_1251_: *mut crate::leanh::LeanObject,
    mut v___y_1252_: *mut crate::leanh::LeanObject,
    mut v___y_1253_: *mut crate::leanh::LeanObject,
    mut v___y_1254_: *mut crate::leanh::LeanObject,
    mut v___y_1255_: *mut crate::leanh::LeanObject,
    mut v___y_1256_: *mut crate::leanh::LeanObject,
    mut v___y_1257_: *mut crate::leanh::LeanObject,
    mut v___y_1258_: *mut crate::leanh::LeanObject,
    mut v___y_1259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: u8 = 0;
    let mut v___x_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1278_: u8 = 0;
    let mut v___x_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1282_: u8 = 0;
    let mut v_a_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1286_: u8 = 0;
    let mut v___x_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1290_: u8 = 0;
    let mut v_a_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1294_: u8 = 0;
    let mut v___x_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1298_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1261_ = l_Lean_Elab_Tactic_getMainTarget(
                    v___y_1252_,
                    v___y_1253_,
                    v___y_1254_,
                    v___y_1255_,
                    v___y_1256_,
                    v___y_1257_,
                    v___y_1258_,
                    v___y_1259_,
                );
                if crate::leanh::lean_obj_tag(v___x_1261_) == 0 {
                    v_a_1262_ = crate::leanh::lean_ctor_get(v___x_1261_, 0);
                    crate::leanh::lean_inc(v_a_1262_);
                    crate::leanh::lean_dec_ref_known(v___x_1261_, 1);
                    v___x_1263_ = l_Lean_Elab_Tactic_getMainTag___redArg(
                        v___y_1253_,
                        v___y_1256_,
                        v___y_1257_,
                        v___y_1258_,
                        v___y_1259_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1263_) == 0 {
                        v_a_1264_ = crate::leanh::lean_ctor_get(v___x_1263_, 0);
                        crate::leanh::lean_inc(v_a_1264_);
                        crate::leanh::lean_dec_ref_known(v___x_1263_, 1);
                        v___x_1265_ = l_Lean_Elab_Tactic_evalChange___lam__2___closed__0;
                        v___x_1266_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Elab_Tactic_elabChange___boxed as *mut core::ffi::c_void,
                            12,
                            3,
                        );
                        crate::leanh::lean_closure_set(v___x_1266_, 0, v_a_1262_);
                        crate::leanh::lean_closure_set(v___x_1266_, 1, v_newType_1250_);
                        crate::leanh::lean_closure_set(v___x_1266_, 2, v___x_1265_);
                        v___x_1267_ = l_Lean_Name_mkStr1(v___x_1251_);
                        v___x_1268_ = 0;
                        v___x_1269_ = l_Lean_Elab_Tactic_withCollectingNewGoalsFrom(
                            v___x_1266_,
                            v_a_1264_,
                            v___x_1267_,
                            v___x_1268_,
                            v___y_1252_,
                            v___y_1253_,
                            v___y_1254_,
                            v___y_1255_,
                            v___y_1256_,
                            v___y_1257_,
                            v___y_1258_,
                            v___y_1259_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1269_) == 0 {
                            v_a_1270_ = crate::leanh::lean_ctor_get(v___x_1269_, 0);
                            crate::leanh::lean_inc(v_a_1270_);
                            crate::leanh::lean_dec_ref_known(v___x_1269_, 1);
                            v_fst_1271_ = crate::leanh::lean_ctor_get(v_a_1270_, 0);
                            crate::leanh::lean_inc(v_fst_1271_);
                            v_snd_1272_ = crate::leanh::lean_ctor_get(v_a_1270_, 1);
                            crate::leanh::lean_inc(v_snd_1272_);
                            crate::leanh::lean_dec(v_a_1270_);
                            v___f_1273_ = crate::leanh::lean_alloc_closure(
                                l_Lean_Elab_Tactic_evalChange___lam__1___boxed
                                    as *mut core::ffi::c_void,
                                11,
                                2,
                            );
                            crate::leanh::lean_closure_set(v___f_1273_, 0, v_fst_1271_);
                            crate::leanh::lean_closure_set(v___f_1273_, 1, v_snd_1272_);
                            v___x_1274_ = l_Lean_Elab_Tactic_withMainContext___redArg(
                                v___f_1273_,
                                v___y_1252_,
                                v___y_1253_,
                                v___y_1254_,
                                v___y_1255_,
                                v___y_1256_,
                                v___y_1257_,
                                v___y_1258_,
                                v___y_1259_,
                            );
                            return v___x_1274_;
                        } else {
                            v_a_1275_ = crate::leanh::lean_ctor_get(v___x_1269_, 0);
                            v_isSharedCheck_1282_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1269_)) as u8;
                            if v_isSharedCheck_1282_ == 0 {
                                v___x_1277_ = v___x_1269_;
                                v_isShared_1278_ = v_isSharedCheck_1282_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1275_);
                                crate::leanh::lean_dec(v___x_1269_);
                                v___x_1277_ = crate::leanh::lean_box(0);
                                v_isShared_1278_ = v_isSharedCheck_1282_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1262_);
                        crate::leanh::lean_dec_ref(v___x_1251_);
                        crate::leanh::lean_dec(v_newType_1250_);
                        v_a_1283_ = crate::leanh::lean_ctor_get(v___x_1263_, 0);
                        v_isSharedCheck_1290_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1263_)) as u8;
                        if v_isSharedCheck_1290_ == 0 {
                            v___x_1285_ = v___x_1263_;
                            v_isShared_1286_ = v_isSharedCheck_1290_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1283_);
                            crate::leanh::lean_dec(v___x_1263_);
                            v___x_1285_ = crate::leanh::lean_box(0);
                            v_isShared_1286_ = v_isSharedCheck_1290_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_1251_);
                    crate::leanh::lean_dec(v_newType_1250_);
                    v_a_1291_ = crate::leanh::lean_ctor_get(v___x_1261_, 0);
                    v_isSharedCheck_1298_ = (!crate::leanh::lean_is_exclusive(v___x_1261_)) as u8;
                    if v_isSharedCheck_1298_ == 0 {
                        v___x_1293_ = v___x_1261_;
                        v_isShared_1294_ = v_isSharedCheck_1298_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1291_);
                        crate::leanh::lean_dec(v___x_1261_);
                        v___x_1293_ = crate::leanh::lean_box(0);
                        v_isShared_1294_ = v_isSharedCheck_1298_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1278_ == 0 {
                    v___x_1280_ = v___x_1277_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1281_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1281_, 0, v_a_1275_);
                    v___x_1280_ = v_reuseFailAlloc_1281_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1280_;
            }
            3 => {
                if v_isShared_1286_ == 0 {
                    v___x_1288_ = v___x_1285_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1289_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_a_1283_);
                    v___x_1288_ = v_reuseFailAlloc_1289_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1288_;
            }
            5 => {
                if v_isShared_1294_ == 0 {
                    v___x_1296_ = v___x_1293_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1297_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_a_1291_);
                    v___x_1296_ = v_reuseFailAlloc_1297_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1296_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalChange___lam__2___boxed(
    mut v_newType_1299_: *mut crate::leanh::LeanObject,
    mut v___x_1300_: *mut crate::leanh::LeanObject,
    mut v___y_1301_: *mut crate::leanh::LeanObject,
    mut v___y_1302_: *mut crate::leanh::LeanObject,
    mut v___y_1303_: *mut crate::leanh::LeanObject,
    mut v___y_1304_: *mut crate::leanh::LeanObject,
    mut v___y_1305_: *mut crate::leanh::LeanObject,
    mut v___y_1306_: *mut crate::leanh::LeanObject,
    mut v___y_1307_: *mut crate::leanh::LeanObject,
    mut v___y_1308_: *mut crate::leanh::LeanObject,
    mut v___y_1309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1310_ = l_Lean_Elab_Tactic_evalChange___lam__2(
        v_newType_1299_,
        v___x_1300_,
        v___y_1301_,
        v___y_1302_,
        v___y_1303_,
        v___y_1304_,
        v___y_1305_,
        v___y_1306_,
        v___y_1307_,
        v___y_1308_,
    );
    crate::leanh::lean_dec(v___y_1308_);
    crate::leanh::lean_dec_ref(v___y_1307_);
    crate::leanh::lean_dec(v___y_1306_);
    crate::leanh::lean_dec_ref(v___y_1305_);
    crate::leanh::lean_dec(v___y_1304_);
    crate::leanh::lean_dec_ref(v___y_1303_);
    crate::leanh::lean_dec(v___y_1302_);
    crate::leanh::lean_dec_ref(v___y_1301_);
    return v_res_1310_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalChange___lam__3(
    mut v_h_1311_: *mut crate::leanh::LeanObject,
    mut v_fst_1312_: *mut crate::leanh::LeanObject,
    mut v___x_1313_: u8,
    mut v_snd_1314_: *mut crate::leanh::LeanObject,
    mut v___y_1315_: *mut crate::leanh::LeanObject,
    mut v___y_1316_: *mut crate::leanh::LeanObject,
    mut v___y_1317_: *mut crate::leanh::LeanObject,
    mut v___y_1318_: *mut crate::leanh::LeanObject,
    mut v___y_1319_: *mut crate::leanh::LeanObject,
    mut v___y_1320_: *mut crate::leanh::LeanObject,
    mut v___y_1321_: *mut crate::leanh::LeanObject,
    mut v___y_1322_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1332_: u8 = 0;
    let mut v___x_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1337_: u8 = 0;
    let mut v_unused_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1342_: u8 = 0;
    let mut v___x_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1346_: u8 = 0;
    let mut v_a_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1350_: u8 = 0;
    let mut v___x_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1354_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1324_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v___y_1316_,
                    v___y_1319_,
                    v___y_1320_,
                    v___y_1321_,
                    v___y_1322_,
                );
                if crate::leanh::lean_obj_tag(v___x_1324_) == 0 {
                    v_a_1325_ = crate::leanh::lean_ctor_get(v___x_1324_, 0);
                    crate::leanh::lean_inc(v_a_1325_);
                    crate::leanh::lean_dec_ref_known(v___x_1324_, 1);
                    v___x_1326_ = l_Lean_MVarId_changeLocalDecl(
                        v_a_1325_,
                        v_h_1311_,
                        v_fst_1312_,
                        v___x_1313_,
                        v___y_1319_,
                        v___y_1320_,
                        v___y_1321_,
                        v___y_1322_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1326_) == 0 {
                        v_a_1327_ = crate::leanh::lean_ctor_get(v___x_1326_, 0);
                        crate::leanh::lean_inc(v_a_1327_);
                        crate::leanh::lean_dec_ref_known(v___x_1326_, 1);
                        v___x_1328_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1328_, 0, v_a_1327_);
                        crate::leanh::lean_ctor_set(v___x_1328_, 1, v_snd_1314_);
                        v___x_1329_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                            v___x_1328_,
                            v___y_1316_,
                            v___y_1319_,
                            v___y_1320_,
                            v___y_1321_,
                            v___y_1322_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1329_) == 0 {
                            v_isSharedCheck_1337_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1329_)) as u8;
                            if v_isSharedCheck_1337_ == 0 {
                                v_unused_1338_ = crate::leanh::lean_ctor_get(v___x_1329_, 0);
                                crate::leanh::lean_dec(v_unused_1338_);
                                v___x_1331_ = v___x_1329_;
                                v_isShared_1332_ = v_isSharedCheck_1337_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_1329_);
                                v___x_1331_ = crate::leanh::lean_box(0);
                                v_isShared_1332_ = v_isSharedCheck_1337_;
                                state = 1;
                                continue;
                            }
                        } else {
                            return v___x_1329_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_snd_1314_);
                        v_a_1339_ = crate::leanh::lean_ctor_get(v___x_1326_, 0);
                        v_isSharedCheck_1346_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1326_)) as u8;
                        if v_isSharedCheck_1346_ == 0 {
                            v___x_1341_ = v___x_1326_;
                            v_isShared_1342_ = v_isSharedCheck_1346_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1339_);
                            crate::leanh::lean_dec(v___x_1326_);
                            v___x_1341_ = crate::leanh::lean_box(0);
                            v_isShared_1342_ = v_isSharedCheck_1346_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_snd_1314_);
                    crate::leanh::lean_dec_ref(v_fst_1312_);
                    crate::leanh::lean_dec(v_h_1311_);
                    v_a_1347_ = crate::leanh::lean_ctor_get(v___x_1324_, 0);
                    v_isSharedCheck_1354_ = (!crate::leanh::lean_is_exclusive(v___x_1324_)) as u8;
                    if v_isSharedCheck_1354_ == 0 {
                        v___x_1349_ = v___x_1324_;
                        v_isShared_1350_ = v_isSharedCheck_1354_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1347_);
                        crate::leanh::lean_dec(v___x_1324_);
                        v___x_1349_ = crate::leanh::lean_box(0);
                        v_isShared_1350_ = v_isSharedCheck_1354_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1333_ = crate::leanh::lean_box(0);
                if v_isShared_1332_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1331_, 0, v___x_1333_);
                    v___x_1335_ = v___x_1331_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1336_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1336_, 0, v___x_1333_);
                    v___x_1335_ = v_reuseFailAlloc_1336_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1335_;
            }
            3 => {
                if v_isShared_1342_ == 0 {
                    v___x_1344_ = v___x_1341_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1345_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1345_, 0, v_a_1339_);
                    v___x_1344_ = v_reuseFailAlloc_1345_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1344_;
            }
            5 => {
                if v_isShared_1350_ == 0 {
                    v___x_1352_ = v___x_1349_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1353_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1353_, 0, v_a_1347_);
                    v___x_1352_ = v_reuseFailAlloc_1353_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1352_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalChange___lam__3___boxed(
    mut v_h_1355_: *mut crate::leanh::LeanObject,
    mut v_fst_1356_: *mut crate::leanh::LeanObject,
    mut v___x_1357_: *mut crate::leanh::LeanObject,
    mut v_snd_1358_: *mut crate::leanh::LeanObject,
    mut v___y_1359_: *mut crate::leanh::LeanObject,
    mut v___y_1360_: *mut crate::leanh::LeanObject,
    mut v___y_1361_: *mut crate::leanh::LeanObject,
    mut v___y_1362_: *mut crate::leanh::LeanObject,
    mut v___y_1363_: *mut crate::leanh::LeanObject,
    mut v___y_1364_: *mut crate::leanh::LeanObject,
    mut v___y_1365_: *mut crate::leanh::LeanObject,
    mut v___y_1366_: *mut crate::leanh::LeanObject,
    mut v___y_1367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3893__boxed_1368_: u8 = 0;
    let mut v_res_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3893__boxed_1368_ = (crate::leanh::lean_unbox(v___x_1357_) as u8);
    v_res_1369_ = l_Lean_Elab_Tactic_evalChange___lam__3(
        v_h_1355_,
        v_fst_1356_,
        v___x_3893__boxed_1368_,
        v_snd_1358_,
        v___y_1359_,
        v___y_1360_,
        v___y_1361_,
        v___y_1362_,
        v___y_1363_,
        v___y_1364_,
        v___y_1365_,
        v___y_1366_,
    );
    crate::leanh::lean_dec(v___y_1366_);
    crate::leanh::lean_dec_ref(v___y_1365_);
    crate::leanh::lean_dec(v___y_1364_);
    crate::leanh::lean_dec_ref(v___y_1363_);
    crate::leanh::lean_dec(v___y_1362_);
    crate::leanh::lean_dec_ref(v___y_1361_);
    crate::leanh::lean_dec(v___y_1360_);
    crate::leanh::lean_dec_ref(v___y_1359_);
    return v_res_1369_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalChange___lam__4(
    mut v_newType_1370_: *mut crate::leanh::LeanObject,
    mut v___x_1371_: *mut crate::leanh::LeanObject,
    mut v___x_1372_: u8,
    mut v_h_1373_: *mut crate::leanh::LeanObject,
    mut v___y_1374_: *mut crate::leanh::LeanObject,
    mut v___y_1375_: *mut crate::leanh::LeanObject,
    mut v___y_1376_: *mut crate::leanh::LeanObject,
    mut v___y_1377_: *mut crate::leanh::LeanObject,
    mut v___y_1378_: *mut crate::leanh::LeanObject,
    mut v___y_1379_: *mut crate::leanh::LeanObject,
    mut v___y_1380_: *mut crate::leanh::LeanObject,
    mut v___y_1381_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: u8 = 0;
    let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1401_: u8 = 0;
    let mut v___x_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1405_: u8 = 0;
    let mut v_a_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1409_: u8 = 0;
    let mut v___x_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1413_: u8 = 0;
    let mut v_a_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1417_: u8 = 0;
    let mut v___x_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1421_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_h_1373_);
                v___x_1383_ = l_Lean_FVarId_getType___redArg(
                    v_h_1373_,
                    v___y_1378_,
                    v___y_1380_,
                    v___y_1381_,
                );
                if crate::leanh::lean_obj_tag(v___x_1383_) == 0 {
                    v_a_1384_ = crate::leanh::lean_ctor_get(v___x_1383_, 0);
                    crate::leanh::lean_inc(v_a_1384_);
                    crate::leanh::lean_dec_ref_known(v___x_1383_, 1);
                    v___x_1385_ = l_Lean_Elab_Tactic_getMainTag___redArg(
                        v___y_1375_,
                        v___y_1378_,
                        v___y_1379_,
                        v___y_1380_,
                        v___y_1381_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1385_) == 0 {
                        v_a_1386_ = crate::leanh::lean_ctor_get(v___x_1385_, 0);
                        crate::leanh::lean_inc(v_a_1386_);
                        crate::leanh::lean_dec_ref_known(v___x_1385_, 1);
                        v___x_1387_ = l_Lean_Elab_Tactic_evalChange___lam__2___closed__0;
                        v___x_1388_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Elab_Tactic_elabChange___boxed as *mut core::ffi::c_void,
                            12,
                            3,
                        );
                        crate::leanh::lean_closure_set(v___x_1388_, 0, v_a_1384_);
                        crate::leanh::lean_closure_set(v___x_1388_, 1, v_newType_1370_);
                        crate::leanh::lean_closure_set(v___x_1388_, 2, v___x_1387_);
                        v___x_1389_ = l_Lean_Name_mkStr1(v___x_1371_);
                        v___x_1390_ = 0;
                        v___x_1391_ = l_Lean_Elab_Tactic_withCollectingNewGoalsFrom(
                            v___x_1388_,
                            v_a_1386_,
                            v___x_1389_,
                            v___x_1390_,
                            v___y_1374_,
                            v___y_1375_,
                            v___y_1376_,
                            v___y_1377_,
                            v___y_1378_,
                            v___y_1379_,
                            v___y_1380_,
                            v___y_1381_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1391_) == 0 {
                            v_a_1392_ = crate::leanh::lean_ctor_get(v___x_1391_, 0);
                            crate::leanh::lean_inc(v_a_1392_);
                            crate::leanh::lean_dec_ref_known(v___x_1391_, 1);
                            v_fst_1393_ = crate::leanh::lean_ctor_get(v_a_1392_, 0);
                            crate::leanh::lean_inc(v_fst_1393_);
                            v_snd_1394_ = crate::leanh::lean_ctor_get(v_a_1392_, 1);
                            crate::leanh::lean_inc(v_snd_1394_);
                            crate::leanh::lean_dec(v_a_1392_);
                            v___x_1395_ = crate::leanh::lean_box((v___x_1372_) as usize);
                            v___f_1396_ = crate::leanh::lean_alloc_closure(
                                l_Lean_Elab_Tactic_evalChange___lam__3___boxed
                                    as *mut core::ffi::c_void,
                                13,
                                4,
                            );
                            crate::leanh::lean_closure_set(v___f_1396_, 0, v_h_1373_);
                            crate::leanh::lean_closure_set(v___f_1396_, 1, v_fst_1393_);
                            crate::leanh::lean_closure_set(v___f_1396_, 2, v___x_1395_);
                            crate::leanh::lean_closure_set(v___f_1396_, 3, v_snd_1394_);
                            v___x_1397_ = l_Lean_Elab_Tactic_withMainContext___redArg(
                                v___f_1396_,
                                v___y_1374_,
                                v___y_1375_,
                                v___y_1376_,
                                v___y_1377_,
                                v___y_1378_,
                                v___y_1379_,
                                v___y_1380_,
                                v___y_1381_,
                            );
                            return v___x_1397_;
                        } else {
                            crate::leanh::lean_dec(v_h_1373_);
                            v_a_1398_ = crate::leanh::lean_ctor_get(v___x_1391_, 0);
                            v_isSharedCheck_1405_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1391_)) as u8;
                            if v_isSharedCheck_1405_ == 0 {
                                v___x_1400_ = v___x_1391_;
                                v_isShared_1401_ = v_isSharedCheck_1405_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1398_);
                                crate::leanh::lean_dec(v___x_1391_);
                                v___x_1400_ = crate::leanh::lean_box(0);
                                v_isShared_1401_ = v_isSharedCheck_1405_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1384_);
                        crate::leanh::lean_dec(v_h_1373_);
                        crate::leanh::lean_dec_ref(v___x_1371_);
                        crate::leanh::lean_dec(v_newType_1370_);
                        v_a_1406_ = crate::leanh::lean_ctor_get(v___x_1385_, 0);
                        v_isSharedCheck_1413_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1385_)) as u8;
                        if v_isSharedCheck_1413_ == 0 {
                            v___x_1408_ = v___x_1385_;
                            v_isShared_1409_ = v_isSharedCheck_1413_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1406_);
                            crate::leanh::lean_dec(v___x_1385_);
                            v___x_1408_ = crate::leanh::lean_box(0);
                            v_isShared_1409_ = v_isSharedCheck_1413_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_h_1373_);
                    crate::leanh::lean_dec_ref(v___x_1371_);
                    crate::leanh::lean_dec(v_newType_1370_);
                    v_a_1414_ = crate::leanh::lean_ctor_get(v___x_1383_, 0);
                    v_isSharedCheck_1421_ = (!crate::leanh::lean_is_exclusive(v___x_1383_)) as u8;
                    if v_isSharedCheck_1421_ == 0 {
                        v___x_1416_ = v___x_1383_;
                        v_isShared_1417_ = v_isSharedCheck_1421_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1414_);
                        crate::leanh::lean_dec(v___x_1383_);
                        v___x_1416_ = crate::leanh::lean_box(0);
                        v_isShared_1417_ = v_isSharedCheck_1421_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1401_ == 0 {
                    v___x_1403_ = v___x_1400_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1404_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1404_, 0, v_a_1398_);
                    v___x_1403_ = v_reuseFailAlloc_1404_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1403_;
            }
            3 => {
                if v_isShared_1409_ == 0 {
                    v___x_1411_ = v___x_1408_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1412_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_a_1406_);
                    v___x_1411_ = v_reuseFailAlloc_1412_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1411_;
            }
            5 => {
                if v_isShared_1417_ == 0 {
                    v___x_1419_ = v___x_1416_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1420_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_a_1414_);
                    v___x_1419_ = v_reuseFailAlloc_1420_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1419_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalChange___lam__4___boxed(
    mut v_newType_1422_: *mut crate::leanh::LeanObject,
    mut v___x_1423_: *mut crate::leanh::LeanObject,
    mut v___x_1424_: *mut crate::leanh::LeanObject,
    mut v_h_1425_: *mut crate::leanh::LeanObject,
    mut v___y_1426_: *mut crate::leanh::LeanObject,
    mut v___y_1427_: *mut crate::leanh::LeanObject,
    mut v___y_1428_: *mut crate::leanh::LeanObject,
    mut v___y_1429_: *mut crate::leanh::LeanObject,
    mut v___y_1430_: *mut crate::leanh::LeanObject,
    mut v___y_1431_: *mut crate::leanh::LeanObject,
    mut v___y_1432_: *mut crate::leanh::LeanObject,
    mut v___y_1433_: *mut crate::leanh::LeanObject,
    mut v___y_1434_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3994__boxed_1435_: u8 = 0;
    let mut v_res_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3994__boxed_1435_ = (crate::leanh::lean_unbox(v___x_1424_) as u8);
    v_res_1436_ = l_Lean_Elab_Tactic_evalChange___lam__4(
        v_newType_1422_,
        v___x_1423_,
        v___x_3994__boxed_1435_,
        v_h_1425_,
        v___y_1426_,
        v___y_1427_,
        v___y_1428_,
        v___y_1429_,
        v___y_1430_,
        v___y_1431_,
        v___y_1432_,
        v___y_1433_,
    );
    crate::leanh::lean_dec(v___y_1433_);
    crate::leanh::lean_dec_ref(v___y_1432_);
    crate::leanh::lean_dec(v___y_1431_);
    crate::leanh::lean_dec_ref(v___y_1430_);
    crate::leanh::lean_dec(v___y_1429_);
    crate::leanh::lean_dec_ref(v___y_1428_);
    crate::leanh::lean_dec(v___y_1427_);
    crate::leanh::lean_dec_ref(v___y_1426_);
    return v_res_1436_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalChange(
    mut v_x_1453_: *mut crate::leanh::LeanObject,
    mut v_a_1454_: *mut crate::leanh::LeanObject,
    mut v_a_1455_: *mut crate::leanh::LeanObject,
    mut v_a_1456_: *mut crate::leanh::LeanObject,
    mut v_a_1457_: *mut crate::leanh::LeanObject,
    mut v_a_1458_: *mut crate::leanh::LeanObject,
    mut v_a_1459_: *mut crate::leanh::LeanObject,
    mut v_a_1460_: *mut crate::leanh::LeanObject,
    mut v_a_1461_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: u8 = 0;
    let mut v___x_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newType_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: u8 = 0;
    let mut v___x_1491_: u8 = 0;
    let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_loc_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: u8 = 0;
    let mut v___x_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1463_ = l_Lean_Elab_Tactic_evalChange___closed__3;
                v___x_1464_ = l_Lean_Elab_Tactic_evalChange___closed__4;
                crate::leanh::lean_inc(v_x_1453_);
                v___x_1465_ = l_Lean_Syntax_isOfKind(v_x_1453_, v___x_1464_);
                if v___x_1465_ == 0 {
                    crate::leanh::lean_dec(v_x_1453_);
                    v___x_1466_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalChange_spec__0___redArg();
                    return v___x_1466_;
                } else {
                    v___f_1467_ = l_Lean_Elab_Tactic_evalChange___closed__5;
                    v___x_1483_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_newType_1484_ = l_Lean_Syntax_getArg(v_x_1453_, v___x_1483_);
                    crate::leanh::lean_inc(v_newType_1484_);
                    v___f_1485_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Elab_Tactic_evalChange___lam__2___boxed as *mut core::ffi::c_void,
                        11,
                        2,
                    );
                    crate::leanh::lean_closure_set(v___f_1485_, 0, v_newType_1484_);
                    crate::leanh::lean_closure_set(v___f_1485_, 1, v___x_1463_);
                    v___x_1486_ = crate::leanh::lean_box((v___x_1465_) as usize);
                    v___f_1487_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Elab_Tactic_evalChange___lam__4___boxed as *mut core::ffi::c_void,
                        13,
                        3,
                    );
                    crate::leanh::lean_closure_set(v___f_1487_, 0, v_newType_1484_);
                    crate::leanh::lean_closure_set(v___f_1487_, 1, v___x_1463_);
                    crate::leanh::lean_closure_set(v___f_1487_, 2, v___x_1486_);
                    v___x_1488_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_1489_ = l_Lean_Syntax_getArg(v_x_1453_, v___x_1488_);
                    crate::leanh::lean_dec(v_x_1453_);
                    v___x_1490_ = l_Lean_Syntax_isNone(v___x_1489_);
                    if v___x_1490_ == 0 {
                        crate::leanh::lean_inc(v___x_1489_);
                        v___x_1491_ = l_Lean_Syntax_matchesNull(v___x_1489_, v___x_1483_);
                        if v___x_1491_ == 0 {
                            crate::leanh::lean_dec(v___x_1489_);
                            crate::leanh::lean_dec_ref(v___f_1487_);
                            crate::leanh::lean_dec_ref(v___f_1485_);
                            v___x_1492_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalChange_spec__0___redArg();
                            return v___x_1492_;
                        } else {
                            v___x_1493_ = crate::leanh::lean_unsigned_to_nat(0);
                            v_loc_1494_ = l_Lean_Syntax_getArg(v___x_1489_, v___x_1493_);
                            crate::leanh::lean_dec(v___x_1489_);
                            v___x_1495_ = l_Lean_Elab_Tactic_evalChange___closed__7;
                            crate::leanh::lean_inc(v_loc_1494_);
                            v___x_1496_ = l_Lean_Syntax_isOfKind(v_loc_1494_, v___x_1495_);
                            if v___x_1496_ == 0 {
                                crate::leanh::lean_dec(v_loc_1494_);
                                crate::leanh::lean_dec_ref(v___f_1487_);
                                crate::leanh::lean_dec_ref(v___f_1485_);
                                v___x_1497_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalChange_spec__0___redArg();
                                return v___x_1497_;
                            } else {
                                v___x_1498_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1498_, 0, v_loc_1494_);
                                v___y_1469_ = v_a_1460_;
                                v___y_1470_ = v_a_1456_;
                                v___y_1471_ = v_a_1458_;
                                v___y_1472_ = v_a_1455_;
                                v___y_1473_ = v___f_1487_;
                                v___y_1474_ = v_a_1459_;
                                v___y_1475_ = v_a_1457_;
                                v___y_1476_ = v_a_1461_;
                                v___y_1477_ = v_a_1454_;
                                v___y_1478_ = v___f_1485_;
                                v___y_1479_ = v___x_1498_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_1489_);
                        v___x_1499_ = crate::leanh::lean_box(0);
                        v___y_1469_ = v_a_1460_;
                        v___y_1470_ = v_a_1456_;
                        v___y_1471_ = v_a_1458_;
                        v___y_1472_ = v_a_1455_;
                        v___y_1473_ = v___f_1487_;
                        v___y_1474_ = v_a_1459_;
                        v___y_1475_ = v_a_1457_;
                        v___y_1476_ = v_a_1461_;
                        v___y_1477_ = v_a_1454_;
                        v___y_1478_ = v___f_1485_;
                        v___y_1479_ = v___x_1499_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1480_ = l_Lean_mkOptionalNode(v___y_1479_);
                v___x_1481_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_1480_);
                crate::leanh::lean_dec(v___x_1480_);
                v___x_1482_ = l_Lean_Elab_Tactic_withLocation(
                    v___x_1481_,
                    v___y_1473_,
                    v___y_1478_,
                    v___f_1467_,
                    v___y_1477_,
                    v___y_1472_,
                    v___y_1470_,
                    v___y_1475_,
                    v___y_1471_,
                    v___y_1474_,
                    v___y_1469_,
                    v___y_1476_,
                );
                crate::leanh::lean_dec(v___x_1481_);
                return v___x_1482_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalChange___boxed(
    mut v_x_1500_: *mut crate::leanh::LeanObject,
    mut v_a_1501_: *mut crate::leanh::LeanObject,
    mut v_a_1502_: *mut crate::leanh::LeanObject,
    mut v_a_1503_: *mut crate::leanh::LeanObject,
    mut v_a_1504_: *mut crate::leanh::LeanObject,
    mut v_a_1505_: *mut crate::leanh::LeanObject,
    mut v_a_1506_: *mut crate::leanh::LeanObject,
    mut v_a_1507_: *mut crate::leanh::LeanObject,
    mut v_a_1508_: *mut crate::leanh::LeanObject,
    mut v_a_1509_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1510_ = l_Lean_Elab_Tactic_evalChange(
        v_x_1500_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_,
        v_a_1508_,
    );
    crate::leanh::lean_dec(v_a_1508_);
    crate::leanh::lean_dec_ref(v_a_1507_);
    crate::leanh::lean_dec(v_a_1506_);
    crate::leanh::lean_dec_ref(v_a_1505_);
    crate::leanh::lean_dec(v_a_1504_);
    crate::leanh::lean_dec_ref(v_a_1503_);
    crate::leanh::lean_dec(v_a_1502_);
    crate::leanh::lean_dec_ref(v_a_1501_);
    return v_res_1510_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1519_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_1520_ = l_Lean_Elab_Tactic_evalChange___closed__4;
    v___x_1521_ = l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange__1___closed__2;
    v___x_1522_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_evalChange___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_1523_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1519_,
        v___x_1520_,
        v___x_1521_,
        v___x_1522_,
    );
    return v___x_1523_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange__1___boxed(
    mut v_a_1524_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1525_ = l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange__1();
    return v_res_1525_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange_docString__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1528_ = l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange__1___closed__2;
    v___x_1529_ = l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange_docString__3___closed__0;
    v___x_1530_ = l_Lean_addBuiltinDocString(v___x_1528_, v___x_1529_);
    return v___x_1530_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange_docString__3___boxed(
    mut v_a_1531_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1532_ = l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange_docString__3();
    return v_res_1532_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Change(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Replace(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Location(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Change_0__Lean_Elab_Tactic_evalChange___regBuiltin_Lean_Elab_Tactic_evalChange_docString__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Change(
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
pub unsafe fn initialize_Lean_Elab_Tactic_Change(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Replace(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Location(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Change(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Change(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Change(builtin);
}
