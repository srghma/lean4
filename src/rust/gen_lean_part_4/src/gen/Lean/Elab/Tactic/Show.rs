// Lean compiler output
// Module: Lean.Elab.Tactic.Show
// Imports: Lean.Elab.Tactic.Change
use crate::r#gen::Init::Data::List::Basic::{
    l_List_appendTR___redArg, l_List_isEmpty___redArg, l_List_reverseAux___redArg,
};
use crate::r#gen::Init::Prelude::{l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind};
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    l_Lean_Elab_Tactic_SavedState_restore___redArg, l_Lean_Elab_Tactic_getGoals___redArg,
    l_Lean_Elab_Tactic_saveState___redArg, l_Lean_Elab_Tactic_setGoals___redArg,
    l_Lean_Elab_Tactic_tacticElabAttribute, l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___redArg,
    l_Lean_Elab_Tactic_withoutRecover___redArg,
};
use crate::r#gen::Lean::Elab::Tactic::Change::{
    initialize_Lean_Elab_Tactic_Change, l_Lean_Elab_Tactic_elabChange___boxed,
    runtime_initialize_Lean_Elab_Tactic_Change,
};
use crate::r#gen::Lean::Elab::Tactic::ElabTerm::l_Lean_Elab_Tactic_withCollectingNewGoalsFrom;
use crate::r#gen::Lean::Exception::l_Lean_Exception_isInterrupt;
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Message::{l_Lean_indentExpr, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::Basic::l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp;
use crate::r#gen::Lean::Meta::Tactic::Replace::l_Lean_MVarId_replaceTargetDefEq;
use crate::r#gen::Lean::Meta::Tactic::Util::{l_Lean_MVarId_getTag, l_Lean_MVarId_getType};
pub static l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__0_value: leanh::LeanStringObject<30> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [39, 115, 104, 111, 119, 39, 32, 116, 97, 99, 116, 105, 99, 32, 102, 97, 105, 108, 101, 100, 44, 32, 112, 97, 116, 116, 101, 114, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__2_value: leanh::LeanStringObject<39> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 39, m_capacity: 39, m_length: 38, m_data: [10, 105, 115, 32, 110, 111, 116, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 97, 108, 108, 121, 32, 101, 113, 117, 97, 108, 32, 116, 111, 32, 116, 97, 114, 103, 101, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__0_value: leanh::LeanStringObject<93> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 93, m_capacity: 93, m_length: 92, m_data: [39, 115, 104, 111, 119, 39, 32, 116, 97, 99, 116, 105, 99, 32, 102, 97, 105, 108, 101, 100, 44, 32, 110, 111, 32, 103, 111, 97, 108, 115, 32, 117, 110, 105, 102, 121, 32, 119, 105, 116, 104, 32, 116, 104, 101, 32, 103, 105, 118, 101, 110, 32, 112, 97, 116, 116, 101, 114, 110, 46, 10, 10, 73, 110, 32, 116, 104, 101, 32, 102, 105, 114, 115, 116, 32, 103, 111, 97, 108, 44, 32, 116, 104, 101, 32, 112, 97, 116, 116, 101, 114, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__2_value: leanh::LeanStringObject<43> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 43, m_capacity: 43, m_length: 42, m_data: [10, 105, 115, 32, 110, 111, 116, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 97, 108, 108, 121, 32, 101, 113, 117, 97, 108, 32, 116, 111, 32, 116, 104, 101, 32, 116, 97, 114, 103, 101, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__4_value: leanh::LeanStringObject<34> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [10, 40, 69, 114, 114, 111, 114, 115, 32, 102, 111, 114, 32, 111, 116, 104, 101, 114, 32, 103, 111, 97, 108, 115, 32, 111, 109, 105, 116, 116, 101, 100, 41, 0]};
static mut l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__4_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 104, 111, 119, 0]};
static mut l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___closed__0_value) as *mut leanh::LeanObject,3987080461608668766 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___closed__1_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_go___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___boxed
        as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_go___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_go___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_go___closed__1_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___boxed
        as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_go___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_go___closed__1_value
) as *mut leanh::LeanObject;
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalShow_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalShow_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_evalShow___closed__0_value: leanh::LeanStringObject<5> =
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
static mut l_Lean_Elab_Tactic_evalShow___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalShow___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_evalShow___closed__1_value: leanh::LeanStringObject<7> =
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
        m_data: [80, 97, 114, 115, 101, 114, 0],
    };
static mut l_Lean_Elab_Tactic_evalShow___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalShow___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_evalShow___closed__2_value: leanh::LeanStringObject<7> =
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
        m_data: [84, 97, 99, 116, 105, 99, 0],
    };
static mut l_Lean_Elab_Tactic_evalShow___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalShow___closed__2_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_evalShow___closed__3_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalShow___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_evalShow___closed__3_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalShow___closed__3_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalShow___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_evalShow___closed__3_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalShow___closed__3_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalShow___closed__2_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_evalShow___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_evalShow___closed__3_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___closed__0_value) as *mut leanh::LeanObject,4563519173115679639 as *mut leanh::LeanObject] };
static mut l_Lean_Elab_Tactic_evalShow___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalShow___closed__3_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__1_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [101, 118, 97, 108, 83, 104, 111, 119, 0]};
static mut l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__1_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalShow___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__2_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__0_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__2_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__2_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalShow___closed__2_value) as *mut leanh::LeanObject,12733524109236233889 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__2_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__1_value) as *mut leanh::LeanObject,14579851650025421784 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__2_value) as *mut leanh::LeanObject;
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_486_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_485_ = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__0;
    v___x_486_ = l_Lean_stringToMessageData(v___x_485_);
    return v___x_486_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_489_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_488_ = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__2;
    v___x_489_ = l_Lean_stringToMessageData(v___x_488_);
    return v___x_489_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg(
    mut v_p_490_: *mut leanh::LeanObject,
    mut v_tgt_491_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_500_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_493_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__1_once), _init_l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__1);
    v___x_494_ = l_Lean_indentExpr(v_p_490_);
    v___x_495_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_495_, 0, v___x_493_);
    leanh::lean_ctor_set(v___x_495_, 1, v___x_494_);
    v___x_496_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__3_once), _init_l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__3);
    v___x_497_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_497_, 0, v___x_495_);
    leanh::lean_ctor_set(v___x_497_, 1, v___x_496_);
    v___x_498_ = l_Lean_indentExpr(v_tgt_491_);
    v___x_499_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_499_, 0, v___x_497_);
    leanh::lean_ctor_set(v___x_499_, 1, v___x_498_);
    v___x_500_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_500_, 0, v___x_499_);
    return v___x_500_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___boxed(
    mut v_p_501_: *mut leanh::LeanObject,
    mut v_tgt_502_: *mut leanh::LeanObject,
    mut v_a_503_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_504_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_504_ =
        l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg(
            v_p_501_, v_tgt_502_,
        );
    return v_res_504_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError(
    mut v_p_505_: *mut leanh::LeanObject,
    mut v_tgt_506_: *mut leanh::LeanObject,
    mut v_a_507_: *mut leanh::LeanObject,
    mut v_a_508_: *mut leanh::LeanObject,
    mut v_a_509_: *mut leanh::LeanObject,
    mut v_a_510_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_512_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_512_ =
        l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg(
            v_p_505_, v_tgt_506_,
        );
    return v___x_512_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___boxed(
    mut v_p_513_: *mut leanh::LeanObject,
    mut v_tgt_514_: *mut leanh::LeanObject,
    mut v_a_515_: *mut leanh::LeanObject,
    mut v_a_516_: *mut leanh::LeanObject,
    mut v_a_517_: *mut leanh::LeanObject,
    mut v_a_518_: *mut leanh::LeanObject,
    mut v_a_519_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_520_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_520_ = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError(
        v_p_513_, v_tgt_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_,
    );
    leanh::lean_dec(v_a_518_);
    leanh::lean_dec_ref(v_a_517_);
    leanh::lean_dec(v_a_516_);
    leanh::lean_dec_ref(v_a_515_);
    return v_res_520_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_523_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_522_ = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__0;
    v___x_523_ = l_Lean_stringToMessageData(v___x_522_);
    return v___x_523_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_526_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_525_ = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__2;
    v___x_526_ = l_Lean_stringToMessageData(v___x_525_);
    return v___x_526_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_529_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_528_ = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__4;
    v___x_529_ = l_Lean_stringToMessageData(v___x_528_);
    return v___x_529_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg(
    mut v_p_530_: *mut leanh::LeanObject,
    mut v_tgt_531_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_542_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_533_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__1_once), _init_l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__1);
    v___x_534_ = l_Lean_indentExpr(v_p_530_);
    v___x_535_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_535_, 0, v___x_533_);
    leanh::lean_ctor_set(v___x_535_, 1, v___x_534_);
    v___x_536_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__3_once), _init_l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__3);
    v___x_537_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_537_, 0, v___x_535_);
    leanh::lean_ctor_set(v___x_537_, 1, v___x_536_);
    v___x_538_ = l_Lean_indentExpr(v_tgt_531_);
    v___x_539_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_539_, 0, v___x_537_);
    leanh::lean_ctor_set(v___x_539_, 1, v___x_538_);
    v___x_540_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__5_once), _init_l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__5);
    v___x_541_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_541_, 0, v___x_539_);
    leanh::lean_ctor_set(v___x_541_, 1, v___x_540_);
    v___x_542_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_542_, 0, v___x_541_);
    return v___x_542_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___boxed(
    mut v_p_543_: *mut leanh::LeanObject,
    mut v_tgt_544_: *mut leanh::LeanObject,
    mut v_a_545_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_546_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_546_ = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg(
        v_p_543_, v_tgt_544_,
    );
    return v_res_546_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError(
    mut v_p_547_: *mut leanh::LeanObject,
    mut v_tgt_548_: *mut leanh::LeanObject,
    mut v_a_549_: *mut leanh::LeanObject,
    mut v_a_550_: *mut leanh::LeanObject,
    mut v_a_551_: *mut leanh::LeanObject,
    mut v_a_552_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_554_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_554_ = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg(
        v_p_547_, v_tgt_548_,
    );
    return v___x_554_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___boxed(
    mut v_p_555_: *mut leanh::LeanObject,
    mut v_tgt_556_: *mut leanh::LeanObject,
    mut v_a_557_: *mut leanh::LeanObject,
    mut v_a_558_: *mut leanh::LeanObject,
    mut v_a_559_: *mut leanh::LeanObject,
    mut v_a_560_: *mut leanh::LeanObject,
    mut v_a_561_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_562_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_562_ = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError(
        v_p_555_, v_tgt_556_, v_a_557_, v_a_558_, v_a_559_, v_a_560_,
    );
    leanh::lean_dec(v_a_560_);
    leanh::lean_dec_ref(v_a_559_);
    leanh::lean_dec(v_a_558_);
    leanh::lean_dec_ref(v_a_557_);
    return v_res_562_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal_spec__0___redArg___lam__0(
    mut v_x_563_: *mut leanh::LeanObject,
    mut v___y_564_: *mut leanh::LeanObject,
    mut v___y_565_: *mut leanh::LeanObject,
    mut v___y_566_: *mut leanh::LeanObject,
    mut v___y_567_: *mut leanh::LeanObject,
    mut v___y_568_: *mut leanh::LeanObject,
    mut v___y_569_: *mut leanh::LeanObject,
    mut v___y_570_: *mut leanh::LeanObject,
    mut v___y_571_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_573_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_567_);
    leanh::lean_inc_ref(v___y_566_);
    leanh::lean_inc(v___y_565_);
    leanh::lean_inc_ref(v___y_564_);
    v___x_573_ = leanh::lean_apply_9(
        v_x_563_,
        v___y_564_,
        v___y_565_,
        v___y_566_,
        v___y_567_,
        v___y_568_,
        v___y_569_,
        v___y_570_,
        v___y_571_,
        leanh::lean_box(0),
    );
    return v___x_573_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal_spec__0___redArg___lam__0___boxed(
    mut v_x_574_: *mut leanh::LeanObject,
    mut v___y_575_: *mut leanh::LeanObject,
    mut v___y_576_: *mut leanh::LeanObject,
    mut v___y_577_: *mut leanh::LeanObject,
    mut v___y_578_: *mut leanh::LeanObject,
    mut v___y_579_: *mut leanh::LeanObject,
    mut v___y_580_: *mut leanh::LeanObject,
    mut v___y_581_: *mut leanh::LeanObject,
    mut v___y_582_: *mut leanh::LeanObject,
    mut v___y_583_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_584_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_584_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal_spec__0___redArg___lam__0(v_x_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_);
    leanh::lean_dec(v___y_578_);
    leanh::lean_dec_ref(v___y_577_);
    leanh::lean_dec(v___y_576_);
    leanh::lean_dec_ref(v___y_575_);
    return v_res_584_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal_spec__0___redArg(
    mut v_mvarId_585_: *mut leanh::LeanObject,
    mut v_x_586_: *mut leanh::LeanObject,
    mut v___y_587_: *mut leanh::LeanObject,
    mut v___y_588_: *mut leanh::LeanObject,
    mut v___y_589_: *mut leanh::LeanObject,
    mut v___y_590_: *mut leanh::LeanObject,
    mut v___y_591_: *mut leanh::LeanObject,
    mut v___y_592_: *mut leanh::LeanObject,
    mut v___y_593_: *mut leanh::LeanObject,
    mut v___y_594_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_601_: u8 = 0;
    let mut v___x_603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_605_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_590_);
                leanh::lean_inc_ref(v___y_589_);
                leanh::lean_inc(v___y_588_);
                leanh::lean_inc_ref(v___y_587_);
                v___f_596_ = leanh::lean_alloc_closure(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 5);
                leanh::lean_closure_set(v___f_596_, 0, v_x_586_);
                leanh::lean_closure_set(v___f_596_, 1, v___y_587_);
                leanh::lean_closure_set(v___f_596_, 2, v___y_588_);
                leanh::lean_closure_set(v___f_596_, 3, v___y_589_);
                leanh::lean_closure_set(v___f_596_, 4, v___y_590_);
                v___x_597_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    leanh::lean_box(0),
                    v_mvarId_585_,
                    v___f_596_,
                    v___y_591_,
                    v___y_592_,
                    v___y_593_,
                    v___y_594_,
                );
                if leanh::lean_obj_tag(v___x_597_) == 0 {
                    return v___x_597_;
                } else {
                    v_a_598_ = leanh::lean_ctor_get(v___x_597_, 0);
                    v_isSharedCheck_605_ = (!leanh::lean_is_exclusive(v___x_597_)) as u8;
                    if v_isSharedCheck_605_ == 0 {
                        v___x_600_ = v___x_597_;
                        v_isShared_601_ = v_isSharedCheck_605_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_598_);
                        leanh::lean_dec(v___x_597_);
                        v___x_600_ = leanh::lean_box(0);
                        v_isShared_601_ = v_isSharedCheck_605_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_601_ == 0 {
                    v___x_603_ = v___x_600_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_604_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_604_, 0, v_a_598_);
                    v___x_603_ = v_reuseFailAlloc_604_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_603_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal_spec__0___redArg___boxed(
    mut v_mvarId_606_: *mut leanh::LeanObject,
    mut v_x_607_: *mut leanh::LeanObject,
    mut v___y_608_: *mut leanh::LeanObject,
    mut v___y_609_: *mut leanh::LeanObject,
    mut v___y_610_: *mut leanh::LeanObject,
    mut v___y_611_: *mut leanh::LeanObject,
    mut v___y_612_: *mut leanh::LeanObject,
    mut v___y_613_: *mut leanh::LeanObject,
    mut v___y_614_: *mut leanh::LeanObject,
    mut v___y_615_: *mut leanh::LeanObject,
    mut v___y_616_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_617_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_617_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal_spec__0___redArg(v_mvarId_606_, v_x_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
    leanh::lean_dec(v___y_615_);
    leanh::lean_dec_ref(v___y_614_);
    leanh::lean_dec(v___y_613_);
    leanh::lean_dec_ref(v___y_612_);
    leanh::lean_dec(v___y_611_);
    leanh::lean_dec_ref(v___y_610_);
    leanh::lean_dec(v___y_609_);
    leanh::lean_dec_ref(v___y_608_);
    return v_res_617_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal_spec__0(
    mut v_00_u03b1_618_: *mut leanh::LeanObject,
    mut v_mvarId_619_: *mut leanh::LeanObject,
    mut v_x_620_: *mut leanh::LeanObject,
    mut v___y_621_: *mut leanh::LeanObject,
    mut v___y_622_: *mut leanh::LeanObject,
    mut v___y_623_: *mut leanh::LeanObject,
    mut v___y_624_: *mut leanh::LeanObject,
    mut v___y_625_: *mut leanh::LeanObject,
    mut v___y_626_: *mut leanh::LeanObject,
    mut v___y_627_: *mut leanh::LeanObject,
    mut v___y_628_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_630_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_630_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal_spec__0___redArg(v_mvarId_619_, v_x_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_);
    return v___x_630_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal_spec__0___boxed(
    mut v_00_u03b1_631_: *mut leanh::LeanObject,
    mut v_mvarId_632_: *mut leanh::LeanObject,
    mut v_x_633_: *mut leanh::LeanObject,
    mut v___y_634_: *mut leanh::LeanObject,
    mut v___y_635_: *mut leanh::LeanObject,
    mut v___y_636_: *mut leanh::LeanObject,
    mut v___y_637_: *mut leanh::LeanObject,
    mut v___y_638_: *mut leanh::LeanObject,
    mut v___y_639_: *mut leanh::LeanObject,
    mut v___y_640_: *mut leanh::LeanObject,
    mut v___y_641_: *mut leanh::LeanObject,
    mut v___y_642_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_643_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_643_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal_spec__0(v_00_u03b1_631_, v_mvarId_632_, v_x_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
    leanh::lean_dec(v___y_641_);
    leanh::lean_dec_ref(v___y_640_);
    leanh::lean_dec(v___y_639_);
    leanh::lean_dec_ref(v___y_638_);
    leanh::lean_dec(v___y_637_);
    leanh::lean_dec_ref(v___y_636_);
    leanh::lean_dec(v___y_635_);
    leanh::lean_dec_ref(v___y_634_);
    return v_res_643_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___lam__0(
    mut v___x_644_: *mut leanh::LeanObject,
    mut v_a_645_: *mut leanh::LeanObject,
    mut v___x_646_: *mut leanh::LeanObject,
    mut v___x_647_: u8,
    mut v_goal_648_: *mut leanh::LeanObject,
    mut v_goals_649_: *mut leanh::LeanObject,
    mut v_prevRev_650_: *mut leanh::LeanObject,
    mut v___y_651_: *mut leanh::LeanObject,
    mut v___y_652_: *mut leanh::LeanObject,
    mut v___y_653_: *mut leanh::LeanObject,
    mut v___y_654_: *mut leanh::LeanObject,
    mut v___y_655_: *mut leanh::LeanObject,
    mut v___y_656_: *mut leanh::LeanObject,
    mut v___y_657_: *mut leanh::LeanObject,
    mut v___y_658_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_666_: u8 = 0;
    let mut v___x_667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_678_: u8 = 0;
    let mut v___x_680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_682_: u8 = 0;
    let mut v_isSharedCheck_683_: u8 = 0;
    let mut v_a_684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_687_: u8 = 0;
    let mut v___x_689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_691_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_660_ = l_Lean_Elab_Tactic_withCollectingNewGoalsFrom(
                    v___x_644_, v_a_645_, v___x_646_, v___x_647_, v___y_651_, v___y_652_,
                    v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_,
                );
                if leanh::lean_obj_tag(v___x_660_) == 0 {
                    v_a_661_ = leanh::lean_ctor_get(v___x_660_, 0);
                    leanh::lean_inc(v_a_661_);
                    leanh::lean_dec_ref_known(v___x_660_, 1);
                    v_fst_662_ = leanh::lean_ctor_get(v_a_661_, 0);
                    v_snd_663_ = leanh::lean_ctor_get(v_a_661_, 1);
                    v_isSharedCheck_683_ = (!leanh::lean_is_exclusive(v_a_661_)) as u8;
                    if v_isSharedCheck_683_ == 0 {
                        v___x_665_ = v_a_661_;
                        v_isShared_666_ = v_isSharedCheck_683_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_663_);
                        leanh::lean_inc(v_fst_662_);
                        leanh::lean_dec(v_a_661_);
                        v___x_665_ = leanh::lean_box(0);
                        v_isShared_666_ = v_isSharedCheck_683_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_prevRev_650_);
                    leanh::lean_dec(v_goals_649_);
                    leanh::lean_dec(v_goal_648_);
                    v_a_684_ = leanh::lean_ctor_get(v___x_660_, 0);
                    v_isSharedCheck_691_ = (!leanh::lean_is_exclusive(v___x_660_)) as u8;
                    if v_isSharedCheck_691_ == 0 {
                        v___x_686_ = v___x_660_;
                        v_isShared_687_ = v_isSharedCheck_691_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_684_);
                        leanh::lean_dec(v___x_660_);
                        v___x_686_ = leanh::lean_box(0);
                        v_isShared_687_ = v_isSharedCheck_691_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_667_ = l_Lean_MVarId_replaceTargetDefEq(
                    v_goal_648_,
                    v_fst_662_,
                    v___y_655_,
                    v___y_656_,
                    v___y_657_,
                    v___y_658_,
                );
                if leanh::lean_obj_tag(v___x_667_) == 0 {
                    v_a_668_ = leanh::lean_ctor_get(v___x_667_, 0);
                    leanh::lean_inc(v_a_668_);
                    leanh::lean_dec_ref_known(v___x_667_, 1);
                    v___x_669_ = l_List_appendTR___redArg(v_snd_663_, v_goals_649_);
                    v___x_670_ = l_List_reverseAux___redArg(v_prevRev_650_, v___x_669_);
                    if v_isShared_666_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_665_, 1);
                        leanh::lean_ctor_set(v___x_665_, 1, v___x_670_);
                        leanh::lean_ctor_set(v___x_665_, 0, v_a_668_);
                        v___x_672_ = v___x_665_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_674_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_674_, 0, v_a_668_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_674_, 1, v___x_670_);
                        v___x_672_ = v_reuseFailAlloc_674_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_665_);
                    leanh::lean_dec(v_snd_663_);
                    leanh::lean_dec(v_prevRev_650_);
                    leanh::lean_dec(v_goals_649_);
                    v_a_675_ = leanh::lean_ctor_get(v___x_667_, 0);
                    v_isSharedCheck_682_ = (!leanh::lean_is_exclusive(v___x_667_)) as u8;
                    if v_isSharedCheck_682_ == 0 {
                        v___x_677_ = v___x_667_;
                        v_isShared_678_ = v_isSharedCheck_682_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_675_);
                        leanh::lean_dec(v___x_667_);
                        v___x_677_ = leanh::lean_box(0);
                        v_isShared_678_ = v_isSharedCheck_682_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_673_ = l_Lean_Elab_Tactic_setGoals___redArg(v___x_672_, v___y_652_);
                return v___x_673_;
            }
            3 => {
                if v_isShared_678_ == 0 {
                    v___x_680_ = v___x_677_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_681_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_681_, 0, v_a_675_);
                    v___x_680_ = v_reuseFailAlloc_681_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_680_;
            }
            5 => {
                if v_isShared_687_ == 0 {
                    v___x_689_ = v___x_686_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_690_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_690_, 0, v_a_684_);
                    v___x_689_ = v_reuseFailAlloc_690_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_689_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___lam__0___boxed(
    mut v___x_692_: *mut leanh::LeanObject,
    mut v_a_693_: *mut leanh::LeanObject,
    mut v___x_694_: *mut leanh::LeanObject,
    mut v___x_695_: *mut leanh::LeanObject,
    mut v_goal_696_: *mut leanh::LeanObject,
    mut v_goals_697_: *mut leanh::LeanObject,
    mut v_prevRev_698_: *mut leanh::LeanObject,
    mut v___y_699_: *mut leanh::LeanObject,
    mut v___y_700_: *mut leanh::LeanObject,
    mut v___y_701_: *mut leanh::LeanObject,
    mut v___y_702_: *mut leanh::LeanObject,
    mut v___y_703_: *mut leanh::LeanObject,
    mut v___y_704_: *mut leanh::LeanObject,
    mut v___y_705_: *mut leanh::LeanObject,
    mut v___y_706_: *mut leanh::LeanObject,
    mut v___y_707_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2263__boxed_708_: u8 = 0;
    let mut v_res_709_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2263__boxed_708_ = (leanh::lean_unbox(v___x_695_) as u8);
    v_res_709_ = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___lam__0(
        v___x_692_,
        v_a_693_,
        v___x_694_,
        v___x_2263__boxed_708_,
        v_goal_696_,
        v_goals_697_,
        v_prevRev_698_,
        v___y_699_,
        v___y_700_,
        v___y_701_,
        v___y_702_,
        v___y_703_,
        v___y_704_,
        v___y_705_,
        v___y_706_,
    );
    leanh::lean_dec(v___y_706_);
    leanh::lean_dec_ref(v___y_705_);
    leanh::lean_dec(v___y_704_);
    leanh::lean_dec_ref(v___y_703_);
    leanh::lean_dec(v___y_702_);
    leanh::lean_dec_ref(v___y_701_);
    leanh::lean_dec(v___y_700_);
    leanh::lean_dec_ref(v___y_699_);
    return v_res_709_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal(
    mut v_newType_713_: *mut leanh::LeanObject,
    mut v_goal_714_: *mut leanh::LeanObject,
    mut v_goals_715_: *mut leanh::LeanObject,
    mut v_prevRev_716_: *mut leanh::LeanObject,
    mut v_err_717_: *mut leanh::LeanObject,
    mut v_a_718_: *mut leanh::LeanObject,
    mut v_a_719_: *mut leanh::LeanObject,
    mut v_a_720_: *mut leanh::LeanObject,
    mut v_a_721_: *mut leanh::LeanObject,
    mut v_a_722_: *mut leanh::LeanObject,
    mut v_a_723_: *mut leanh::LeanObject,
    mut v_a_724_: *mut leanh::LeanObject,
    mut v_a_725_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_733_: u8 = 0;
    let mut v___x_734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_740_: u8 = 0;
    let mut v___x_742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_744_: u8 = 0;
    let mut v_a_745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_748_: u8 = 0;
    let mut v___x_750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_752_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_goal_714_);
                v___x_727_ =
                    l_Lean_MVarId_getType(v_goal_714_, v_a_722_, v_a_723_, v_a_724_, v_a_725_);
                if leanh::lean_obj_tag(v___x_727_) == 0 {
                    v_a_728_ = leanh::lean_ctor_get(v___x_727_, 0);
                    leanh::lean_inc(v_a_728_);
                    leanh::lean_dec_ref_known(v___x_727_, 1);
                    leanh::lean_inc(v_goal_714_);
                    v___x_729_ =
                        l_Lean_MVarId_getTag(v_goal_714_, v_a_722_, v_a_723_, v_a_724_, v_a_725_);
                    if leanh::lean_obj_tag(v___x_729_) == 0 {
                        v_a_730_ = leanh::lean_ctor_get(v___x_729_, 0);
                        leanh::lean_inc(v_a_730_);
                        leanh::lean_dec_ref_known(v___x_729_, 1);
                        v___x_731_ = leanh::lean_alloc_closure(
                            l_Lean_Elab_Tactic_elabChange___boxed as *mut core::ffi::c_void,
                            12,
                            3,
                        );
                        leanh::lean_closure_set(v___x_731_, 0, v_a_728_);
                        leanh::lean_closure_set(v___x_731_, 1, v_newType_713_);
                        leanh::lean_closure_set(v___x_731_, 2, v_err_717_);
                        v___x_732_ = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___closed__1;
                        v___x_733_ = 0;
                        v___x_734_ = leanh::lean_box((v___x_733_) as usize);
                        leanh::lean_inc(v_goal_714_);
                        v___f_735_ = leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___lam__0___boxed as *mut core::ffi::c_void, 16, 7);
                        leanh::lean_closure_set(v___f_735_, 0, v___x_731_);
                        leanh::lean_closure_set(v___f_735_, 1, v_a_730_);
                        leanh::lean_closure_set(v___f_735_, 2, v___x_732_);
                        leanh::lean_closure_set(v___f_735_, 3, v___x_734_);
                        leanh::lean_closure_set(v___f_735_, 4, v_goal_714_);
                        leanh::lean_closure_set(v___f_735_, 5, v_goals_715_);
                        leanh::lean_closure_set(v___f_735_, 6, v_prevRev_716_);
                        v___x_736_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal_spec__0___redArg(v_goal_714_, v___f_735_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_);
                        return v___x_736_;
                    } else {
                        leanh::lean_dec(v_a_728_);
                        leanh::lean_dec_ref(v_err_717_);
                        leanh::lean_dec(v_prevRev_716_);
                        leanh::lean_dec(v_goals_715_);
                        leanh::lean_dec(v_goal_714_);
                        leanh::lean_dec(v_newType_713_);
                        v_a_737_ = leanh::lean_ctor_get(v___x_729_, 0);
                        v_isSharedCheck_744_ = (!leanh::lean_is_exclusive(v___x_729_)) as u8;
                        if v_isSharedCheck_744_ == 0 {
                            v___x_739_ = v___x_729_;
                            v_isShared_740_ = v_isSharedCheck_744_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_737_);
                            leanh::lean_dec(v___x_729_);
                            v___x_739_ = leanh::lean_box(0);
                            v_isShared_740_ = v_isSharedCheck_744_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_err_717_);
                    leanh::lean_dec(v_prevRev_716_);
                    leanh::lean_dec(v_goals_715_);
                    leanh::lean_dec(v_goal_714_);
                    leanh::lean_dec(v_newType_713_);
                    v_a_745_ = leanh::lean_ctor_get(v___x_727_, 0);
                    v_isSharedCheck_752_ = (!leanh::lean_is_exclusive(v___x_727_)) as u8;
                    if v_isSharedCheck_752_ == 0 {
                        v___x_747_ = v___x_727_;
                        v_isShared_748_ = v_isSharedCheck_752_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_745_);
                        leanh::lean_dec(v___x_727_);
                        v___x_747_ = leanh::lean_box(0);
                        v_isShared_748_ = v_isSharedCheck_752_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_740_ == 0 {
                    v___x_742_ = v___x_739_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_743_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_743_, 0, v_a_737_);
                    v___x_742_ = v_reuseFailAlloc_743_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_742_;
            }
            3 => {
                if v_isShared_748_ == 0 {
                    v___x_750_ = v___x_747_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_751_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_751_, 0, v_a_745_);
                    v___x_750_ = v_reuseFailAlloc_751_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_750_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___boxed(
    mut v_newType_753_: *mut leanh::LeanObject,
    mut v_goal_754_: *mut leanh::LeanObject,
    mut v_goals_755_: *mut leanh::LeanObject,
    mut v_prevRev_756_: *mut leanh::LeanObject,
    mut v_err_757_: *mut leanh::LeanObject,
    mut v_a_758_: *mut leanh::LeanObject,
    mut v_a_759_: *mut leanh::LeanObject,
    mut v_a_760_: *mut leanh::LeanObject,
    mut v_a_761_: *mut leanh::LeanObject,
    mut v_a_762_: *mut leanh::LeanObject,
    mut v_a_763_: *mut leanh::LeanObject,
    mut v_a_764_: *mut leanh::LeanObject,
    mut v_a_765_: *mut leanh::LeanObject,
    mut v_a_766_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_767_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_767_ = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal(
        v_newType_753_,
        v_goal_754_,
        v_goals_755_,
        v_prevRev_756_,
        v_err_757_,
        v_a_758_,
        v_a_759_,
        v_a_760_,
        v_a_761_,
        v_a_762_,
        v_a_763_,
        v_a_764_,
        v_a_765_,
    );
    leanh::lean_dec(v_a_765_);
    leanh::lean_dec_ref(v_a_764_);
    leanh::lean_dec(v_a_763_);
    leanh::lean_dec_ref(v_a_762_);
    leanh::lean_dec(v_a_761_);
    leanh::lean_dec_ref(v_a_760_);
    leanh::lean_dec(v_a_759_);
    leanh::lean_dec_ref(v_a_758_);
    return v_res_767_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_go(
    mut v_newType_770_: *mut leanh::LeanObject,
    mut v_firstGoal_771_: *mut leanh::LeanObject,
    mut v_goals_772_: *mut leanh::LeanObject,
    mut v_prevRev_773_: *mut leanh::LeanObject,
    mut v_a_774_: *mut leanh::LeanObject,
    mut v_a_775_: *mut leanh::LeanObject,
    mut v_a_776_: *mut leanh::LeanObject,
    mut v_a_777_: *mut leanh::LeanObject,
    mut v_a_778_: *mut leanh::LeanObject,
    mut v_a_779_: *mut leanh::LeanObject,
    mut v_a_780_: *mut leanh::LeanObject,
    mut v_a_781_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_793_: u8 = 0;
    let mut v___x_795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_797_: u8 = 0;
    let mut v_head_798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_802_: u8 = 0;
    let mut v___y_804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_805_: u8 = 0;
    let mut v___y_806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_807_: u8 = 0;
    let mut v___x_808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_814_: u8 = 0;
    let mut v___x_815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_821_: u8 = 0;
    let mut v___x_822_: u8 = 0;
    let mut v___x_823_: u8 = 0;
    let mut v_a_824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_827_: u8 = 0;
    let mut v___x_829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_831_: u8 = 0;
    let mut v___x_832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_834_: u8 = 0;
    let mut v___x_835_: u8 = 0;
    let mut v_recover_836_: u8 = 0;
    let mut v_isSharedCheck_837_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_goals_772_) == 0 {
                    leanh::lean_dec(v_prevRev_773_);
                    v___x_783_ = l_Lean_Elab_Tactic_getGoals___redArg(v_a_775_);
                    if leanh::lean_obj_tag(v___x_783_) == 0 {
                        v_a_784_ = leanh::lean_ctor_get(v___x_783_, 0);
                        leanh::lean_inc(v_a_784_);
                        leanh::lean_dec_ref_known(v___x_783_, 1);
                        if leanh::lean_obj_tag(v_a_784_) == 0 {
                            v___y_786_ = v_a_784_;
                            state = 1;
                            continue;
                        } else {
                            v_tail_789_ = leanh::lean_ctor_get(v_a_784_, 1);
                            leanh::lean_inc(v_tail_789_);
                            leanh::lean_dec_ref_known(v_a_784_, 2);
                            v___y_786_ = v_tail_789_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_firstGoal_771_);
                        leanh::lean_dec(v_newType_770_);
                        v_a_790_ = leanh::lean_ctor_get(v___x_783_, 0);
                        v_isSharedCheck_797_ = (!leanh::lean_is_exclusive(v___x_783_)) as u8;
                        if v_isSharedCheck_797_ == 0 {
                            v___x_792_ = v___x_783_;
                            v_isShared_793_ = v_isSharedCheck_797_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_790_);
                            leanh::lean_dec(v___x_783_);
                            v___x_792_ = leanh::lean_box(0);
                            v_isShared_793_ = v_isSharedCheck_797_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v_head_798_ = leanh::lean_ctor_get(v_goals_772_, 0);
                    v_tail_799_ = leanh::lean_ctor_get(v_goals_772_, 1);
                    v_isSharedCheck_837_ = (!leanh::lean_is_exclusive(v_goals_772_)) as u8;
                    if v_isSharedCheck_837_ == 0 {
                        v___x_801_ = v_goals_772_;
                        v_isShared_802_ = v_isSharedCheck_837_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_799_);
                        leanh::lean_inc(v_head_798_);
                        leanh::lean_dec(v_goals_772_);
                        v___x_801_ = leanh::lean_box(0);
                        v_isShared_802_ = v_isSharedCheck_837_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_787_ =
                    l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_go___closed__0;
                v___x_788_ = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal(
                    v_newType_770_,
                    v_firstGoal_771_,
                    v___y_786_,
                    v_goals_772_,
                    v___x_787_,
                    v_a_774_,
                    v_a_775_,
                    v_a_776_,
                    v_a_777_,
                    v_a_778_,
                    v_a_779_,
                    v_a_780_,
                    v_a_781_,
                );
                return v___x_788_;
            }
            2 => {
                if v_isShared_793_ == 0 {
                    v___x_795_ = v___x_792_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_796_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_796_, 0, v_a_790_);
                    v___x_795_ = v_reuseFailAlloc_796_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_795_;
            }
            4 => {
                v___x_834_ = l_List_isEmpty___redArg(v_tail_799_);
                if v___x_834_ == 0 {
                    v___y_814_ = v___x_834_;
                    state = 7;
                    continue;
                } else {
                    v___x_835_ = l_List_isEmpty___redArg(v_prevRev_773_);
                    if v___x_835_ == 0 {
                        v_recover_836_ = leanh::lean_ctor_get_uint8(
                            v_a_774_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        );
                        if v_recover_836_ == 0 {
                            v___y_814_ = v___x_834_;
                            state = 7;
                            continue;
                        } else {
                            v___y_814_ = v___x_835_;
                            state = 7;
                            continue;
                        }
                    } else {
                        v___y_814_ = v___x_835_;
                        state = 7;
                        continue;
                    }
                }
            }
            5 => {
                if v___y_807_ == 0 {
                    leanh::lean_dec_ref(v___y_804_);
                    v___x_808_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(
                        v___y_806_, v___y_805_, v_a_775_, v_a_776_, v_a_777_, v_a_778_, v_a_779_,
                        v_a_780_, v_a_781_,
                    );
                    if leanh::lean_obj_tag(v___x_808_) == 0 {
                        leanh::lean_dec_ref_known(v___x_808_, 1);
                        if v_isShared_802_ == 0 {
                            leanh::lean_ctor_set(v___x_801_, 1, v_prevRev_773_);
                            v___x_810_ = v___x_801_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_812_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_812_, 0, v_head_798_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_812_, 1, v_prevRev_773_);
                            v___x_810_ = v_reuseFailAlloc_812_;
                            state = 6;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_801_);
                        leanh::lean_dec(v_tail_799_);
                        leanh::lean_dec(v_head_798_);
                        leanh::lean_dec(v_prevRev_773_);
                        leanh::lean_dec(v_firstGoal_771_);
                        leanh::lean_dec(v_newType_770_);
                        return v___x_808_;
                    }
                } else {
                    leanh::lean_dec_ref(v___y_806_);
                    leanh::lean_del_object(v___x_801_);
                    leanh::lean_dec(v_tail_799_);
                    leanh::lean_dec(v_head_798_);
                    leanh::lean_dec(v_prevRev_773_);
                    leanh::lean_dec(v_firstGoal_771_);
                    leanh::lean_dec(v_newType_770_);
                    return v___y_804_;
                }
            }
            6 => {
                v_goals_772_ = v_tail_799_;
                v_prevRev_773_ = v___x_810_;
                state = 0;
                continue;
            }
            7 => {
                if v___y_814_ == 0 {
                    v___x_815_ = l_Lean_Elab_Tactic_saveState___redArg(
                        v_a_775_, v_a_777_, v_a_779_, v_a_781_,
                    );
                    if leanh::lean_obj_tag(v___x_815_) == 0 {
                        v_a_816_ = leanh::lean_ctor_get(v___x_815_, 0);
                        leanh::lean_inc(v_a_816_);
                        leanh::lean_dec_ref_known(v___x_815_, 1);
                        v___x_817_ = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_go___closed__1;
                        leanh::lean_inc(v_prevRev_773_);
                        leanh::lean_inc(v_tail_799_);
                        leanh::lean_inc(v_head_798_);
                        leanh::lean_inc(v_newType_770_);
                        v___x_818_ = leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___boxed as *mut core::ffi::c_void, 14, 5);
                        leanh::lean_closure_set(v___x_818_, 0, v_newType_770_);
                        leanh::lean_closure_set(v___x_818_, 1, v_head_798_);
                        leanh::lean_closure_set(v___x_818_, 2, v_tail_799_);
                        leanh::lean_closure_set(v___x_818_, 3, v_prevRev_773_);
                        leanh::lean_closure_set(v___x_818_, 4, v___x_817_);
                        v___x_819_ = l_Lean_Elab_Tactic_withoutRecover___redArg(
                            v___x_818_, v_a_774_, v_a_775_, v_a_776_, v_a_777_, v_a_778_, v_a_779_,
                            v_a_780_, v_a_781_,
                        );
                        if leanh::lean_obj_tag(v___x_819_) == 0 {
                            leanh::lean_dec(v_a_816_);
                            leanh::lean_del_object(v___x_801_);
                            leanh::lean_dec(v_tail_799_);
                            leanh::lean_dec(v_head_798_);
                            leanh::lean_dec(v_prevRev_773_);
                            leanh::lean_dec(v_firstGoal_771_);
                            leanh::lean_dec(v_newType_770_);
                            return v___x_819_;
                        } else {
                            v_a_820_ = leanh::lean_ctor_get(v___x_819_, 0);
                            leanh::lean_inc(v_a_820_);
                            v___x_821_ = 1;
                            v___x_822_ = l_Lean_Exception_isInterrupt(v_a_820_);
                            if v___x_822_ == 0 {
                                v___x_823_ = l_Lean_Exception_isRuntime(v_a_820_);
                                v___y_804_ = v___x_819_;
                                v___y_805_ = v___x_821_;
                                v___y_806_ = v_a_816_;
                                v___y_807_ = v___x_823_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_dec(v_a_820_);
                                v___y_804_ = v___x_819_;
                                v___y_805_ = v___x_821_;
                                v___y_806_ = v_a_816_;
                                v___y_807_ = v___x_822_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_del_object(v___x_801_);
                        leanh::lean_dec(v_tail_799_);
                        leanh::lean_dec(v_head_798_);
                        leanh::lean_dec(v_prevRev_773_);
                        leanh::lean_dec(v_firstGoal_771_);
                        leanh::lean_dec(v_newType_770_);
                        v_a_824_ = leanh::lean_ctor_get(v___x_815_, 0);
                        v_isSharedCheck_831_ = (!leanh::lean_is_exclusive(v___x_815_)) as u8;
                        if v_isSharedCheck_831_ == 0 {
                            v___x_826_ = v___x_815_;
                            v_isShared_827_ = v_isSharedCheck_831_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_824_);
                            leanh::lean_dec(v___x_815_);
                            v___x_826_ = leanh::lean_box(0);
                            v_isShared_827_ = v_isSharedCheck_831_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_801_);
                    leanh::lean_dec(v_firstGoal_771_);
                    v___x_832_ = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_go___closed__1;
                    v___x_833_ =
                        l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal(
                            v_newType_770_,
                            v_head_798_,
                            v_tail_799_,
                            v_prevRev_773_,
                            v___x_832_,
                            v_a_774_,
                            v_a_775_,
                            v_a_776_,
                            v_a_777_,
                            v_a_778_,
                            v_a_779_,
                            v_a_780_,
                            v_a_781_,
                        );
                    return v___x_833_;
                }
            }
            8 => {
                if v_isShared_827_ == 0 {
                    v___x_829_ = v___x_826_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_830_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_830_, 0, v_a_824_);
                    v___x_829_ = v_reuseFailAlloc_830_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_829_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_go___boxed(
    mut v_newType_838_: *mut leanh::LeanObject,
    mut v_firstGoal_839_: *mut leanh::LeanObject,
    mut v_goals_840_: *mut leanh::LeanObject,
    mut v_prevRev_841_: *mut leanh::LeanObject,
    mut v_a_842_: *mut leanh::LeanObject,
    mut v_a_843_: *mut leanh::LeanObject,
    mut v_a_844_: *mut leanh::LeanObject,
    mut v_a_845_: *mut leanh::LeanObject,
    mut v_a_846_: *mut leanh::LeanObject,
    mut v_a_847_: *mut leanh::LeanObject,
    mut v_a_848_: *mut leanh::LeanObject,
    mut v_a_849_: *mut leanh::LeanObject,
    mut v_a_850_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_851_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_851_ = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_go(
        v_newType_838_,
        v_firstGoal_839_,
        v_goals_840_,
        v_prevRev_841_,
        v_a_842_,
        v_a_843_,
        v_a_844_,
        v_a_845_,
        v_a_846_,
        v_a_847_,
        v_a_848_,
        v_a_849_,
    );
    leanh::lean_dec(v_a_849_);
    leanh::lean_dec_ref(v_a_848_);
    leanh::lean_dec(v_a_847_);
    leanh::lean_dec_ref(v_a_846_);
    leanh::lean_dec(v_a_845_);
    leanh::lean_dec_ref(v_a_844_);
    leanh::lean_dec(v_a_843_);
    leanh::lean_dec_ref(v_a_842_);
    return v_res_851_;
}
pub unsafe fn l_Lean_Elab_Tactic_elabShow(
    mut v_newType_852_: *mut leanh::LeanObject,
    mut v_a_853_: *mut leanh::LeanObject,
    mut v_a_854_: *mut leanh::LeanObject,
    mut v_a_855_: *mut leanh::LeanObject,
    mut v_a_856_: *mut leanh::LeanObject,
    mut v_a_857_: *mut leanh::LeanObject,
    mut v_a_858_: *mut leanh::LeanObject,
    mut v_a_859_: *mut leanh::LeanObject,
    mut v_a_860_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_871_: u8 = 0;
    let mut v___x_873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_875_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_862_ = l_Lean_Elab_Tactic_getGoals___redArg(v_a_854_);
                if leanh::lean_obj_tag(v___x_862_) == 0 {
                    v_a_863_ = leanh::lean_ctor_get(v___x_862_, 0);
                    leanh::lean_inc(v_a_863_);
                    leanh::lean_dec_ref_known(v___x_862_, 1);
                    if leanh::lean_obj_tag(v_a_863_) == 1 {
                        v_head_864_ = leanh::lean_ctor_get(v_a_863_, 0);
                        leanh::lean_inc(v_head_864_);
                        v___x_865_ = leanh::lean_box(0);
                        v___x_866_ =
                            l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_go(
                                v_newType_852_,
                                v_head_864_,
                                v_a_863_,
                                v___x_865_,
                                v_a_853_,
                                v_a_854_,
                                v_a_855_,
                                v_a_856_,
                                v_a_857_,
                                v_a_858_,
                                v_a_859_,
                                v_a_860_,
                            );
                        return v___x_866_;
                    } else {
                        leanh::lean_dec(v_a_863_);
                        leanh::lean_dec(v_newType_852_);
                        v___x_867_ = l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___redArg(
                            v_a_857_, v_a_858_, v_a_859_, v_a_860_,
                        );
                        return v___x_867_;
                    }
                } else {
                    leanh::lean_dec(v_newType_852_);
                    v_a_868_ = leanh::lean_ctor_get(v___x_862_, 0);
                    v_isSharedCheck_875_ = (!leanh::lean_is_exclusive(v___x_862_)) as u8;
                    if v_isSharedCheck_875_ == 0 {
                        v___x_870_ = v___x_862_;
                        v_isShared_871_ = v_isSharedCheck_875_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_868_);
                        leanh::lean_dec(v___x_862_);
                        v___x_870_ = leanh::lean_box(0);
                        v_isShared_871_ = v_isSharedCheck_875_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_871_ == 0 {
                    v___x_873_ = v___x_870_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_874_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_874_, 0, v_a_868_);
                    v___x_873_ = v_reuseFailAlloc_874_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_873_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_elabShow___boxed(
    mut v_newType_876_: *mut leanh::LeanObject,
    mut v_a_877_: *mut leanh::LeanObject,
    mut v_a_878_: *mut leanh::LeanObject,
    mut v_a_879_: *mut leanh::LeanObject,
    mut v_a_880_: *mut leanh::LeanObject,
    mut v_a_881_: *mut leanh::LeanObject,
    mut v_a_882_: *mut leanh::LeanObject,
    mut v_a_883_: *mut leanh::LeanObject,
    mut v_a_884_: *mut leanh::LeanObject,
    mut v_a_885_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_886_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_886_ = l_Lean_Elab_Tactic_elabShow(
        v_newType_876_,
        v_a_877_,
        v_a_878_,
        v_a_879_,
        v_a_880_,
        v_a_881_,
        v_a_882_,
        v_a_883_,
        v_a_884_,
    );
    leanh::lean_dec(v_a_884_);
    leanh::lean_dec_ref(v_a_883_);
    leanh::lean_dec(v_a_882_);
    leanh::lean_dec_ref(v_a_881_);
    leanh::lean_dec(v_a_880_);
    leanh::lean_dec_ref(v_a_879_);
    leanh::lean_dec(v_a_878_);
    leanh::lean_dec_ref(v_a_877_);
    return v_res_886_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalShow_spec__0___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_889_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_887_ = leanh::lean_box(0);
    v___x_888_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_889_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_889_, 0, v___x_888_);
    leanh::lean_ctor_set(v___x_889_, 1, v___x_887_);
    return v___x_889_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalShow_spec__0___redArg()
-> *mut leanh::LeanObject {
    let mut v___x_891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_891_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalShow_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalShow_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalShow_spec__0___redArg___closed__0);
    v___x_892_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_892_, 0, v___x_891_);
    return v___x_892_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalShow_spec__0___redArg___boxed(
    mut v___y_893_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_894_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_894_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalShow_spec__0___redArg();
    return v_res_894_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalShow_spec__0(
    mut v_00_u03b1_895_: *mut leanh::LeanObject,
    mut v___y_896_: *mut leanh::LeanObject,
    mut v___y_897_: *mut leanh::LeanObject,
    mut v___y_898_: *mut leanh::LeanObject,
    mut v___y_899_: *mut leanh::LeanObject,
    mut v___y_900_: *mut leanh::LeanObject,
    mut v___y_901_: *mut leanh::LeanObject,
    mut v___y_902_: *mut leanh::LeanObject,
    mut v___y_903_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_905_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_905_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalShow_spec__0___redArg();
    return v___x_905_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalShow_spec__0___boxed(
    mut v_00_u03b1_906_: *mut leanh::LeanObject,
    mut v___y_907_: *mut leanh::LeanObject,
    mut v___y_908_: *mut leanh::LeanObject,
    mut v___y_909_: *mut leanh::LeanObject,
    mut v___y_910_: *mut leanh::LeanObject,
    mut v___y_911_: *mut leanh::LeanObject,
    mut v___y_912_: *mut leanh::LeanObject,
    mut v___y_913_: *mut leanh::LeanObject,
    mut v___y_914_: *mut leanh::LeanObject,
    mut v___y_915_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_916_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_916_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalShow_spec__0(
        v_00_u03b1_906_,
        v___y_907_,
        v___y_908_,
        v___y_909_,
        v___y_910_,
        v___y_911_,
        v___y_912_,
        v___y_913_,
        v___y_914_,
    );
    leanh::lean_dec(v___y_914_);
    leanh::lean_dec_ref(v___y_913_);
    leanh::lean_dec(v___y_912_);
    leanh::lean_dec_ref(v___y_911_);
    leanh::lean_dec(v___y_910_);
    leanh::lean_dec_ref(v___y_909_);
    leanh::lean_dec(v___y_908_);
    leanh::lean_dec_ref(v___y_907_);
    return v_res_916_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalShow(
    mut v_x_925_: *mut leanh::LeanObject,
    mut v_a_926_: *mut leanh::LeanObject,
    mut v_a_927_: *mut leanh::LeanObject,
    mut v_a_928_: *mut leanh::LeanObject,
    mut v_a_929_: *mut leanh::LeanObject,
    mut v_a_930_: *mut leanh::LeanObject,
    mut v_a_931_: *mut leanh::LeanObject,
    mut v_a_932_: *mut leanh::LeanObject,
    mut v_a_933_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_936_: u8 = 0;
    v___x_935_ = l_Lean_Elab_Tactic_evalShow___closed__3;
    leanh::lean_inc(v_x_925_);
    v___x_936_ = l_Lean_Syntax_isOfKind(v_x_925_, v___x_935_);
    if v___x_936_ == 0 {
        let mut v___x_937_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_925_);
        v___x_937_ =
            l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalShow_spec__0___redArg(
            );
        return v___x_937_;
    } else {
        let mut v___x_938_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_newType_939_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_940_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_938_ = leanh::lean_unsigned_to_nat(1);
        v_newType_939_ = l_Lean_Syntax_getArg(v_x_925_, v___x_938_);
        leanh::lean_dec(v_x_925_);
        v___x_940_ = l_Lean_Elab_Tactic_elabShow(
            v_newType_939_,
            v_a_926_,
            v_a_927_,
            v_a_928_,
            v_a_929_,
            v_a_930_,
            v_a_931_,
            v_a_932_,
            v_a_933_,
        );
        return v___x_940_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalShow___boxed(
    mut v_x_941_: *mut leanh::LeanObject,
    mut v_a_942_: *mut leanh::LeanObject,
    mut v_a_943_: *mut leanh::LeanObject,
    mut v_a_944_: *mut leanh::LeanObject,
    mut v_a_945_: *mut leanh::LeanObject,
    mut v_a_946_: *mut leanh::LeanObject,
    mut v_a_947_: *mut leanh::LeanObject,
    mut v_a_948_: *mut leanh::LeanObject,
    mut v_a_949_: *mut leanh::LeanObject,
    mut v_a_950_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_951_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_951_ = l_Lean_Elab_Tactic_evalShow(
        v_x_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_,
    );
    leanh::lean_dec(v_a_949_);
    leanh::lean_dec_ref(v_a_948_);
    leanh::lean_dec(v_a_947_);
    leanh::lean_dec_ref(v_a_946_);
    leanh::lean_dec(v_a_945_);
    leanh::lean_dec_ref(v_a_944_);
    leanh::lean_dec(v_a_943_);
    leanh::lean_dec_ref(v_a_942_);
    return v_res_951_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1()
-> *mut leanh::LeanObject {
    let mut v___x_960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_960_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_961_ = l_Lean_Elab_Tactic_evalShow___closed__3;
    v___x_962_ = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__2;
    v___x_963_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_evalShow___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_964_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_960_, v___x_961_, v___x_962_, v___x_963_,
    );
    return v___x_964_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___boxed(
    mut v_a_965_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_966_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_966_ = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1();
    return v_res_966_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Show(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Change(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Show(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Show(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Change(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Show(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Show(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Show(builtin);
}