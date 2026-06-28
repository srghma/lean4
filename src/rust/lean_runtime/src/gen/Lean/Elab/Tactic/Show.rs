// Lean compiler output
// Module: Lean.Elab.Tactic.Show
// Imports: Lean.Elab.Tactic.Change
use crate::r#gen::Init::Data::List::Basic::{
    l_List_appendTR___redArg, l_List_isEmpty___redArg, l_List_reverseAux___redArg,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind,
};
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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_9, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unsigned_to_nat,
};
pub static l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__0_value: LeanStringObject<30> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [39, 115, 104, 111, 119, 39, 32, 116, 97, 99, 116, 105, 99, 32, 102, 97, 105, 108, 101, 100, 44, 32, 112, 97, 116, 116, 101, 114, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__2_value: LeanStringObject<39> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 39, m_capacity: 39, m_length: 38, m_data: [10, 105, 115, 32, 110, 111, 116, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 97, 108, 108, 121, 32, 101, 113, 117, 97, 108, 32, 116, 111, 32, 116, 97, 114, 103, 101, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__0_value: LeanStringObject<93> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 93, m_capacity: 93, m_length: 92, m_data: [39, 115, 104, 111, 119, 39, 32, 116, 97, 99, 116, 105, 99, 32, 102, 97, 105, 108, 101, 100, 44, 32, 110, 111, 32, 103, 111, 97, 108, 115, 32, 117, 110, 105, 102, 121, 32, 119, 105, 116, 104, 32, 116, 104, 101, 32, 103, 105, 118, 101, 110, 32, 112, 97, 116, 116, 101, 114, 110, 46, 10, 10, 73, 110, 32, 116, 104, 101, 32, 102, 105, 114, 115, 116, 32, 103, 111, 97, 108, 44, 32, 116, 104, 101, 32, 112, 97, 116, 116, 101, 114, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__2_value: LeanStringObject<43> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 43, m_capacity: 43, m_length: 42, m_data: [10, 105, 115, 32, 110, 111, 116, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 97, 108, 108, 121, 32, 101, 113, 117, 97, 108, 32, 116, 111, 32, 116, 104, 101, 32, 116, 97, 114, 103, 101, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__4_value: LeanStringObject<34> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [10, 40, 69, 114, 114, 111, 114, 115, 32, 102, 111, 114, 32, 111, 116, 104, 101, 114, 32, 103, 111, 97, 108, 115, 32, 111, 109, 105, 116, 116, 101, 100, 41, 0]};
static mut l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__4_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 104, 111, 119, 0]};
static mut l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___closed__0_value) as *mut LeanObject,3987080461608668766 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___closed__1_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_go___closed__0_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_go___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_go___closed__1_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_go___closed__1_value
) as *mut LeanObject;
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalShow_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalShow_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_evalShow___closed__0_value: LeanStringObject<5> = LeanStringObject {
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
static mut l_Lean_Elab_Tactic_evalShow___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalShow___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalShow___closed__1_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_evalShow___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalShow___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalShow___closed__2_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_evalShow___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalShow___closed__2_value) as *mut LeanObject;
static l_Lean_Elab_Tactic_evalShow___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_evalShow___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_evalShow___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_evalShow___closed__3_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_evalShow___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_evalShow___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_evalShow___closed__3_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_evalShow___closed__2_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_evalShow___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_evalShow___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___closed__0_value) as *mut LeanObject,4563519173115679639 as *mut LeanObject] };
static mut l_Lean_Elab_Tactic_evalShow___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalShow___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__1_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [101, 118, 97, 108, 83, 104, 111, 119, 0]};
static mut l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__1_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalShow___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__2_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__0_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__2_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__2_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalShow___closed__2_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__2_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__1_value) as *mut LeanObject,14579851650025421784 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__2_value) as *mut LeanObject;
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_486_: *mut LeanObject = core::ptr::null_mut();
    v___x_485_ = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__0;
    v___x_486_ = l_Lean_stringToMessageData(v___x_485_);
    return v___x_486_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_489_: *mut LeanObject = core::ptr::null_mut();
    v___x_488_ = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__2;
    v___x_489_ = l_Lean_stringToMessageData(v___x_488_);
    return v___x_489_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg(
    mut v_p_490_: *mut LeanObject,
    mut v_tgt_491_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_500_: *mut LeanObject = core::ptr::null_mut();
    v___x_493_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__1_once), _init_l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__1);
    v___x_494_ = l_Lean_indentExpr(v_p_490_);
    v___x_495_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_495_, 0, v___x_493_);
    lean_ctor_set(v___x_495_, 1, v___x_494_);
    v___x_496_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__3_once), _init_l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___closed__3);
    v___x_497_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_497_, 0, v___x_495_);
    lean_ctor_set(v___x_497_, 1, v___x_496_);
    v___x_498_ = l_Lean_indentExpr(v_tgt_491_);
    v___x_499_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_499_, 0, v___x_497_);
    lean_ctor_set(v___x_499_, 1, v___x_498_);
    v___x_500_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_500_, 0, v___x_499_);
    return v___x_500_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg___boxed(
    mut v_p_501_: *mut LeanObject,
    mut v_tgt_502_: *mut LeanObject,
    mut v_a_503_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_504_: *mut LeanObject = core::ptr::null_mut();
    v_res_504_ =
        l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg(
            v_p_501_, v_tgt_502_,
        );
    return v_res_504_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError(
    mut v_p_505_: *mut LeanObject,
    mut v_tgt_506_: *mut LeanObject,
    mut v_a_507_: *mut LeanObject,
    mut v_a_508_: *mut LeanObject,
    mut v_a_509_: *mut LeanObject,
    mut v_a_510_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_512_: *mut LeanObject = core::ptr::null_mut();
    v___x_512_ =
        l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___redArg(
            v_p_505_, v_tgt_506_,
        );
    return v___x_512_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError___boxed(
    mut v_p_513_: *mut LeanObject,
    mut v_tgt_514_: *mut LeanObject,
    mut v_a_515_: *mut LeanObject,
    mut v_a_516_: *mut LeanObject,
    mut v_a_517_: *mut LeanObject,
    mut v_a_518_: *mut LeanObject,
    mut v_a_519_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_520_: *mut LeanObject = core::ptr::null_mut();
    v_res_520_ = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_simpleError(
        v_p_513_, v_tgt_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_,
    );
    lean_dec(v_a_518_);
    lean_dec_ref(v_a_517_);
    lean_dec(v_a_516_);
    lean_dec_ref(v_a_515_);
    return v_res_520_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_523_: *mut LeanObject = core::ptr::null_mut();
    v___x_522_ = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__0;
    v___x_523_ = l_Lean_stringToMessageData(v___x_522_);
    return v___x_523_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_526_: *mut LeanObject = core::ptr::null_mut();
    v___x_525_ = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__2;
    v___x_526_ = l_Lean_stringToMessageData(v___x_525_);
    return v___x_526_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_529_: *mut LeanObject = core::ptr::null_mut();
    v___x_528_ = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__4;
    v___x_529_ = l_Lean_stringToMessageData(v___x_528_);
    return v___x_529_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg(
    mut v_p_530_: *mut LeanObject,
    mut v_tgt_531_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_542_: *mut LeanObject = core::ptr::null_mut();
    v___x_533_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__1_once), _init_l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__1);
    v___x_534_ = l_Lean_indentExpr(v_p_530_);
    v___x_535_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_535_, 0, v___x_533_);
    lean_ctor_set(v___x_535_, 1, v___x_534_);
    v___x_536_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__3_once), _init_l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__3);
    v___x_537_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_537_, 0, v___x_535_);
    lean_ctor_set(v___x_537_, 1, v___x_536_);
    v___x_538_ = l_Lean_indentExpr(v_tgt_531_);
    v___x_539_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_539_, 0, v___x_537_);
    lean_ctor_set(v___x_539_, 1, v___x_538_);
    v___x_540_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__5_once), _init_l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___closed__5);
    v___x_541_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_541_, 0, v___x_539_);
    lean_ctor_set(v___x_541_, 1, v___x_540_);
    v___x_542_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_542_, 0, v___x_541_);
    return v___x_542_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg___boxed(
    mut v_p_543_: *mut LeanObject,
    mut v_tgt_544_: *mut LeanObject,
    mut v_a_545_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_546_: *mut LeanObject = core::ptr::null_mut();
    v_res_546_ = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg(
        v_p_543_, v_tgt_544_,
    );
    return v_res_546_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError(
    mut v_p_547_: *mut LeanObject,
    mut v_tgt_548_: *mut LeanObject,
    mut v_a_549_: *mut LeanObject,
    mut v_a_550_: *mut LeanObject,
    mut v_a_551_: *mut LeanObject,
    mut v_a_552_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_554_: *mut LeanObject = core::ptr::null_mut();
    v___x_554_ = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___redArg(
        v_p_547_, v_tgt_548_,
    );
    return v___x_554_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError___boxed(
    mut v_p_555_: *mut LeanObject,
    mut v_tgt_556_: *mut LeanObject,
    mut v_a_557_: *mut LeanObject,
    mut v_a_558_: *mut LeanObject,
    mut v_a_559_: *mut LeanObject,
    mut v_a_560_: *mut LeanObject,
    mut v_a_561_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_562_: *mut LeanObject = core::ptr::null_mut();
    v_res_562_ = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_manyError(
        v_p_555_, v_tgt_556_, v_a_557_, v_a_558_, v_a_559_, v_a_560_,
    );
    lean_dec(v_a_560_);
    lean_dec_ref(v_a_559_);
    lean_dec(v_a_558_);
    lean_dec_ref(v_a_557_);
    return v_res_562_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal_spec__0___redArg___lam__0(
    mut v_x_563_: *mut LeanObject,
    mut v___y_564_: *mut LeanObject,
    mut v___y_565_: *mut LeanObject,
    mut v___y_566_: *mut LeanObject,
    mut v___y_567_: *mut LeanObject,
    mut v___y_568_: *mut LeanObject,
    mut v___y_569_: *mut LeanObject,
    mut v___y_570_: *mut LeanObject,
    mut v___y_571_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_573_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_567_);
    lean_inc_ref(v___y_566_);
    lean_inc(v___y_565_);
    lean_inc_ref(v___y_564_);
    v___x_573_ = lean_apply_9(
        v_x_563_,
        v___y_564_,
        v___y_565_,
        v___y_566_,
        v___y_567_,
        v___y_568_,
        v___y_569_,
        v___y_570_,
        v___y_571_,
        lean_box(0),
    );
    return v___x_573_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal_spec__0___redArg___lam__0___boxed(
    mut v_x_574_: *mut LeanObject,
    mut v___y_575_: *mut LeanObject,
    mut v___y_576_: *mut LeanObject,
    mut v___y_577_: *mut LeanObject,
    mut v___y_578_: *mut LeanObject,
    mut v___y_579_: *mut LeanObject,
    mut v___y_580_: *mut LeanObject,
    mut v___y_581_: *mut LeanObject,
    mut v___y_582_: *mut LeanObject,
    mut v___y_583_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_584_: *mut LeanObject = core::ptr::null_mut();
    v_res_584_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal_spec__0___redArg___lam__0(v_x_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_);
    lean_dec(v___y_578_);
    lean_dec_ref(v___y_577_);
    lean_dec(v___y_576_);
    lean_dec_ref(v___y_575_);
    return v_res_584_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal_spec__0___redArg(
    mut v_mvarId_585_: *mut LeanObject,
    mut v_x_586_: *mut LeanObject,
    mut v___y_587_: *mut LeanObject,
    mut v___y_588_: *mut LeanObject,
    mut v___y_589_: *mut LeanObject,
    mut v___y_590_: *mut LeanObject,
    mut v___y_591_: *mut LeanObject,
    mut v___y_592_: *mut LeanObject,
    mut v___y_593_: *mut LeanObject,
    mut v___y_594_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_601_: u8 = 0;
    let mut v___x_603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_605_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_590_);
                lean_inc_ref(v___y_589_);
                lean_inc(v___y_588_);
                lean_inc_ref(v___y_587_);
                v___f_596_ = lean_alloc_closure(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 5);
                lean_closure_set(v___f_596_, 0, v_x_586_);
                lean_closure_set(v___f_596_, 1, v___y_587_);
                lean_closure_set(v___f_596_, 2, v___y_588_);
                lean_closure_set(v___f_596_, 3, v___y_589_);
                lean_closure_set(v___f_596_, 4, v___y_590_);
                v___x_597_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    lean_box(0),
                    v_mvarId_585_,
                    v___f_596_,
                    v___y_591_,
                    v___y_592_,
                    v___y_593_,
                    v___y_594_,
                );
                if lean_obj_tag(v___x_597_) == 0 {
                    return v___x_597_;
                } else {
                    v_a_598_ = lean_ctor_get(v___x_597_, 0);
                    v_isSharedCheck_605_ = (!lean_is_exclusive(v___x_597_)) as u8;
                    if v_isSharedCheck_605_ == 0 {
                        v___x_600_ = v___x_597_;
                        v_isShared_601_ = v_isSharedCheck_605_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_598_);
                        lean_dec(v___x_597_);
                        v___x_600_ = lean_box(0);
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
                    v_reuseFailAlloc_604_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_604_, 0, v_a_598_);
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
    mut v_mvarId_606_: *mut LeanObject,
    mut v_x_607_: *mut LeanObject,
    mut v___y_608_: *mut LeanObject,
    mut v___y_609_: *mut LeanObject,
    mut v___y_610_: *mut LeanObject,
    mut v___y_611_: *mut LeanObject,
    mut v___y_612_: *mut LeanObject,
    mut v___y_613_: *mut LeanObject,
    mut v___y_614_: *mut LeanObject,
    mut v___y_615_: *mut LeanObject,
    mut v___y_616_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_617_: *mut LeanObject = core::ptr::null_mut();
    v_res_617_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal_spec__0___redArg(v_mvarId_606_, v_x_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
    lean_dec(v___y_615_);
    lean_dec_ref(v___y_614_);
    lean_dec(v___y_613_);
    lean_dec_ref(v___y_612_);
    lean_dec(v___y_611_);
    lean_dec_ref(v___y_610_);
    lean_dec(v___y_609_);
    lean_dec_ref(v___y_608_);
    return v_res_617_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal_spec__0(
    mut v_00_u03b1_618_: *mut LeanObject,
    mut v_mvarId_619_: *mut LeanObject,
    mut v_x_620_: *mut LeanObject,
    mut v___y_621_: *mut LeanObject,
    mut v___y_622_: *mut LeanObject,
    mut v___y_623_: *mut LeanObject,
    mut v___y_624_: *mut LeanObject,
    mut v___y_625_: *mut LeanObject,
    mut v___y_626_: *mut LeanObject,
    mut v___y_627_: *mut LeanObject,
    mut v___y_628_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_630_: *mut LeanObject = core::ptr::null_mut();
    v___x_630_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal_spec__0___redArg(v_mvarId_619_, v_x_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_);
    return v___x_630_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal_spec__0___boxed(
    mut v_00_u03b1_631_: *mut LeanObject,
    mut v_mvarId_632_: *mut LeanObject,
    mut v_x_633_: *mut LeanObject,
    mut v___y_634_: *mut LeanObject,
    mut v___y_635_: *mut LeanObject,
    mut v___y_636_: *mut LeanObject,
    mut v___y_637_: *mut LeanObject,
    mut v___y_638_: *mut LeanObject,
    mut v___y_639_: *mut LeanObject,
    mut v___y_640_: *mut LeanObject,
    mut v___y_641_: *mut LeanObject,
    mut v___y_642_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_643_: *mut LeanObject = core::ptr::null_mut();
    v_res_643_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal_spec__0(v_00_u03b1_631_, v_mvarId_632_, v_x_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
    lean_dec(v___y_641_);
    lean_dec_ref(v___y_640_);
    lean_dec(v___y_639_);
    lean_dec_ref(v___y_638_);
    lean_dec(v___y_637_);
    lean_dec_ref(v___y_636_);
    lean_dec(v___y_635_);
    lean_dec_ref(v___y_634_);
    return v_res_643_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___lam__0(
    mut v___x_644_: *mut LeanObject,
    mut v_a_645_: *mut LeanObject,
    mut v___x_646_: *mut LeanObject,
    mut v___x_647_: u8,
    mut v_goal_648_: *mut LeanObject,
    mut v_goals_649_: *mut LeanObject,
    mut v_prevRev_650_: *mut LeanObject,
    mut v___y_651_: *mut LeanObject,
    mut v___y_652_: *mut LeanObject,
    mut v___y_653_: *mut LeanObject,
    mut v___y_654_: *mut LeanObject,
    mut v___y_655_: *mut LeanObject,
    mut v___y_656_: *mut LeanObject,
    mut v___y_657_: *mut LeanObject,
    mut v___y_658_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_666_: u8 = 0;
    let mut v___x_667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_678_: u8 = 0;
    let mut v___x_680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_682_: u8 = 0;
    let mut v_isSharedCheck_683_: u8 = 0;
    let mut v_a_684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_687_: u8 = 0;
    let mut v___x_689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_691_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_660_ = l_Lean_Elab_Tactic_withCollectingNewGoalsFrom(
                    v___x_644_, v_a_645_, v___x_646_, v___x_647_, v___y_651_, v___y_652_,
                    v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_,
                );
                if lean_obj_tag(v___x_660_) == 0 {
                    v_a_661_ = lean_ctor_get(v___x_660_, 0);
                    lean_inc(v_a_661_);
                    lean_dec_ref_known(v___x_660_, 1);
                    v_fst_662_ = lean_ctor_get(v_a_661_, 0);
                    v_snd_663_ = lean_ctor_get(v_a_661_, 1);
                    v_isSharedCheck_683_ = (!lean_is_exclusive(v_a_661_)) as u8;
                    if v_isSharedCheck_683_ == 0 {
                        v___x_665_ = v_a_661_;
                        v_isShared_666_ = v_isSharedCheck_683_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_663_);
                        lean_inc(v_fst_662_);
                        lean_dec(v_a_661_);
                        v___x_665_ = lean_box(0);
                        v_isShared_666_ = v_isSharedCheck_683_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_prevRev_650_);
                    lean_dec(v_goals_649_);
                    lean_dec(v_goal_648_);
                    v_a_684_ = lean_ctor_get(v___x_660_, 0);
                    v_isSharedCheck_691_ = (!lean_is_exclusive(v___x_660_)) as u8;
                    if v_isSharedCheck_691_ == 0 {
                        v___x_686_ = v___x_660_;
                        v_isShared_687_ = v_isSharedCheck_691_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_684_);
                        lean_dec(v___x_660_);
                        v___x_686_ = lean_box(0);
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
                if lean_obj_tag(v___x_667_) == 0 {
                    v_a_668_ = lean_ctor_get(v___x_667_, 0);
                    lean_inc(v_a_668_);
                    lean_dec_ref_known(v___x_667_, 1);
                    v___x_669_ = l_List_appendTR___redArg(v_snd_663_, v_goals_649_);
                    v___x_670_ = l_List_reverseAux___redArg(v_prevRev_650_, v___x_669_);
                    if v_isShared_666_ == 0 {
                        lean_ctor_set_tag(v___x_665_, 1);
                        lean_ctor_set(v___x_665_, 1, v___x_670_);
                        lean_ctor_set(v___x_665_, 0, v_a_668_);
                        v___x_672_ = v___x_665_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_674_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_674_, 0, v_a_668_);
                        lean_ctor_set(v_reuseFailAlloc_674_, 1, v___x_670_);
                        v___x_672_ = v_reuseFailAlloc_674_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_665_);
                    lean_dec(v_snd_663_);
                    lean_dec(v_prevRev_650_);
                    lean_dec(v_goals_649_);
                    v_a_675_ = lean_ctor_get(v___x_667_, 0);
                    v_isSharedCheck_682_ = (!lean_is_exclusive(v___x_667_)) as u8;
                    if v_isSharedCheck_682_ == 0 {
                        v___x_677_ = v___x_667_;
                        v_isShared_678_ = v_isSharedCheck_682_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_675_);
                        lean_dec(v___x_667_);
                        v___x_677_ = lean_box(0);
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
                    v_reuseFailAlloc_681_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_681_, 0, v_a_675_);
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
                    v_reuseFailAlloc_690_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_690_, 0, v_a_684_);
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
    mut v___x_692_: *mut LeanObject,
    mut v_a_693_: *mut LeanObject,
    mut v___x_694_: *mut LeanObject,
    mut v___x_695_: *mut LeanObject,
    mut v_goal_696_: *mut LeanObject,
    mut v_goals_697_: *mut LeanObject,
    mut v_prevRev_698_: *mut LeanObject,
    mut v___y_699_: *mut LeanObject,
    mut v___y_700_: *mut LeanObject,
    mut v___y_701_: *mut LeanObject,
    mut v___y_702_: *mut LeanObject,
    mut v___y_703_: *mut LeanObject,
    mut v___y_704_: *mut LeanObject,
    mut v___y_705_: *mut LeanObject,
    mut v___y_706_: *mut LeanObject,
    mut v___y_707_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2263__boxed_708_: u8 = 0;
    let mut v_res_709_: *mut LeanObject = core::ptr::null_mut();
    v___x_2263__boxed_708_ = (lean_unbox(v___x_695_) as u8);
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
    lean_dec(v___y_706_);
    lean_dec_ref(v___y_705_);
    lean_dec(v___y_704_);
    lean_dec_ref(v___y_703_);
    lean_dec(v___y_702_);
    lean_dec_ref(v___y_701_);
    lean_dec(v___y_700_);
    lean_dec_ref(v___y_699_);
    return v_res_709_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal(
    mut v_newType_713_: *mut LeanObject,
    mut v_goal_714_: *mut LeanObject,
    mut v_goals_715_: *mut LeanObject,
    mut v_prevRev_716_: *mut LeanObject,
    mut v_err_717_: *mut LeanObject,
    mut v_a_718_: *mut LeanObject,
    mut v_a_719_: *mut LeanObject,
    mut v_a_720_: *mut LeanObject,
    mut v_a_721_: *mut LeanObject,
    mut v_a_722_: *mut LeanObject,
    mut v_a_723_: *mut LeanObject,
    mut v_a_724_: *mut LeanObject,
    mut v_a_725_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_733_: u8 = 0;
    let mut v___x_734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_740_: u8 = 0;
    let mut v___x_742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_744_: u8 = 0;
    let mut v_a_745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_748_: u8 = 0;
    let mut v___x_750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_752_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_goal_714_);
                v___x_727_ =
                    l_Lean_MVarId_getType(v_goal_714_, v_a_722_, v_a_723_, v_a_724_, v_a_725_);
                if lean_obj_tag(v___x_727_) == 0 {
                    v_a_728_ = lean_ctor_get(v___x_727_, 0);
                    lean_inc(v_a_728_);
                    lean_dec_ref_known(v___x_727_, 1);
                    lean_inc(v_goal_714_);
                    v___x_729_ =
                        l_Lean_MVarId_getTag(v_goal_714_, v_a_722_, v_a_723_, v_a_724_, v_a_725_);
                    if lean_obj_tag(v___x_729_) == 0 {
                        v_a_730_ = lean_ctor_get(v___x_729_, 0);
                        lean_inc(v_a_730_);
                        lean_dec_ref_known(v___x_729_, 1);
                        v___x_731_ = lean_alloc_closure(
                            l_Lean_Elab_Tactic_elabChange___boxed as *mut core::ffi::c_void,
                            12,
                            3,
                        );
                        lean_closure_set(v___x_731_, 0, v_a_728_);
                        lean_closure_set(v___x_731_, 1, v_newType_713_);
                        lean_closure_set(v___x_731_, 2, v_err_717_);
                        v___x_732_ = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___closed__1;
                        v___x_733_ = 0;
                        v___x_734_ = lean_box((v___x_733_) as usize);
                        lean_inc(v_goal_714_);
                        v___f_735_ = lean_alloc_closure(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___lam__0___boxed as *mut core::ffi::c_void, 16, 7);
                        lean_closure_set(v___f_735_, 0, v___x_731_);
                        lean_closure_set(v___f_735_, 1, v_a_730_);
                        lean_closure_set(v___f_735_, 2, v___x_732_);
                        lean_closure_set(v___f_735_, 3, v___x_734_);
                        lean_closure_set(v___f_735_, 4, v_goal_714_);
                        lean_closure_set(v___f_735_, 5, v_goals_715_);
                        lean_closure_set(v___f_735_, 6, v_prevRev_716_);
                        v___x_736_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal_spec__0___redArg(v_goal_714_, v___f_735_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_);
                        return v___x_736_;
                    } else {
                        lean_dec(v_a_728_);
                        lean_dec_ref(v_err_717_);
                        lean_dec(v_prevRev_716_);
                        lean_dec(v_goals_715_);
                        lean_dec(v_goal_714_);
                        lean_dec(v_newType_713_);
                        v_a_737_ = lean_ctor_get(v___x_729_, 0);
                        v_isSharedCheck_744_ = (!lean_is_exclusive(v___x_729_)) as u8;
                        if v_isSharedCheck_744_ == 0 {
                            v___x_739_ = v___x_729_;
                            v_isShared_740_ = v_isSharedCheck_744_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_737_);
                            lean_dec(v___x_729_);
                            v___x_739_ = lean_box(0);
                            v_isShared_740_ = v_isSharedCheck_744_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_err_717_);
                    lean_dec(v_prevRev_716_);
                    lean_dec(v_goals_715_);
                    lean_dec(v_goal_714_);
                    lean_dec(v_newType_713_);
                    v_a_745_ = lean_ctor_get(v___x_727_, 0);
                    v_isSharedCheck_752_ = (!lean_is_exclusive(v___x_727_)) as u8;
                    if v_isSharedCheck_752_ == 0 {
                        v___x_747_ = v___x_727_;
                        v_isShared_748_ = v_isSharedCheck_752_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_745_);
                        lean_dec(v___x_727_);
                        v___x_747_ = lean_box(0);
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
                    v_reuseFailAlloc_743_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_743_, 0, v_a_737_);
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
                    v_reuseFailAlloc_751_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_751_, 0, v_a_745_);
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
    mut v_newType_753_: *mut LeanObject,
    mut v_goal_754_: *mut LeanObject,
    mut v_goals_755_: *mut LeanObject,
    mut v_prevRev_756_: *mut LeanObject,
    mut v_err_757_: *mut LeanObject,
    mut v_a_758_: *mut LeanObject,
    mut v_a_759_: *mut LeanObject,
    mut v_a_760_: *mut LeanObject,
    mut v_a_761_: *mut LeanObject,
    mut v_a_762_: *mut LeanObject,
    mut v_a_763_: *mut LeanObject,
    mut v_a_764_: *mut LeanObject,
    mut v_a_765_: *mut LeanObject,
    mut v_a_766_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_767_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_765_);
    lean_dec_ref(v_a_764_);
    lean_dec(v_a_763_);
    lean_dec_ref(v_a_762_);
    lean_dec(v_a_761_);
    lean_dec_ref(v_a_760_);
    lean_dec(v_a_759_);
    lean_dec_ref(v_a_758_);
    return v_res_767_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_go(
    mut v_newType_770_: *mut LeanObject,
    mut v_firstGoal_771_: *mut LeanObject,
    mut v_goals_772_: *mut LeanObject,
    mut v_prevRev_773_: *mut LeanObject,
    mut v_a_774_: *mut LeanObject,
    mut v_a_775_: *mut LeanObject,
    mut v_a_776_: *mut LeanObject,
    mut v_a_777_: *mut LeanObject,
    mut v_a_778_: *mut LeanObject,
    mut v_a_779_: *mut LeanObject,
    mut v_a_780_: *mut LeanObject,
    mut v_a_781_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_793_: u8 = 0;
    let mut v___x_795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_797_: u8 = 0;
    let mut v_head_798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_802_: u8 = 0;
    let mut v___y_804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_805_: u8 = 0;
    let mut v___y_806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_807_: u8 = 0;
    let mut v___x_808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_814_: u8 = 0;
    let mut v___x_815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_821_: u8 = 0;
    let mut v___x_822_: u8 = 0;
    let mut v___x_823_: u8 = 0;
    let mut v_a_824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_827_: u8 = 0;
    let mut v___x_829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_831_: u8 = 0;
    let mut v___x_832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_834_: u8 = 0;
    let mut v___x_835_: u8 = 0;
    let mut v_recover_836_: u8 = 0;
    let mut v_isSharedCheck_837_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_goals_772_) == 0 {
                    lean_dec(v_prevRev_773_);
                    v___x_783_ = l_Lean_Elab_Tactic_getGoals___redArg(v_a_775_);
                    if lean_obj_tag(v___x_783_) == 0 {
                        v_a_784_ = lean_ctor_get(v___x_783_, 0);
                        lean_inc(v_a_784_);
                        lean_dec_ref_known(v___x_783_, 1);
                        if lean_obj_tag(v_a_784_) == 0 {
                            v___y_786_ = v_a_784_;
                            state = 1;
                            continue;
                        } else {
                            v_tail_789_ = lean_ctor_get(v_a_784_, 1);
                            lean_inc(v_tail_789_);
                            lean_dec_ref_known(v_a_784_, 2);
                            v___y_786_ = v_tail_789_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_firstGoal_771_);
                        lean_dec(v_newType_770_);
                        v_a_790_ = lean_ctor_get(v___x_783_, 0);
                        v_isSharedCheck_797_ = (!lean_is_exclusive(v___x_783_)) as u8;
                        if v_isSharedCheck_797_ == 0 {
                            v___x_792_ = v___x_783_;
                            v_isShared_793_ = v_isSharedCheck_797_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_790_);
                            lean_dec(v___x_783_);
                            v___x_792_ = lean_box(0);
                            v_isShared_793_ = v_isSharedCheck_797_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v_head_798_ = lean_ctor_get(v_goals_772_, 0);
                    v_tail_799_ = lean_ctor_get(v_goals_772_, 1);
                    v_isSharedCheck_837_ = (!lean_is_exclusive(v_goals_772_)) as u8;
                    if v_isSharedCheck_837_ == 0 {
                        v___x_801_ = v_goals_772_;
                        v_isShared_802_ = v_isSharedCheck_837_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_tail_799_);
                        lean_inc(v_head_798_);
                        lean_dec(v_goals_772_);
                        v___x_801_ = lean_box(0);
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
                    v_reuseFailAlloc_796_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_796_, 0, v_a_790_);
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
                        v_recover_836_ = lean_ctor_get_uint8(
                            v_a_774_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
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
                    lean_dec_ref(v___y_804_);
                    v___x_808_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(
                        v___y_806_, v___y_805_, v_a_775_, v_a_776_, v_a_777_, v_a_778_, v_a_779_,
                        v_a_780_, v_a_781_,
                    );
                    if lean_obj_tag(v___x_808_) == 0 {
                        lean_dec_ref_known(v___x_808_, 1);
                        if v_isShared_802_ == 0 {
                            lean_ctor_set(v___x_801_, 1, v_prevRev_773_);
                            v___x_810_ = v___x_801_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_812_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_812_, 0, v_head_798_);
                            lean_ctor_set(v_reuseFailAlloc_812_, 1, v_prevRev_773_);
                            v___x_810_ = v_reuseFailAlloc_812_;
                            state = 6;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_801_);
                        lean_dec(v_tail_799_);
                        lean_dec(v_head_798_);
                        lean_dec(v_prevRev_773_);
                        lean_dec(v_firstGoal_771_);
                        lean_dec(v_newType_770_);
                        return v___x_808_;
                    }
                } else {
                    lean_dec_ref(v___y_806_);
                    lean_del_object(v___x_801_);
                    lean_dec(v_tail_799_);
                    lean_dec(v_head_798_);
                    lean_dec(v_prevRev_773_);
                    lean_dec(v_firstGoal_771_);
                    lean_dec(v_newType_770_);
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
                    if lean_obj_tag(v___x_815_) == 0 {
                        v_a_816_ = lean_ctor_get(v___x_815_, 0);
                        lean_inc(v_a_816_);
                        lean_dec_ref_known(v___x_815_, 1);
                        v___x_817_ = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_go___closed__1;
                        lean_inc(v_prevRev_773_);
                        lean_inc(v_tail_799_);
                        lean_inc(v_head_798_);
                        lean_inc(v_newType_770_);
                        v___x_818_ = lean_alloc_closure(l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_elabShow_tryGoal___boxed as *mut core::ffi::c_void, 14, 5);
                        lean_closure_set(v___x_818_, 0, v_newType_770_);
                        lean_closure_set(v___x_818_, 1, v_head_798_);
                        lean_closure_set(v___x_818_, 2, v_tail_799_);
                        lean_closure_set(v___x_818_, 3, v_prevRev_773_);
                        lean_closure_set(v___x_818_, 4, v___x_817_);
                        v___x_819_ = l_Lean_Elab_Tactic_withoutRecover___redArg(
                            v___x_818_, v_a_774_, v_a_775_, v_a_776_, v_a_777_, v_a_778_, v_a_779_,
                            v_a_780_, v_a_781_,
                        );
                        if lean_obj_tag(v___x_819_) == 0 {
                            lean_dec(v_a_816_);
                            lean_del_object(v___x_801_);
                            lean_dec(v_tail_799_);
                            lean_dec(v_head_798_);
                            lean_dec(v_prevRev_773_);
                            lean_dec(v_firstGoal_771_);
                            lean_dec(v_newType_770_);
                            return v___x_819_;
                        } else {
                            v_a_820_ = lean_ctor_get(v___x_819_, 0);
                            lean_inc(v_a_820_);
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
                                lean_dec(v_a_820_);
                                v___y_804_ = v___x_819_;
                                v___y_805_ = v___x_821_;
                                v___y_806_ = v_a_816_;
                                v___y_807_ = v___x_822_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        lean_del_object(v___x_801_);
                        lean_dec(v_tail_799_);
                        lean_dec(v_head_798_);
                        lean_dec(v_prevRev_773_);
                        lean_dec(v_firstGoal_771_);
                        lean_dec(v_newType_770_);
                        v_a_824_ = lean_ctor_get(v___x_815_, 0);
                        v_isSharedCheck_831_ = (!lean_is_exclusive(v___x_815_)) as u8;
                        if v_isSharedCheck_831_ == 0 {
                            v___x_826_ = v___x_815_;
                            v_isShared_827_ = v_isSharedCheck_831_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_824_);
                            lean_dec(v___x_815_);
                            v___x_826_ = lean_box(0);
                            v_isShared_827_ = v_isSharedCheck_831_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_801_);
                    lean_dec(v_firstGoal_771_);
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
                    v_reuseFailAlloc_830_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_830_, 0, v_a_824_);
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
    mut v_newType_838_: *mut LeanObject,
    mut v_firstGoal_839_: *mut LeanObject,
    mut v_goals_840_: *mut LeanObject,
    mut v_prevRev_841_: *mut LeanObject,
    mut v_a_842_: *mut LeanObject,
    mut v_a_843_: *mut LeanObject,
    mut v_a_844_: *mut LeanObject,
    mut v_a_845_: *mut LeanObject,
    mut v_a_846_: *mut LeanObject,
    mut v_a_847_: *mut LeanObject,
    mut v_a_848_: *mut LeanObject,
    mut v_a_849_: *mut LeanObject,
    mut v_a_850_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_851_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_849_);
    lean_dec_ref(v_a_848_);
    lean_dec(v_a_847_);
    lean_dec_ref(v_a_846_);
    lean_dec(v_a_845_);
    lean_dec_ref(v_a_844_);
    lean_dec(v_a_843_);
    lean_dec_ref(v_a_842_);
    return v_res_851_;
}
pub unsafe fn l_Lean_Elab_Tactic_elabShow(
    mut v_newType_852_: *mut LeanObject,
    mut v_a_853_: *mut LeanObject,
    mut v_a_854_: *mut LeanObject,
    mut v_a_855_: *mut LeanObject,
    mut v_a_856_: *mut LeanObject,
    mut v_a_857_: *mut LeanObject,
    mut v_a_858_: *mut LeanObject,
    mut v_a_859_: *mut LeanObject,
    mut v_a_860_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_871_: u8 = 0;
    let mut v___x_873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_875_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_862_ = l_Lean_Elab_Tactic_getGoals___redArg(v_a_854_);
                if lean_obj_tag(v___x_862_) == 0 {
                    v_a_863_ = lean_ctor_get(v___x_862_, 0);
                    lean_inc(v_a_863_);
                    lean_dec_ref_known(v___x_862_, 1);
                    if lean_obj_tag(v_a_863_) == 1 {
                        v_head_864_ = lean_ctor_get(v_a_863_, 0);
                        lean_inc(v_head_864_);
                        v___x_865_ = lean_box(0);
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
                        lean_dec(v_a_863_);
                        lean_dec(v_newType_852_);
                        v___x_867_ = l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___redArg(
                            v_a_857_, v_a_858_, v_a_859_, v_a_860_,
                        );
                        return v___x_867_;
                    }
                } else {
                    lean_dec(v_newType_852_);
                    v_a_868_ = lean_ctor_get(v___x_862_, 0);
                    v_isSharedCheck_875_ = (!lean_is_exclusive(v___x_862_)) as u8;
                    if v_isSharedCheck_875_ == 0 {
                        v___x_870_ = v___x_862_;
                        v_isShared_871_ = v_isSharedCheck_875_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_868_);
                        lean_dec(v___x_862_);
                        v___x_870_ = lean_box(0);
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
                    v_reuseFailAlloc_874_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_874_, 0, v_a_868_);
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
    mut v_newType_876_: *mut LeanObject,
    mut v_a_877_: *mut LeanObject,
    mut v_a_878_: *mut LeanObject,
    mut v_a_879_: *mut LeanObject,
    mut v_a_880_: *mut LeanObject,
    mut v_a_881_: *mut LeanObject,
    mut v_a_882_: *mut LeanObject,
    mut v_a_883_: *mut LeanObject,
    mut v_a_884_: *mut LeanObject,
    mut v_a_885_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_886_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_884_);
    lean_dec_ref(v_a_883_);
    lean_dec(v_a_882_);
    lean_dec_ref(v_a_881_);
    lean_dec(v_a_880_);
    lean_dec_ref(v_a_879_);
    lean_dec(v_a_878_);
    lean_dec_ref(v_a_877_);
    return v_res_886_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalShow_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_889_: *mut LeanObject = core::ptr::null_mut();
    v___x_887_ = lean_box(0);
    v___x_888_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_889_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_889_, 0, v___x_888_);
    lean_ctor_set(v___x_889_, 1, v___x_887_);
    return v___x_889_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalShow_spec__0___redArg()
-> *mut LeanObject {
    let mut v___x_891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut LeanObject = core::ptr::null_mut();
    v___x_891_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalShow_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalShow_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalShow_spec__0___redArg___closed__0);
    v___x_892_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_892_, 0, v___x_891_);
    return v___x_892_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalShow_spec__0___redArg___boxed(
    mut v___y_893_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_894_: *mut LeanObject = core::ptr::null_mut();
    v_res_894_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalShow_spec__0___redArg();
    return v_res_894_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalShow_spec__0(
    mut v_00_u03b1_895_: *mut LeanObject,
    mut v___y_896_: *mut LeanObject,
    mut v___y_897_: *mut LeanObject,
    mut v___y_898_: *mut LeanObject,
    mut v___y_899_: *mut LeanObject,
    mut v___y_900_: *mut LeanObject,
    mut v___y_901_: *mut LeanObject,
    mut v___y_902_: *mut LeanObject,
    mut v___y_903_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_905_: *mut LeanObject = core::ptr::null_mut();
    v___x_905_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalShow_spec__0___redArg();
    return v___x_905_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalShow_spec__0___boxed(
    mut v_00_u03b1_906_: *mut LeanObject,
    mut v___y_907_: *mut LeanObject,
    mut v___y_908_: *mut LeanObject,
    mut v___y_909_: *mut LeanObject,
    mut v___y_910_: *mut LeanObject,
    mut v___y_911_: *mut LeanObject,
    mut v___y_912_: *mut LeanObject,
    mut v___y_913_: *mut LeanObject,
    mut v___y_914_: *mut LeanObject,
    mut v___y_915_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_916_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_914_);
    lean_dec_ref(v___y_913_);
    lean_dec(v___y_912_);
    lean_dec_ref(v___y_911_);
    lean_dec(v___y_910_);
    lean_dec_ref(v___y_909_);
    lean_dec(v___y_908_);
    lean_dec_ref(v___y_907_);
    return v_res_916_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalShow(
    mut v_x_925_: *mut LeanObject,
    mut v_a_926_: *mut LeanObject,
    mut v_a_927_: *mut LeanObject,
    mut v_a_928_: *mut LeanObject,
    mut v_a_929_: *mut LeanObject,
    mut v_a_930_: *mut LeanObject,
    mut v_a_931_: *mut LeanObject,
    mut v_a_932_: *mut LeanObject,
    mut v_a_933_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_936_: u8 = 0;
    v___x_935_ = l_Lean_Elab_Tactic_evalShow___closed__3;
    lean_inc(v_x_925_);
    v___x_936_ = l_Lean_Syntax_isOfKind(v_x_925_, v___x_935_);
    if v___x_936_ == 0 {
        let mut v___x_937_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_925_);
        v___x_937_ =
            l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalShow_spec__0___redArg(
            );
        return v___x_937_;
    } else {
        let mut v___x_938_: *mut LeanObject = core::ptr::null_mut();
        let mut v_newType_939_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_940_: *mut LeanObject = core::ptr::null_mut();
        v___x_938_ = lean_unsigned_to_nat(1);
        v_newType_939_ = l_Lean_Syntax_getArg(v_x_925_, v___x_938_);
        lean_dec(v_x_925_);
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
    mut v_x_941_: *mut LeanObject,
    mut v_a_942_: *mut LeanObject,
    mut v_a_943_: *mut LeanObject,
    mut v_a_944_: *mut LeanObject,
    mut v_a_945_: *mut LeanObject,
    mut v_a_946_: *mut LeanObject,
    mut v_a_947_: *mut LeanObject,
    mut v_a_948_: *mut LeanObject,
    mut v_a_949_: *mut LeanObject,
    mut v_a_950_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_951_: *mut LeanObject = core::ptr::null_mut();
    v_res_951_ = l_Lean_Elab_Tactic_evalShow(
        v_x_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_,
    );
    lean_dec(v_a_949_);
    lean_dec_ref(v_a_948_);
    lean_dec(v_a_947_);
    lean_dec_ref(v_a_946_);
    lean_dec(v_a_945_);
    lean_dec_ref(v_a_944_);
    lean_dec(v_a_943_);
    lean_dec_ref(v_a_942_);
    return v_res_951_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1()
-> *mut LeanObject {
    let mut v___x_960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut LeanObject = core::ptr::null_mut();
    v___x_960_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_961_ = l_Lean_Elab_Tactic_evalShow___closed__3;
    v___x_962_ = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1___closed__2;
    v___x_963_ = lean_alloc_closure(
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
    mut v_a_965_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_966_: *mut LeanObject = core::ptr::null_mut();
    v_res_966_ = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1();
    return v_res_966_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Show(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Change(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Show_0__Lean_Elab_Tactic_evalShow___regBuiltin_Lean_Elab_Tactic_evalShow__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Show(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Show(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Change(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Show(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Show(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Show(builtin);
}
