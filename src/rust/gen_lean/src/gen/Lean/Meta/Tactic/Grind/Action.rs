// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Action
// Imports: Lean.Meta.Tactic.Grind.Types
use crate::r#gen::Init::Data::List::Basic::{
    l_List_intersperseTR___redArg, l_List_isEmpty___redArg, l_List_reverse___redArg,
};
use crate::r#gen::Init::Meta::Defs::{
    l_Lean_Syntax_TSepArray_getElems___redArg, l_Lean_Syntax_isNone, l_Lean_Syntax_structEq,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs,
    l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesNull, l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node3,
    l_Lean_replaceRef,
};
use crate::r#gen::Lean::CoreM::{l_Lean_Exception_isMaxHeartbeat, l_Lean_Exception_isRuntime};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::Exception::{
    l_Lean_Exception_isInterrupt, l_Lean_Exception_isMaxRecDepth, l_Lean_Exception_toMessageData,
};
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag, l_Lean_MessageData_ofList,
    l_Lean_MessageData_ofSyntax, l_Lean_MessageLog_add, l_Lean_indentD,
    l_Lean_instBEqMessageSeverity_beq, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp;
use crate::r#gen::Lean::Meta::Sym::SymM::{
    l_Lean_Meta_Sym_getConfig___redArg, l_Lean_Meta_Sym_reportIssue,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    initialize_Lean_Meta_Tactic_Grind_Types, l_Lean_Meta_Grind_SavedState_restore___redArg,
    l_Lean_Meta_Grind_Solvers_mbtc, l_Lean_Meta_Grind_evalTactic,
    l_Lean_Meta_Grind_getConfig___redArg, l_Lean_Meta_Grind_saveState___redArg,
    runtime_initialize_Lean_Meta_Tactic_Grind_Types,
};
use crate::r#gen::Lean::Meta::Tactic::Util::l_Lean_MVarId_admit;
use crate::ffi::{
    lean_array_mk, lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity,
    lean_nat_dec_eq, lean_nat_sub, lean_string_dec_eq,
};
use crate::ffi::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::ffi::lean_grind_process_new_facts;
pub static l_Lean_Meta_Grind_ActionResult_toMessageData___closed__0_value:
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
    m_data: [99, 108, 111, 115, 101, 100, 32, 0],
};
static mut l_Lean_Meta_Grind_ActionResult_toMessageData___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_ActionResult_toMessageData___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_ActionResult_toMessageData___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_ActionResult_toMessageData___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_ActionResult_toMessageData___closed__2_value:
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
    m_data: [115, 116, 117, 99, 107, 32, 0],
};
static mut l_Lean_Meta_Grind_ActionResult_toMessageData___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_ActionResult_toMessageData___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_ActionResult_toMessageData___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_ActionResult_toMessageData___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_instToMessageDataActionResult___closed__0_value:
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
    m_fun: l_Lean_Meta_Grind_ActionResult_toMessageData as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_instToMessageDataActionResult___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instToMessageDataActionResult___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Grind_instToMessageDataActionResult: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instToMessageDataActionResult___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Action_done___redArg___closed__0_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Meta_Grind_Action_done___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_done___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Action_instAndThen___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lean_Meta_Grind_Action_instAndThen___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 15,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Action_instAndThen___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_instAndThen___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Grind_Action_instAndThen: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_instAndThen___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Action_instOrElse___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lean_Meta_Grind_Action_instOrElse___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 15,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Action_instOrElse___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_instOrElse___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Grind_Action_instOrElse: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_instOrElse___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Action_run___lam__0___closed__0_value: crate::leanh::LeanStringObject<
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
static mut l_Lean_Meta_Grind_Action_run___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Action_run___lam__0___closed__1_value: crate::leanh::LeanStringObject<
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
static mut l_Lean_Meta_Grind_Action_run___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Action_run___lam__0___closed__2_value: crate::leanh::LeanStringObject<
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
static mut l_Lean_Meta_Grind_Action_run___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Action_run___lam__0___closed__3_value: crate::leanh::LeanStringObject<
    6,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [71, 114, 105, 110, 100, 0],
};
static mut l_Lean_Meta_Grind_Action_run___lam__0___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Action_run___lam__0___closed__4_value: crate::leanh::LeanStringObject<
    6,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [115, 111, 114, 114, 121, 0],
};
static mut l_Lean_Meta_Grind_Action_run___lam__0___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Action_run___lam__0___closed__5_value_aux_0: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Action_run___lam__0___closed__5_value_aux_1: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__5_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Action_run___lam__0___closed__5_value_aux_2: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__5_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Action_run___lam__0___closed__5_value_aux_3: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__5_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__3_value)
            as *mut crate::leanh::LeanObject,
        3168557723425139092 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Action_run___lam__0___closed__5_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__5_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__4_value)
            as *mut crate::leanh::LeanObject,
        12610174047474239361 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Action_run___lam__0___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Action_run___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Grind_Action_run___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 11,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Grind_Action_run___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Action_mkGrindStep___closed__0_value: crate::leanh::LeanStringObject<
    10,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [103, 114, 105, 110, 100, 83, 116, 101, 112, 0],
};
static mut l_Lean_Meta_Grind_Action_mkGrindStep___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindStep___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Action_mkGrindStep___closed__1_value_aux_0: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Action_mkGrindStep___closed__1_value_aux_1: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindStep___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Action_mkGrindStep___closed__1_value_aux_2: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindStep___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Action_mkGrindStep___closed__1_value_aux_3: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindStep___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__3_value)
            as *mut crate::leanh::LeanObject,
        3168557723425139092 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Action_mkGrindStep___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindStep___closed__1_value_aux_3)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindStep___closed__0_value)
                as *mut crate::leanh::LeanObject,
            6321866296242073541 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Action_mkGrindStep___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindStep___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Action_mkGrindStep___closed__2_value: crate::leanh::LeanArrayObject<
    0,
> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Meta_Grind_Action_mkGrindStep___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindStep___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Action_mkGrindStep___closed__3_value: crate::leanh::LeanStringObject<
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
    m_data: [110, 117, 108, 108, 0],
};
static mut l_Lean_Meta_Grind_Action_mkGrindStep___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindStep___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Action_mkGrindStep___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindStep___closed__3_value)
                as *mut crate::leanh::LeanObject,
            9855511589286918680 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Action_mkGrindStep___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindStep___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Action_mkGrindStep___closed__5_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 1,
        },
        m_objs: [
            (((2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindStep___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindStep___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Action_mkGrindStep___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindStep___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Action_mkGrindSeq___closed__0_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Meta_Grind_Action_mkGrindSeq___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Action_mkGrindSeq___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 1,
        },
        m_objs: [
            (((2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindStep___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Action_mkGrindSeq___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Action_mkGrindSeq___closed__2_value: crate::leanh::LeanStringObject<
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
    m_data: [103, 114, 105, 110, 100, 83, 101, 113, 0],
};
static mut l_Lean_Meta_Grind_Action_mkGrindSeq___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Action_mkGrindSeq___closed__3_value_aux_0: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Action_mkGrindSeq___closed__3_value_aux_1: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__3_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Action_mkGrindSeq___closed__3_value_aux_2: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__3_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Action_mkGrindSeq___closed__3_value_aux_3: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__3_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__3_value)
            as *mut crate::leanh::LeanObject,
        3168557723425139092 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Action_mkGrindSeq___closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__3_value_aux_3)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__2_value)
                as *mut crate::leanh::LeanObject,
            12547805878916670878 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Action_mkGrindSeq___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Action_mkGrindSeq___closed__4_value: crate::leanh::LeanStringObject<
    18,
> = crate::leanh::LeanStringObject {
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
        103, 114, 105, 110, 100, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0,
    ],
};
static mut l_Lean_Meta_Grind_Action_mkGrindSeq___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Action_mkGrindSeq___closed__5_value_aux_0: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Action_mkGrindSeq___closed__5_value_aux_1: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__5_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Action_mkGrindSeq___closed__5_value_aux_2: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__5_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Action_mkGrindSeq___closed__5_value_aux_3: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__5_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__3_value)
            as *mut crate::leanh::LeanObject,
        3168557723425139092 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Action_mkGrindSeq___closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__5_value_aux_3)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__4_value)
                as *mut crate::leanh::LeanObject,
            13326625262248817187 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Action_mkGrindSeq___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__0_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 7,
    m_data: [103, 114, 105, 110, 100, 194, 183, 95, 0],
};
static mut l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__1_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__3_value)
            as *mut crate::leanh::LeanObject,
        3168557723425139092 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__1_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        12389819025714499611 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__2_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 1,
    m_data: [194, 183, 0],
};
static mut l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__3_value:
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
    m_data: [100, 111, 110, 101, 0],
};
static mut l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__4_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__4_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__4_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__4_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__4_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__4_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__3_value)
            as *mut crate::leanh::LeanObject,
        3168557723425139092 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__4_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__4_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
        4707943553582391371 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [112, 97, 114, 101, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__2_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__3_value) as *mut crate::leanh::LeanObject,3168557723425139092 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__1_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__0_value) as *mut crate::leanh::LeanObject,6341562230758934095 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__3_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 107, 105, 112, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__5_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__5_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__5_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__2_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__5_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__5_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__3_value) as *mut crate::leanh::LeanObject,3168557723425139092 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__5_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__4_value) as *mut crate::leanh::LeanObject,3888978822640132046 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Action_ungroup___redArg___closed__0_value:
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
    m_data: [110, 101, 120, 116, 0],
};
static mut l_Lean_Meta_Grind_Action_ungroup___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_ungroup___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Action_ungroup___redArg___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Action_ungroup___redArg___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_ungroup___redArg___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Action_ungroup___redArg___closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_ungroup___redArg___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Action_ungroup___redArg___closed__1_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_ungroup___redArg___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__3_value)
            as *mut crate::leanh::LeanObject,
        3168557723425139092 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Action_ungroup___redArg___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_ungroup___redArg___closed__1_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_ungroup___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        7819112639170036602 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Action_ungroup___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_ungroup___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__1_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__2_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__3_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__4_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__5_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__6_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___closed__0_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__0_value:
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
        103, 101, 110, 101, 114, 97, 116, 101, 100, 32, 116, 97, 99, 116, 105, 99, 32, 99, 97, 110,
        110, 111, 116, 32, 99, 108, 111, 115, 101, 32, 116, 104, 101, 32, 103, 111, 97, 108, 0,
    ],
};
static mut l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__2_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        10, 73, 110, 105, 116, 105, 97, 108, 32, 103, 111, 97, 108, 10, 0,
    ],
};
static mut l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Action_mbtc___closed__0_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [109, 98, 116, 99, 0],
    };
static mut l_Lean_Meta_Grind_Action_mbtc___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mbtc___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Action_mbtc___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Action_mbtc___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mbtc___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Action_mbtc___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mbtc___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Action_mbtc___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mbtc___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__3_value)
                as *mut crate::leanh::LeanObject,
            3168557723425139092 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Action_mbtc___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mbtc___closed__1_value_aux_3)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mbtc___closed__0_value)
                as *mut crate::leanh::LeanObject,
            17215256822346630302 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Action_mbtc___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mbtc___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Grind_ActionResult_toMessageData_spec__1(
    mut v_a_2850_: *mut crate::leanh::LeanObject,
    mut v_a_2851_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2857_: u8 = 0;
    let mut v_mvarId_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2863_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_2850_) == 0 {
                    v___x_2852_ = l_List_reverse___redArg(v_a_2851_);
                    return v___x_2852_;
                } else {
                    v_head_2853_ = crate::leanh::lean_ctor_get(v_a_2850_, 0);
                    v_tail_2854_ = crate::leanh::lean_ctor_get(v_a_2850_, 1);
                    v_isSharedCheck_2863_ = (!crate::leanh::lean_is_exclusive(v_a_2850_)) as u8;
                    if v_isSharedCheck_2863_ == 0 {
                        v___x_2856_ = v_a_2850_;
                        v_isShared_2857_ = v_isSharedCheck_2863_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2854_);
                        crate::leanh::lean_inc(v_head_2853_);
                        crate::leanh::lean_dec(v_a_2850_);
                        v___x_2856_ = crate::leanh::lean_box(0);
                        v_isShared_2857_ = v_isSharedCheck_2863_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_mvarId_2858_ = crate::leanh::lean_ctor_get(v_head_2853_, 1);
                crate::leanh::lean_inc(v_mvarId_2858_);
                crate::leanh::lean_dec(v_head_2853_);
                if v_isShared_2857_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2856_, 1, v_a_2851_);
                    crate::leanh::lean_ctor_set(v___x_2856_, 0, v_mvarId_2858_);
                    v___x_2860_ = v___x_2856_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2862_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2862_, 0, v_mvarId_2858_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2862_, 1, v_a_2851_);
                    v___x_2860_ = v_reuseFailAlloc_2862_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_2850_ = v_tail_2854_;
                v_a_2851_ = v___x_2860_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Grind_ActionResult_toMessageData_spec__0(
    mut v_a_2864_: *mut crate::leanh::LeanObject,
    mut v_a_2865_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2871_: u8 = 0;
    let mut v___x_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2877_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_2864_) == 0 {
                    v___x_2866_ = l_List_reverse___redArg(v_a_2865_);
                    return v___x_2866_;
                } else {
                    v_head_2867_ = crate::leanh::lean_ctor_get(v_a_2864_, 0);
                    v_tail_2868_ = crate::leanh::lean_ctor_get(v_a_2864_, 1);
                    v_isSharedCheck_2877_ = (!crate::leanh::lean_is_exclusive(v_a_2864_)) as u8;
                    if v_isSharedCheck_2877_ == 0 {
                        v___x_2870_ = v_a_2864_;
                        v_isShared_2871_ = v_isSharedCheck_2877_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2868_);
                        crate::leanh::lean_inc(v_head_2867_);
                        crate::leanh::lean_dec(v_a_2864_);
                        v___x_2870_ = crate::leanh::lean_box(0);
                        v_isShared_2871_ = v_isSharedCheck_2877_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2872_ = l_Lean_MessageData_ofSyntax(v_head_2867_);
                if v_isShared_2871_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2870_, 1, v_a_2865_);
                    crate::leanh::lean_ctor_set(v___x_2870_, 0, v___x_2872_);
                    v___x_2874_ = v___x_2870_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2876_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2876_, 0, v___x_2872_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2876_, 1, v_a_2865_);
                    v___x_2874_ = v_reuseFailAlloc_2876_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_2864_ = v_tail_2868_;
                v_a_2865_ = v___x_2874_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Grind_ActionResult_toMessageData_spec__2(
    mut v_a_2878_: *mut crate::leanh::LeanObject,
    mut v_a_2879_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2885_: u8 = 0;
    let mut v___x_2886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2891_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_2878_) == 0 {
                    v___x_2880_ = l_List_reverse___redArg(v_a_2879_);
                    return v___x_2880_;
                } else {
                    v_head_2881_ = crate::leanh::lean_ctor_get(v_a_2878_, 0);
                    v_tail_2882_ = crate::leanh::lean_ctor_get(v_a_2878_, 1);
                    v_isSharedCheck_2891_ = (!crate::leanh::lean_is_exclusive(v_a_2878_)) as u8;
                    if v_isSharedCheck_2891_ == 0 {
                        v___x_2884_ = v_a_2878_;
                        v_isShared_2885_ = v_isSharedCheck_2891_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2882_);
                        crate::leanh::lean_inc(v_head_2881_);
                        crate::leanh::lean_dec(v_a_2878_);
                        v___x_2884_ = crate::leanh::lean_box(0);
                        v_isShared_2885_ = v_isSharedCheck_2891_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2886_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2886_, 0, v_head_2881_);
                if v_isShared_2885_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2884_, 1, v_a_2879_);
                    crate::leanh::lean_ctor_set(v___x_2884_, 0, v___x_2886_);
                    v___x_2888_ = v___x_2884_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2890_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2890_, 0, v___x_2886_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2890_, 1, v_a_2879_);
                    v___x_2888_ = v_reuseFailAlloc_2890_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_2878_ = v_tail_2882_;
                v_a_2879_ = v___x_2888_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Meta_Grind_ActionResult_toMessageData___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2893_ = l_Lean_Meta_Grind_ActionResult_toMessageData___closed__0;
    v___x_2894_ = l_Lean_stringToMessageData(v___x_2893_);
    return v___x_2894_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_ActionResult_toMessageData___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2896_ = l_Lean_Meta_Grind_ActionResult_toMessageData___closed__2;
    v___x_2897_ = l_Lean_stringToMessageData(v___x_2896_);
    return v___x_2897_;
}
pub unsafe fn l_Lean_Meta_Grind_ActionResult_toMessageData(
    mut v_x_2898_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2898_) == 0 {
        let mut v_seq_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_seq_2899_ = crate::leanh::lean_ctor_get(v_x_2898_, 0);
        crate::leanh::lean_inc(v_seq_2899_);
        crate::leanh::lean_dec_ref_known(v_x_2898_, 1);
        v___x_2900_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_ActionResult_toMessageData___closed__1),
            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_ActionResult_toMessageData___closed__1_once),
            _init_l_Lean_Meta_Grind_ActionResult_toMessageData___closed__1,
        );
        v___x_2901_ = crate::leanh::lean_box(0);
        v___x_2902_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_ActionResult_toMessageData_spec__0(
            v_seq_2899_,
            v___x_2901_,
        );
        v___x_2903_ = l_Lean_MessageData_ofList(v___x_2902_);
        v___x_2904_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2904_, 0, v___x_2900_);
        crate::leanh::lean_ctor_set(v___x_2904_, 1, v___x_2903_);
        return v___x_2904_;
    } else {
        let mut v_gs_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_gs_2905_ = crate::leanh::lean_ctor_get(v_x_2898_, 0);
        crate::leanh::lean_inc(v_gs_2905_);
        crate::leanh::lean_dec_ref_known(v_x_2898_, 1);
        v___x_2906_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_ActionResult_toMessageData___closed__3),
            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_ActionResult_toMessageData___closed__3_once),
            _init_l_Lean_Meta_Grind_ActionResult_toMessageData___closed__3,
        );
        v___x_2907_ = crate::leanh::lean_box(0);
        v___x_2908_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_ActionResult_toMessageData_spec__1(
            v_gs_2905_,
            v___x_2907_,
        );
        v___x_2909_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_ActionResult_toMessageData_spec__2(
            v___x_2908_,
            v___x_2907_,
        );
        v___x_2910_ = l_Lean_MessageData_ofList(v___x_2909_);
        v___x_2911_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2911_, 0, v___x_2906_);
        crate::leanh::lean_ctor_set(v___x_2911_, 1, v___x_2910_);
        return v___x_2911_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Action_skip___redArg(
    mut v_goal_2914_: *mut crate::leanh::LeanObject,
    mut v_kp_2915_: *mut crate::leanh::LeanObject,
    mut v_a_2916_: *mut crate::leanh::LeanObject,
    mut v_a_2917_: *mut crate::leanh::LeanObject,
    mut v_a_2918_: *mut crate::leanh::LeanObject,
    mut v_a_2919_: *mut crate::leanh::LeanObject,
    mut v_a_2920_: *mut crate::leanh::LeanObject,
    mut v_a_2921_: *mut crate::leanh::LeanObject,
    mut v_a_2922_: *mut crate::leanh::LeanObject,
    mut v_a_2923_: *mut crate::leanh::LeanObject,
    mut v_a_2924_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_2924_);
    crate::leanh::lean_inc_ref(v_a_2923_);
    crate::leanh::lean_inc(v_a_2922_);
    crate::leanh::lean_inc_ref(v_a_2921_);
    crate::leanh::lean_inc(v_a_2920_);
    crate::leanh::lean_inc_ref(v_a_2919_);
    crate::leanh::lean_inc(v_a_2918_);
    crate::leanh::lean_inc_ref(v_a_2917_);
    crate::leanh::lean_inc(v_a_2916_);
    v___x_2926_ = crate::leanh::lean_apply_11(
        v_kp_2915_,
        v_goal_2914_,
        v_a_2916_,
        v_a_2917_,
        v_a_2918_,
        v_a_2919_,
        v_a_2920_,
        v_a_2921_,
        v_a_2922_,
        v_a_2923_,
        v_a_2924_,
        crate::leanh::lean_box(0),
    );
    return v___x_2926_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_skip___redArg___boxed(
    mut v_goal_2927_: *mut crate::leanh::LeanObject,
    mut v_kp_2928_: *mut crate::leanh::LeanObject,
    mut v_a_2929_: *mut crate::leanh::LeanObject,
    mut v_a_2930_: *mut crate::leanh::LeanObject,
    mut v_a_2931_: *mut crate::leanh::LeanObject,
    mut v_a_2932_: *mut crate::leanh::LeanObject,
    mut v_a_2933_: *mut crate::leanh::LeanObject,
    mut v_a_2934_: *mut crate::leanh::LeanObject,
    mut v_a_2935_: *mut crate::leanh::LeanObject,
    mut v_a_2936_: *mut crate::leanh::LeanObject,
    mut v_a_2937_: *mut crate::leanh::LeanObject,
    mut v_a_2938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2939_ = l_Lean_Meta_Grind_Action_skip___redArg(
        v_goal_2927_,
        v_kp_2928_,
        v_a_2929_,
        v_a_2930_,
        v_a_2931_,
        v_a_2932_,
        v_a_2933_,
        v_a_2934_,
        v_a_2935_,
        v_a_2936_,
        v_a_2937_,
    );
    crate::leanh::lean_dec(v_a_2937_);
    crate::leanh::lean_dec_ref(v_a_2936_);
    crate::leanh::lean_dec(v_a_2935_);
    crate::leanh::lean_dec_ref(v_a_2934_);
    crate::leanh::lean_dec(v_a_2933_);
    crate::leanh::lean_dec_ref(v_a_2932_);
    crate::leanh::lean_dec(v_a_2931_);
    crate::leanh::lean_dec_ref(v_a_2930_);
    crate::leanh::lean_dec(v_a_2929_);
    return v_res_2939_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_skip(
    mut v_goal_2940_: *mut crate::leanh::LeanObject,
    mut v_x_2941_: *mut crate::leanh::LeanObject,
    mut v_kp_2942_: *mut crate::leanh::LeanObject,
    mut v_a_2943_: *mut crate::leanh::LeanObject,
    mut v_a_2944_: *mut crate::leanh::LeanObject,
    mut v_a_2945_: *mut crate::leanh::LeanObject,
    mut v_a_2946_: *mut crate::leanh::LeanObject,
    mut v_a_2947_: *mut crate::leanh::LeanObject,
    mut v_a_2948_: *mut crate::leanh::LeanObject,
    mut v_a_2949_: *mut crate::leanh::LeanObject,
    mut v_a_2950_: *mut crate::leanh::LeanObject,
    mut v_a_2951_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_2951_);
    crate::leanh::lean_inc_ref(v_a_2950_);
    crate::leanh::lean_inc(v_a_2949_);
    crate::leanh::lean_inc_ref(v_a_2948_);
    crate::leanh::lean_inc(v_a_2947_);
    crate::leanh::lean_inc_ref(v_a_2946_);
    crate::leanh::lean_inc(v_a_2945_);
    crate::leanh::lean_inc_ref(v_a_2944_);
    crate::leanh::lean_inc(v_a_2943_);
    v___x_2953_ = crate::leanh::lean_apply_11(
        v_kp_2942_,
        v_goal_2940_,
        v_a_2943_,
        v_a_2944_,
        v_a_2945_,
        v_a_2946_,
        v_a_2947_,
        v_a_2948_,
        v_a_2949_,
        v_a_2950_,
        v_a_2951_,
        crate::leanh::lean_box(0),
    );
    return v___x_2953_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_skip___boxed(
    mut v_goal_2954_: *mut crate::leanh::LeanObject,
    mut v_x_2955_: *mut crate::leanh::LeanObject,
    mut v_kp_2956_: *mut crate::leanh::LeanObject,
    mut v_a_2957_: *mut crate::leanh::LeanObject,
    mut v_a_2958_: *mut crate::leanh::LeanObject,
    mut v_a_2959_: *mut crate::leanh::LeanObject,
    mut v_a_2960_: *mut crate::leanh::LeanObject,
    mut v_a_2961_: *mut crate::leanh::LeanObject,
    mut v_a_2962_: *mut crate::leanh::LeanObject,
    mut v_a_2963_: *mut crate::leanh::LeanObject,
    mut v_a_2964_: *mut crate::leanh::LeanObject,
    mut v_a_2965_: *mut crate::leanh::LeanObject,
    mut v_a_2966_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2967_ = l_Lean_Meta_Grind_Action_skip(
        v_goal_2954_,
        v_x_2955_,
        v_kp_2956_,
        v_a_2957_,
        v_a_2958_,
        v_a_2959_,
        v_a_2960_,
        v_a_2961_,
        v_a_2962_,
        v_a_2963_,
        v_a_2964_,
        v_a_2965_,
    );
    crate::leanh::lean_dec(v_a_2965_);
    crate::leanh::lean_dec_ref(v_a_2964_);
    crate::leanh::lean_dec(v_a_2963_);
    crate::leanh::lean_dec_ref(v_a_2962_);
    crate::leanh::lean_dec(v_a_2961_);
    crate::leanh::lean_dec_ref(v_a_2960_);
    crate::leanh::lean_dec(v_a_2959_);
    crate::leanh::lean_dec_ref(v_a_2958_);
    crate::leanh::lean_dec(v_a_2957_);
    crate::leanh::lean_dec_ref(v_x_2955_);
    return v_res_2967_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_done___redArg(
    mut v_goal_2970_: *mut crate::leanh::LeanObject,
    mut v_kna_2971_: *mut crate::leanh::LeanObject,
    mut v_a_2972_: *mut crate::leanh::LeanObject,
    mut v_a_2973_: *mut crate::leanh::LeanObject,
    mut v_a_2974_: *mut crate::leanh::LeanObject,
    mut v_a_2975_: *mut crate::leanh::LeanObject,
    mut v_a_2976_: *mut crate::leanh::LeanObject,
    mut v_a_2977_: *mut crate::leanh::LeanObject,
    mut v_a_2978_: *mut crate::leanh::LeanObject,
    mut v_a_2979_: *mut crate::leanh::LeanObject,
    mut v_a_2980_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toGoalState_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inconsistent_2983_: u8 = 0;
    v_toGoalState_2982_ = crate::leanh::lean_ctor_get(v_goal_2970_, 0);
    v_inconsistent_2983_ = crate::leanh::lean_ctor_get_uint8(
        v_toGoalState_2982_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17) as u32,
    );
    if v_inconsistent_2983_ == 0 {
        let mut v___x_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc(v_a_2980_);
        crate::leanh::lean_inc_ref(v_a_2979_);
        crate::leanh::lean_inc(v_a_2978_);
        crate::leanh::lean_inc_ref(v_a_2977_);
        crate::leanh::lean_inc(v_a_2976_);
        crate::leanh::lean_inc_ref(v_a_2975_);
        crate::leanh::lean_inc(v_a_2974_);
        crate::leanh::lean_inc_ref(v_a_2973_);
        crate::leanh::lean_inc(v_a_2972_);
        v___x_2984_ = crate::leanh::lean_apply_11(
            v_kna_2971_,
            v_goal_2970_,
            v_a_2972_,
            v_a_2973_,
            v_a_2974_,
            v_a_2975_,
            v_a_2976_,
            v_a_2977_,
            v_a_2978_,
            v_a_2979_,
            v_a_2980_,
            crate::leanh::lean_box(0),
        );
        return v___x_2984_;
    } else {
        let mut v___x_2985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_kna_2971_);
        crate::leanh::lean_dec_ref(v_goal_2970_);
        v___x_2985_ = l_Lean_Meta_Grind_Action_done___redArg___closed__0;
        v___x_2986_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2986_, 0, v___x_2985_);
        return v___x_2986_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Action_done___redArg___boxed(
    mut v_goal_2987_: *mut crate::leanh::LeanObject,
    mut v_kna_2988_: *mut crate::leanh::LeanObject,
    mut v_a_2989_: *mut crate::leanh::LeanObject,
    mut v_a_2990_: *mut crate::leanh::LeanObject,
    mut v_a_2991_: *mut crate::leanh::LeanObject,
    mut v_a_2992_: *mut crate::leanh::LeanObject,
    mut v_a_2993_: *mut crate::leanh::LeanObject,
    mut v_a_2994_: *mut crate::leanh::LeanObject,
    mut v_a_2995_: *mut crate::leanh::LeanObject,
    mut v_a_2996_: *mut crate::leanh::LeanObject,
    mut v_a_2997_: *mut crate::leanh::LeanObject,
    mut v_a_2998_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2999_ = l_Lean_Meta_Grind_Action_done___redArg(
        v_goal_2987_,
        v_kna_2988_,
        v_a_2989_,
        v_a_2990_,
        v_a_2991_,
        v_a_2992_,
        v_a_2993_,
        v_a_2994_,
        v_a_2995_,
        v_a_2996_,
        v_a_2997_,
    );
    crate::leanh::lean_dec(v_a_2997_);
    crate::leanh::lean_dec_ref(v_a_2996_);
    crate::leanh::lean_dec(v_a_2995_);
    crate::leanh::lean_dec_ref(v_a_2994_);
    crate::leanh::lean_dec(v_a_2993_);
    crate::leanh::lean_dec_ref(v_a_2992_);
    crate::leanh::lean_dec(v_a_2991_);
    crate::leanh::lean_dec_ref(v_a_2990_);
    crate::leanh::lean_dec(v_a_2989_);
    return v_res_2999_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_done(
    mut v_goal_3000_: *mut crate::leanh::LeanObject,
    mut v_kna_3001_: *mut crate::leanh::LeanObject,
    mut v_x_3002_: *mut crate::leanh::LeanObject,
    mut v_a_3003_: *mut crate::leanh::LeanObject,
    mut v_a_3004_: *mut crate::leanh::LeanObject,
    mut v_a_3005_: *mut crate::leanh::LeanObject,
    mut v_a_3006_: *mut crate::leanh::LeanObject,
    mut v_a_3007_: *mut crate::leanh::LeanObject,
    mut v_a_3008_: *mut crate::leanh::LeanObject,
    mut v_a_3009_: *mut crate::leanh::LeanObject,
    mut v_a_3010_: *mut crate::leanh::LeanObject,
    mut v_a_3011_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3013_ = l_Lean_Meta_Grind_Action_done___redArg(
        v_goal_3000_,
        v_kna_3001_,
        v_a_3003_,
        v_a_3004_,
        v_a_3005_,
        v_a_3006_,
        v_a_3007_,
        v_a_3008_,
        v_a_3009_,
        v_a_3010_,
        v_a_3011_,
    );
    return v___x_3013_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_done___boxed(
    mut v_goal_3014_: *mut crate::leanh::LeanObject,
    mut v_kna_3015_: *mut crate::leanh::LeanObject,
    mut v_x_3016_: *mut crate::leanh::LeanObject,
    mut v_a_3017_: *mut crate::leanh::LeanObject,
    mut v_a_3018_: *mut crate::leanh::LeanObject,
    mut v_a_3019_: *mut crate::leanh::LeanObject,
    mut v_a_3020_: *mut crate::leanh::LeanObject,
    mut v_a_3021_: *mut crate::leanh::LeanObject,
    mut v_a_3022_: *mut crate::leanh::LeanObject,
    mut v_a_3023_: *mut crate::leanh::LeanObject,
    mut v_a_3024_: *mut crate::leanh::LeanObject,
    mut v_a_3025_: *mut crate::leanh::LeanObject,
    mut v_a_3026_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3027_ = l_Lean_Meta_Grind_Action_done(
        v_goal_3014_,
        v_kna_3015_,
        v_x_3016_,
        v_a_3017_,
        v_a_3018_,
        v_a_3019_,
        v_a_3020_,
        v_a_3021_,
        v_a_3022_,
        v_a_3023_,
        v_a_3024_,
        v_a_3025_,
    );
    crate::leanh::lean_dec(v_a_3025_);
    crate::leanh::lean_dec_ref(v_a_3024_);
    crate::leanh::lean_dec(v_a_3023_);
    crate::leanh::lean_dec_ref(v_a_3022_);
    crate::leanh::lean_dec(v_a_3021_);
    crate::leanh::lean_dec_ref(v_a_3020_);
    crate::leanh::lean_dec(v_a_3019_);
    crate::leanh::lean_dec_ref(v_a_3018_);
    crate::leanh::lean_dec(v_a_3017_);
    crate::leanh::lean_dec_ref(v_x_3016_);
    return v_res_3027_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_andThen___lam__0(
    mut v_y_3028_: *mut crate::leanh::LeanObject,
    mut v_kp_3029_: *mut crate::leanh::LeanObject,
    mut v_goal_x27_3030_: *mut crate::leanh::LeanObject,
    mut v___y_3031_: *mut crate::leanh::LeanObject,
    mut v___y_3032_: *mut crate::leanh::LeanObject,
    mut v___y_3033_: *mut crate::leanh::LeanObject,
    mut v___y_3034_: *mut crate::leanh::LeanObject,
    mut v___y_3035_: *mut crate::leanh::LeanObject,
    mut v___y_3036_: *mut crate::leanh::LeanObject,
    mut v___y_3037_: *mut crate::leanh::LeanObject,
    mut v___y_3038_: *mut crate::leanh::LeanObject,
    mut v___y_3039_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_3039_);
    crate::leanh::lean_inc_ref(v___y_3038_);
    crate::leanh::lean_inc(v___y_3037_);
    crate::leanh::lean_inc_ref(v___y_3036_);
    crate::leanh::lean_inc(v___y_3035_);
    crate::leanh::lean_inc_ref(v___y_3034_);
    crate::leanh::lean_inc(v___y_3033_);
    crate::leanh::lean_inc_ref(v___y_3032_);
    crate::leanh::lean_inc(v___y_3031_);
    crate::leanh::lean_inc_ref(v_kp_3029_);
    v___x_3041_ = crate::leanh::lean_apply_13(
        v_y_3028_,
        v_goal_x27_3030_,
        v_kp_3029_,
        v_kp_3029_,
        v___y_3031_,
        v___y_3032_,
        v___y_3033_,
        v___y_3034_,
        v___y_3035_,
        v___y_3036_,
        v___y_3037_,
        v___y_3038_,
        v___y_3039_,
        crate::leanh::lean_box(0),
    );
    return v___x_3041_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_andThen___lam__0___boxed(
    mut v_y_3042_: *mut crate::leanh::LeanObject,
    mut v_kp_3043_: *mut crate::leanh::LeanObject,
    mut v_goal_x27_3044_: *mut crate::leanh::LeanObject,
    mut v___y_3045_: *mut crate::leanh::LeanObject,
    mut v___y_3046_: *mut crate::leanh::LeanObject,
    mut v___y_3047_: *mut crate::leanh::LeanObject,
    mut v___y_3048_: *mut crate::leanh::LeanObject,
    mut v___y_3049_: *mut crate::leanh::LeanObject,
    mut v___y_3050_: *mut crate::leanh::LeanObject,
    mut v___y_3051_: *mut crate::leanh::LeanObject,
    mut v___y_3052_: *mut crate::leanh::LeanObject,
    mut v___y_3053_: *mut crate::leanh::LeanObject,
    mut v___y_3054_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3055_ = l_Lean_Meta_Grind_Action_andThen___lam__0(
        v_y_3042_,
        v_kp_3043_,
        v_goal_x27_3044_,
        v___y_3045_,
        v___y_3046_,
        v___y_3047_,
        v___y_3048_,
        v___y_3049_,
        v___y_3050_,
        v___y_3051_,
        v___y_3052_,
        v___y_3053_,
    );
    crate::leanh::lean_dec(v___y_3053_);
    crate::leanh::lean_dec_ref(v___y_3052_);
    crate::leanh::lean_dec(v___y_3051_);
    crate::leanh::lean_dec_ref(v___y_3050_);
    crate::leanh::lean_dec(v___y_3049_);
    crate::leanh::lean_dec_ref(v___y_3048_);
    crate::leanh::lean_dec(v___y_3047_);
    crate::leanh::lean_dec_ref(v___y_3046_);
    crate::leanh::lean_dec(v___y_3045_);
    return v_res_3055_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_andThen(
    mut v_x_3056_: *mut crate::leanh::LeanObject,
    mut v_y_3057_: *mut crate::leanh::LeanObject,
    mut v_goal_3058_: *mut crate::leanh::LeanObject,
    mut v_kna_3059_: *mut crate::leanh::LeanObject,
    mut v_kp_3060_: *mut crate::leanh::LeanObject,
    mut v_a_3061_: *mut crate::leanh::LeanObject,
    mut v_a_3062_: *mut crate::leanh::LeanObject,
    mut v_a_3063_: *mut crate::leanh::LeanObject,
    mut v_a_3064_: *mut crate::leanh::LeanObject,
    mut v_a_3065_: *mut crate::leanh::LeanObject,
    mut v_a_3066_: *mut crate::leanh::LeanObject,
    mut v_a_3067_: *mut crate::leanh::LeanObject,
    mut v_a_3068_: *mut crate::leanh::LeanObject,
    mut v_a_3069_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3071_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Action_andThen___lam__0___boxed as *mut core::ffi::c_void,
        13,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3071_, 0, v_y_3057_);
    crate::leanh::lean_closure_set(v___f_3071_, 1, v_kp_3060_);
    crate::leanh::lean_inc(v_a_3069_);
    crate::leanh::lean_inc_ref(v_a_3068_);
    crate::leanh::lean_inc(v_a_3067_);
    crate::leanh::lean_inc_ref(v_a_3066_);
    crate::leanh::lean_inc(v_a_3065_);
    crate::leanh::lean_inc_ref(v_a_3064_);
    crate::leanh::lean_inc(v_a_3063_);
    crate::leanh::lean_inc_ref(v_a_3062_);
    crate::leanh::lean_inc(v_a_3061_);
    v___x_3072_ = crate::leanh::lean_apply_13(
        v_x_3056_,
        v_goal_3058_,
        v_kna_3059_,
        v___f_3071_,
        v_a_3061_,
        v_a_3062_,
        v_a_3063_,
        v_a_3064_,
        v_a_3065_,
        v_a_3066_,
        v_a_3067_,
        v_a_3068_,
        v_a_3069_,
        crate::leanh::lean_box(0),
    );
    return v___x_3072_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_andThen___boxed(
    mut v_x_3073_: *mut crate::leanh::LeanObject,
    mut v_y_3074_: *mut crate::leanh::LeanObject,
    mut v_goal_3075_: *mut crate::leanh::LeanObject,
    mut v_kna_3076_: *mut crate::leanh::LeanObject,
    mut v_kp_3077_: *mut crate::leanh::LeanObject,
    mut v_a_3078_: *mut crate::leanh::LeanObject,
    mut v_a_3079_: *mut crate::leanh::LeanObject,
    mut v_a_3080_: *mut crate::leanh::LeanObject,
    mut v_a_3081_: *mut crate::leanh::LeanObject,
    mut v_a_3082_: *mut crate::leanh::LeanObject,
    mut v_a_3083_: *mut crate::leanh::LeanObject,
    mut v_a_3084_: *mut crate::leanh::LeanObject,
    mut v_a_3085_: *mut crate::leanh::LeanObject,
    mut v_a_3086_: *mut crate::leanh::LeanObject,
    mut v_a_3087_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3088_ = l_Lean_Meta_Grind_Action_andThen(
        v_x_3073_,
        v_y_3074_,
        v_goal_3075_,
        v_kna_3076_,
        v_kp_3077_,
        v_a_3078_,
        v_a_3079_,
        v_a_3080_,
        v_a_3081_,
        v_a_3082_,
        v_a_3083_,
        v_a_3084_,
        v_a_3085_,
        v_a_3086_,
    );
    crate::leanh::lean_dec(v_a_3086_);
    crate::leanh::lean_dec_ref(v_a_3085_);
    crate::leanh::lean_dec(v_a_3084_);
    crate::leanh::lean_dec_ref(v_a_3083_);
    crate::leanh::lean_dec(v_a_3082_);
    crate::leanh::lean_dec_ref(v_a_3081_);
    crate::leanh::lean_dec(v_a_3080_);
    crate::leanh::lean_dec_ref(v_a_3079_);
    crate::leanh::lean_dec(v_a_3078_);
    return v_res_3088_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_instAndThen___lam__0(
    mut v_x_3089_: *mut crate::leanh::LeanObject,
    mut v_y_3090_: *mut crate::leanh::LeanObject,
    mut v___y_3091_: *mut crate::leanh::LeanObject,
    mut v___y_3092_: *mut crate::leanh::LeanObject,
    mut v___y_3093_: *mut crate::leanh::LeanObject,
    mut v___y_3094_: *mut crate::leanh::LeanObject,
    mut v___y_3095_: *mut crate::leanh::LeanObject,
    mut v___y_3096_: *mut crate::leanh::LeanObject,
    mut v___y_3097_: *mut crate::leanh::LeanObject,
    mut v___y_3098_: *mut crate::leanh::LeanObject,
    mut v___y_3099_: *mut crate::leanh::LeanObject,
    mut v___y_3100_: *mut crate::leanh::LeanObject,
    mut v___y_3101_: *mut crate::leanh::LeanObject,
    mut v___y_3102_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3104_ = crate::leanh::lean_box(0);
    v___x_3105_ = crate::leanh::lean_apply_1(v_y_3090_, v___x_3104_);
    v___x_3106_ = l_Lean_Meta_Grind_Action_andThen(
        v_x_3089_,
        v___x_3105_,
        v___y_3091_,
        v___y_3092_,
        v___y_3093_,
        v___y_3094_,
        v___y_3095_,
        v___y_3096_,
        v___y_3097_,
        v___y_3098_,
        v___y_3099_,
        v___y_3100_,
        v___y_3101_,
        v___y_3102_,
    );
    return v___x_3106_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_instAndThen___lam__0___boxed(
    mut v_x_3107_: *mut crate::leanh::LeanObject,
    mut v_y_3108_: *mut crate::leanh::LeanObject,
    mut v___y_3109_: *mut crate::leanh::LeanObject,
    mut v___y_3110_: *mut crate::leanh::LeanObject,
    mut v___y_3111_: *mut crate::leanh::LeanObject,
    mut v___y_3112_: *mut crate::leanh::LeanObject,
    mut v___y_3113_: *mut crate::leanh::LeanObject,
    mut v___y_3114_: *mut crate::leanh::LeanObject,
    mut v___y_3115_: *mut crate::leanh::LeanObject,
    mut v___y_3116_: *mut crate::leanh::LeanObject,
    mut v___y_3117_: *mut crate::leanh::LeanObject,
    mut v___y_3118_: *mut crate::leanh::LeanObject,
    mut v___y_3119_: *mut crate::leanh::LeanObject,
    mut v___y_3120_: *mut crate::leanh::LeanObject,
    mut v___y_3121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3122_ = l_Lean_Meta_Grind_Action_instAndThen___lam__0(
        v_x_3107_,
        v_y_3108_,
        v___y_3109_,
        v___y_3110_,
        v___y_3111_,
        v___y_3112_,
        v___y_3113_,
        v___y_3114_,
        v___y_3115_,
        v___y_3116_,
        v___y_3117_,
        v___y_3118_,
        v___y_3119_,
        v___y_3120_,
    );
    crate::leanh::lean_dec(v___y_3120_);
    crate::leanh::lean_dec_ref(v___y_3119_);
    crate::leanh::lean_dec(v___y_3118_);
    crate::leanh::lean_dec_ref(v___y_3117_);
    crate::leanh::lean_dec(v___y_3116_);
    crate::leanh::lean_dec_ref(v___y_3115_);
    crate::leanh::lean_dec(v___y_3114_);
    crate::leanh::lean_dec_ref(v___y_3113_);
    crate::leanh::lean_dec(v___y_3112_);
    return v_res_3122_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_orElse___lam__0(
    mut v_y_3125_: *mut crate::leanh::LeanObject,
    mut v_kna_3126_: *mut crate::leanh::LeanObject,
    mut v_kp_3127_: *mut crate::leanh::LeanObject,
    mut v_goal_3128_: *mut crate::leanh::LeanObject,
    mut v___y_3129_: *mut crate::leanh::LeanObject,
    mut v___y_3130_: *mut crate::leanh::LeanObject,
    mut v___y_3131_: *mut crate::leanh::LeanObject,
    mut v___y_3132_: *mut crate::leanh::LeanObject,
    mut v___y_3133_: *mut crate::leanh::LeanObject,
    mut v___y_3134_: *mut crate::leanh::LeanObject,
    mut v___y_3135_: *mut crate::leanh::LeanObject,
    mut v___y_3136_: *mut crate::leanh::LeanObject,
    mut v___y_3137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_3137_);
    crate::leanh::lean_inc_ref(v___y_3136_);
    crate::leanh::lean_inc(v___y_3135_);
    crate::leanh::lean_inc_ref(v___y_3134_);
    crate::leanh::lean_inc(v___y_3133_);
    crate::leanh::lean_inc_ref(v___y_3132_);
    crate::leanh::lean_inc(v___y_3131_);
    crate::leanh::lean_inc_ref(v___y_3130_);
    crate::leanh::lean_inc(v___y_3129_);
    v___x_3139_ = crate::leanh::lean_apply_13(
        v_y_3125_,
        v_goal_3128_,
        v_kna_3126_,
        v_kp_3127_,
        v___y_3129_,
        v___y_3130_,
        v___y_3131_,
        v___y_3132_,
        v___y_3133_,
        v___y_3134_,
        v___y_3135_,
        v___y_3136_,
        v___y_3137_,
        crate::leanh::lean_box(0),
    );
    return v___x_3139_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_orElse___lam__0___boxed(
    mut v_y_3140_: *mut crate::leanh::LeanObject,
    mut v_kna_3141_: *mut crate::leanh::LeanObject,
    mut v_kp_3142_: *mut crate::leanh::LeanObject,
    mut v_goal_3143_: *mut crate::leanh::LeanObject,
    mut v___y_3144_: *mut crate::leanh::LeanObject,
    mut v___y_3145_: *mut crate::leanh::LeanObject,
    mut v___y_3146_: *mut crate::leanh::LeanObject,
    mut v___y_3147_: *mut crate::leanh::LeanObject,
    mut v___y_3148_: *mut crate::leanh::LeanObject,
    mut v___y_3149_: *mut crate::leanh::LeanObject,
    mut v___y_3150_: *mut crate::leanh::LeanObject,
    mut v___y_3151_: *mut crate::leanh::LeanObject,
    mut v___y_3152_: *mut crate::leanh::LeanObject,
    mut v___y_3153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3154_ = l_Lean_Meta_Grind_Action_orElse___lam__0(
        v_y_3140_,
        v_kna_3141_,
        v_kp_3142_,
        v_goal_3143_,
        v___y_3144_,
        v___y_3145_,
        v___y_3146_,
        v___y_3147_,
        v___y_3148_,
        v___y_3149_,
        v___y_3150_,
        v___y_3151_,
        v___y_3152_,
    );
    crate::leanh::lean_dec(v___y_3152_);
    crate::leanh::lean_dec_ref(v___y_3151_);
    crate::leanh::lean_dec(v___y_3150_);
    crate::leanh::lean_dec_ref(v___y_3149_);
    crate::leanh::lean_dec(v___y_3148_);
    crate::leanh::lean_dec_ref(v___y_3147_);
    crate::leanh::lean_dec(v___y_3146_);
    crate::leanh::lean_dec_ref(v___y_3145_);
    crate::leanh::lean_dec(v___y_3144_);
    return v_res_3154_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_orElse(
    mut v_x_3155_: *mut crate::leanh::LeanObject,
    mut v_y_3156_: *mut crate::leanh::LeanObject,
    mut v_goal_3157_: *mut crate::leanh::LeanObject,
    mut v_kna_3158_: *mut crate::leanh::LeanObject,
    mut v_kp_3159_: *mut crate::leanh::LeanObject,
    mut v_a_3160_: *mut crate::leanh::LeanObject,
    mut v_a_3161_: *mut crate::leanh::LeanObject,
    mut v_a_3162_: *mut crate::leanh::LeanObject,
    mut v_a_3163_: *mut crate::leanh::LeanObject,
    mut v_a_3164_: *mut crate::leanh::LeanObject,
    mut v_a_3165_: *mut crate::leanh::LeanObject,
    mut v_a_3166_: *mut crate::leanh::LeanObject,
    mut v_a_3167_: *mut crate::leanh::LeanObject,
    mut v_a_3168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_kp_3159_);
    v___f_3170_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Action_orElse___lam__0___boxed as *mut core::ffi::c_void,
        14,
        3,
    );
    crate::leanh::lean_closure_set(v___f_3170_, 0, v_y_3156_);
    crate::leanh::lean_closure_set(v___f_3170_, 1, v_kna_3158_);
    crate::leanh::lean_closure_set(v___f_3170_, 2, v_kp_3159_);
    crate::leanh::lean_inc(v_a_3168_);
    crate::leanh::lean_inc_ref(v_a_3167_);
    crate::leanh::lean_inc(v_a_3166_);
    crate::leanh::lean_inc_ref(v_a_3165_);
    crate::leanh::lean_inc(v_a_3164_);
    crate::leanh::lean_inc_ref(v_a_3163_);
    crate::leanh::lean_inc(v_a_3162_);
    crate::leanh::lean_inc_ref(v_a_3161_);
    crate::leanh::lean_inc(v_a_3160_);
    v___x_3171_ = crate::leanh::lean_apply_13(
        v_x_3155_,
        v_goal_3157_,
        v___f_3170_,
        v_kp_3159_,
        v_a_3160_,
        v_a_3161_,
        v_a_3162_,
        v_a_3163_,
        v_a_3164_,
        v_a_3165_,
        v_a_3166_,
        v_a_3167_,
        v_a_3168_,
        crate::leanh::lean_box(0),
    );
    return v___x_3171_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_orElse___boxed(
    mut v_x_3172_: *mut crate::leanh::LeanObject,
    mut v_y_3173_: *mut crate::leanh::LeanObject,
    mut v_goal_3174_: *mut crate::leanh::LeanObject,
    mut v_kna_3175_: *mut crate::leanh::LeanObject,
    mut v_kp_3176_: *mut crate::leanh::LeanObject,
    mut v_a_3177_: *mut crate::leanh::LeanObject,
    mut v_a_3178_: *mut crate::leanh::LeanObject,
    mut v_a_3179_: *mut crate::leanh::LeanObject,
    mut v_a_3180_: *mut crate::leanh::LeanObject,
    mut v_a_3181_: *mut crate::leanh::LeanObject,
    mut v_a_3182_: *mut crate::leanh::LeanObject,
    mut v_a_3183_: *mut crate::leanh::LeanObject,
    mut v_a_3184_: *mut crate::leanh::LeanObject,
    mut v_a_3185_: *mut crate::leanh::LeanObject,
    mut v_a_3186_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3187_ = l_Lean_Meta_Grind_Action_orElse(
        v_x_3172_,
        v_y_3173_,
        v_goal_3174_,
        v_kna_3175_,
        v_kp_3176_,
        v_a_3177_,
        v_a_3178_,
        v_a_3179_,
        v_a_3180_,
        v_a_3181_,
        v_a_3182_,
        v_a_3183_,
        v_a_3184_,
        v_a_3185_,
    );
    crate::leanh::lean_dec(v_a_3185_);
    crate::leanh::lean_dec_ref(v_a_3184_);
    crate::leanh::lean_dec(v_a_3183_);
    crate::leanh::lean_dec_ref(v_a_3182_);
    crate::leanh::lean_dec(v_a_3181_);
    crate::leanh::lean_dec_ref(v_a_3180_);
    crate::leanh::lean_dec(v_a_3179_);
    crate::leanh::lean_dec_ref(v_a_3178_);
    crate::leanh::lean_dec(v_a_3177_);
    return v_res_3187_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_instOrElse___lam__0(
    mut v_x_3188_: *mut crate::leanh::LeanObject,
    mut v_y_3189_: *mut crate::leanh::LeanObject,
    mut v___y_3190_: *mut crate::leanh::LeanObject,
    mut v___y_3191_: *mut crate::leanh::LeanObject,
    mut v___y_3192_: *mut crate::leanh::LeanObject,
    mut v___y_3193_: *mut crate::leanh::LeanObject,
    mut v___y_3194_: *mut crate::leanh::LeanObject,
    mut v___y_3195_: *mut crate::leanh::LeanObject,
    mut v___y_3196_: *mut crate::leanh::LeanObject,
    mut v___y_3197_: *mut crate::leanh::LeanObject,
    mut v___y_3198_: *mut crate::leanh::LeanObject,
    mut v___y_3199_: *mut crate::leanh::LeanObject,
    mut v___y_3200_: *mut crate::leanh::LeanObject,
    mut v___y_3201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3203_ = crate::leanh::lean_box(0);
    v___x_3204_ = crate::leanh::lean_apply_1(v_y_3189_, v___x_3203_);
    v___x_3205_ = l_Lean_Meta_Grind_Action_orElse(
        v_x_3188_,
        v___x_3204_,
        v___y_3190_,
        v___y_3191_,
        v___y_3192_,
        v___y_3193_,
        v___y_3194_,
        v___y_3195_,
        v___y_3196_,
        v___y_3197_,
        v___y_3198_,
        v___y_3199_,
        v___y_3200_,
        v___y_3201_,
    );
    return v___x_3205_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_instOrElse___lam__0___boxed(
    mut v_x_3206_: *mut crate::leanh::LeanObject,
    mut v_y_3207_: *mut crate::leanh::LeanObject,
    mut v___y_3208_: *mut crate::leanh::LeanObject,
    mut v___y_3209_: *mut crate::leanh::LeanObject,
    mut v___y_3210_: *mut crate::leanh::LeanObject,
    mut v___y_3211_: *mut crate::leanh::LeanObject,
    mut v___y_3212_: *mut crate::leanh::LeanObject,
    mut v___y_3213_: *mut crate::leanh::LeanObject,
    mut v___y_3214_: *mut crate::leanh::LeanObject,
    mut v___y_3215_: *mut crate::leanh::LeanObject,
    mut v___y_3216_: *mut crate::leanh::LeanObject,
    mut v___y_3217_: *mut crate::leanh::LeanObject,
    mut v___y_3218_: *mut crate::leanh::LeanObject,
    mut v___y_3219_: *mut crate::leanh::LeanObject,
    mut v___y_3220_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3221_ = l_Lean_Meta_Grind_Action_instOrElse___lam__0(
        v_x_3206_,
        v_y_3207_,
        v___y_3208_,
        v___y_3209_,
        v___y_3210_,
        v___y_3211_,
        v___y_3212_,
        v___y_3213_,
        v___y_3214_,
        v___y_3215_,
        v___y_3216_,
        v___y_3217_,
        v___y_3218_,
        v___y_3219_,
    );
    crate::leanh::lean_dec(v___y_3219_);
    crate::leanh::lean_dec_ref(v___y_3218_);
    crate::leanh::lean_dec(v___y_3217_);
    crate::leanh::lean_dec_ref(v___y_3216_);
    crate::leanh::lean_dec(v___y_3215_);
    crate::leanh::lean_dec_ref(v___y_3214_);
    crate::leanh::lean_dec(v___y_3213_);
    crate::leanh::lean_dec_ref(v___y_3212_);
    crate::leanh::lean_dec(v___y_3211_);
    return v_res_3221_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_loop___redArg___lam__0___boxed(
    mut v_n_3224_: *mut crate::leanh::LeanObject,
    mut v_x_3225_: *mut crate::leanh::LeanObject,
    mut v_kp_3226_: *mut crate::leanh::LeanObject,
    mut v_goal_x27_3227_: *mut crate::leanh::LeanObject,
    mut v___y_3228_: *mut crate::leanh::LeanObject,
    mut v___y_3229_: *mut crate::leanh::LeanObject,
    mut v___y_3230_: *mut crate::leanh::LeanObject,
    mut v___y_3231_: *mut crate::leanh::LeanObject,
    mut v___y_3232_: *mut crate::leanh::LeanObject,
    mut v___y_3233_: *mut crate::leanh::LeanObject,
    mut v___y_3234_: *mut crate::leanh::LeanObject,
    mut v___y_3235_: *mut crate::leanh::LeanObject,
    mut v___y_3236_: *mut crate::leanh::LeanObject,
    mut v___y_3237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3238_ = l_Lean_Meta_Grind_Action_loop___redArg___lam__0(
        v_n_3224_,
        v_x_3225_,
        v_kp_3226_,
        v_goal_x27_3227_,
        v___y_3228_,
        v___y_3229_,
        v___y_3230_,
        v___y_3231_,
        v___y_3232_,
        v___y_3233_,
        v___y_3234_,
        v___y_3235_,
        v___y_3236_,
    );
    crate::leanh::lean_dec(v___y_3236_);
    crate::leanh::lean_dec_ref(v___y_3235_);
    crate::leanh::lean_dec(v___y_3234_);
    crate::leanh::lean_dec_ref(v___y_3233_);
    crate::leanh::lean_dec(v___y_3232_);
    crate::leanh::lean_dec_ref(v___y_3231_);
    crate::leanh::lean_dec(v___y_3230_);
    crate::leanh::lean_dec_ref(v___y_3229_);
    crate::leanh::lean_dec(v___y_3228_);
    crate::leanh::lean_dec(v_n_3224_);
    return v_res_3238_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_loop___redArg(
    mut v_n_3239_: *mut crate::leanh::LeanObject,
    mut v_x_3240_: *mut crate::leanh::LeanObject,
    mut v_goal_3241_: *mut crate::leanh::LeanObject,
    mut v_kp_3242_: *mut crate::leanh::LeanObject,
    mut v_a_3243_: *mut crate::leanh::LeanObject,
    mut v_a_3244_: *mut crate::leanh::LeanObject,
    mut v_a_3245_: *mut crate::leanh::LeanObject,
    mut v_a_3246_: *mut crate::leanh::LeanObject,
    mut v_a_3247_: *mut crate::leanh::LeanObject,
    mut v_a_3248_: *mut crate::leanh::LeanObject,
    mut v_a_3249_: *mut crate::leanh::LeanObject,
    mut v_a_3250_: *mut crate::leanh::LeanObject,
    mut v_a_3251_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3261_: u8 = 0;
    let mut v___x_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: u8 = 0;
    let mut v___x_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3270_: u8 = 0;
    let mut v___x_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3274_: u8 = 0;
    let mut v_a_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3278_: u8 = 0;
    let mut v___x_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3282_: u8 = 0;
    let mut v___y_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: u8 = 0;
    let mut v___x_3287_: u8 = 0;
    let mut v___x_3288_: u8 = 0;
    let mut v_zero_3289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_3290_: u8 = 0;
    let mut v___x_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_3289_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_3290_ = lean_nat_dec_eq(v_n_3239_, v_zero_3289_);
                if v_isZero_3290_ == 1 {
                    crate::leanh::lean_dec_ref(v_x_3240_);
                    crate::leanh::lean_inc(v_a_3251_);
                    crate::leanh::lean_inc_ref(v_a_3250_);
                    crate::leanh::lean_inc(v_a_3249_);
                    crate::leanh::lean_inc_ref(v_a_3248_);
                    crate::leanh::lean_inc(v_a_3247_);
                    crate::leanh::lean_inc_ref(v_a_3246_);
                    crate::leanh::lean_inc(v_a_3245_);
                    crate::leanh::lean_inc_ref(v_a_3244_);
                    crate::leanh::lean_inc(v_a_3243_);
                    crate::leanh::lean_inc_ref(v_goal_3241_);
                    v___x_3291_ = crate::leanh::lean_apply_11(
                        v_kp_3242_,
                        v_goal_3241_,
                        v_a_3243_,
                        v_a_3244_,
                        v_a_3245_,
                        v_a_3246_,
                        v_a_3247_,
                        v_a_3248_,
                        v_a_3249_,
                        v_a_3250_,
                        v_a_3251_,
                        crate::leanh::lean_box(0),
                    );
                    v___y_3284_ = v___x_3291_;
                    state = 7;
                    continue;
                } else {
                    v_one_3292_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_3293_ = lean_nat_sub(v_n_3239_, v_one_3292_);
                    crate::leanh::lean_inc_ref(v_kp_3242_);
                    crate::leanh::lean_inc_ref(v_x_3240_);
                    v___f_3294_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Meta_Grind_Action_loop___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        14,
                        3,
                    );
                    crate::leanh::lean_closure_set(v___f_3294_, 0, v_n_3293_);
                    crate::leanh::lean_closure_set(v___f_3294_, 1, v_x_3240_);
                    crate::leanh::lean_closure_set(v___f_3294_, 2, v_kp_3242_);
                    crate::leanh::lean_inc(v_a_3251_);
                    crate::leanh::lean_inc_ref(v_a_3250_);
                    crate::leanh::lean_inc(v_a_3249_);
                    crate::leanh::lean_inc_ref(v_a_3248_);
                    crate::leanh::lean_inc(v_a_3247_);
                    crate::leanh::lean_inc_ref(v_a_3246_);
                    crate::leanh::lean_inc(v_a_3245_);
                    crate::leanh::lean_inc_ref(v_a_3244_);
                    crate::leanh::lean_inc(v_a_3243_);
                    crate::leanh::lean_inc_ref(v_goal_3241_);
                    v___x_3295_ = crate::leanh::lean_apply_13(
                        v_x_3240_,
                        v_goal_3241_,
                        v_kp_3242_,
                        v___f_3294_,
                        v_a_3243_,
                        v_a_3244_,
                        v_a_3245_,
                        v_a_3246_,
                        v_a_3247_,
                        v_a_3248_,
                        v_a_3249_,
                        v_a_3250_,
                        v_a_3251_,
                        crate::leanh::lean_box(0),
                    );
                    v___y_3284_ = v___x_3295_;
                    state = 7;
                    continue;
                }
            }
            1 => {
                v___x_3254_ = crate::leanh::lean_box(0);
                v___x_3255_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3255_, 0, v_goal_3241_);
                crate::leanh::lean_ctor_set(v___x_3255_, 1, v___x_3254_);
                v___x_3256_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3256_, 0, v___x_3255_);
                v___x_3257_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3257_, 0, v___x_3256_);
                return v___x_3257_;
            }
            2 => {
                if v___y_3261_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_3260_);
                    crate::leanh::lean_dec_ref(v_goal_3241_);
                    return v___y_3259_;
                } else {
                    crate::leanh::lean_dec_ref(v___y_3259_);
                    v___x_3262_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_3246_);
                    if crate::leanh::lean_obj_tag(v___x_3262_) == 0 {
                        v_a_3263_ = crate::leanh::lean_ctor_get(v___x_3262_, 0);
                        crate::leanh::lean_inc(v_a_3263_);
                        crate::leanh::lean_dec_ref_known(v___x_3262_, 1);
                        v___x_3264_ = (crate::leanh::lean_unbox(v_a_3263_) as u8);
                        crate::leanh::lean_dec(v_a_3263_);
                        if v___x_3264_ == 0 {
                            crate::leanh::lean_dec_ref(v___y_3260_);
                            state = 1;
                            continue;
                        } else {
                            v___x_3265_ = l_Lean_Exception_toMessageData(v___y_3260_);
                            v___x_3266_ = l_Lean_Meta_Sym_reportIssue(
                                v___x_3265_,
                                v_a_3246_,
                                v_a_3247_,
                                v_a_3248_,
                                v_a_3249_,
                                v_a_3250_,
                                v_a_3251_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_3266_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_3266_, 1);
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_goal_3241_);
                                v_a_3267_ = crate::leanh::lean_ctor_get(v___x_3266_, 0);
                                v_isSharedCheck_3274_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3266_)) as u8;
                                if v_isSharedCheck_3274_ == 0 {
                                    v___x_3269_ = v___x_3266_;
                                    v_isShared_3270_ = v_isSharedCheck_3274_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3267_);
                                    crate::leanh::lean_dec(v___x_3266_);
                                    v___x_3269_ = crate::leanh::lean_box(0);
                                    v_isShared_3270_ = v_isSharedCheck_3274_;
                                    state = 3;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___y_3260_);
                        crate::leanh::lean_dec_ref(v_goal_3241_);
                        v_a_3275_ = crate::leanh::lean_ctor_get(v___x_3262_, 0);
                        v_isSharedCheck_3282_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3262_)) as u8;
                        if v_isSharedCheck_3282_ == 0 {
                            v___x_3277_ = v___x_3262_;
                            v_isShared_3278_ = v_isSharedCheck_3282_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3275_);
                            crate::leanh::lean_dec(v___x_3262_);
                            v___x_3277_ = crate::leanh::lean_box(0);
                            v_isShared_3278_ = v_isSharedCheck_3282_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            3 => {
                if v_isShared_3270_ == 0 {
                    v___x_3272_ = v___x_3269_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3273_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3273_, 0, v_a_3267_);
                    v___x_3272_ = v_reuseFailAlloc_3273_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3272_;
            }
            5 => {
                if v_isShared_3278_ == 0 {
                    v___x_3280_ = v___x_3277_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3281_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3281_, 0, v_a_3275_);
                    v___x_3280_ = v_reuseFailAlloc_3281_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3280_;
            }
            7 => {
                if crate::leanh::lean_obj_tag(v___y_3284_) == 0 {
                    crate::leanh::lean_dec_ref(v_goal_3241_);
                    return v___y_3284_;
                } else {
                    v_a_3285_ = crate::leanh::lean_ctor_get(v___y_3284_, 0);
                    v___x_3286_ = l_Lean_Exception_isInterrupt(v_a_3285_);
                    if v___x_3286_ == 0 {
                        crate::leanh::lean_inc_n(v_a_3285_, 2);
                        v___x_3287_ = l_Lean_Exception_isMaxHeartbeat(v_a_3285_);
                        if v___x_3287_ == 0 {
                            crate::leanh::lean_inc(v_a_3285_);
                            v___x_3288_ = l_Lean_Exception_isMaxRecDepth(v_a_3285_);
                            v___y_3259_ = v___y_3284_;
                            v___y_3260_ = v_a_3285_;
                            v___y_3261_ = v___x_3288_;
                            state = 2;
                            continue;
                        } else {
                            v___y_3259_ = v___y_3284_;
                            v___y_3260_ = v_a_3285_;
                            v___y_3261_ = v___x_3287_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_goal_3241_);
                        return v___y_3284_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Action_loop___redArg___lam__0(
    mut v_n_3296_: *mut crate::leanh::LeanObject,
    mut v_x_3297_: *mut crate::leanh::LeanObject,
    mut v_kp_3298_: *mut crate::leanh::LeanObject,
    mut v_goal_x27_3299_: *mut crate::leanh::LeanObject,
    mut v___y_3300_: *mut crate::leanh::LeanObject,
    mut v___y_3301_: *mut crate::leanh::LeanObject,
    mut v___y_3302_: *mut crate::leanh::LeanObject,
    mut v___y_3303_: *mut crate::leanh::LeanObject,
    mut v___y_3304_: *mut crate::leanh::LeanObject,
    mut v___y_3305_: *mut crate::leanh::LeanObject,
    mut v___y_3306_: *mut crate::leanh::LeanObject,
    mut v___y_3307_: *mut crate::leanh::LeanObject,
    mut v___y_3308_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3310_ = l_Lean_Meta_Grind_Action_loop___redArg(
        v_n_3296_,
        v_x_3297_,
        v_goal_x27_3299_,
        v_kp_3298_,
        v___y_3300_,
        v___y_3301_,
        v___y_3302_,
        v___y_3303_,
        v___y_3304_,
        v___y_3305_,
        v___y_3306_,
        v___y_3307_,
        v___y_3308_,
    );
    return v___x_3310_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_loop___redArg___boxed(
    mut v_n_3311_: *mut crate::leanh::LeanObject,
    mut v_x_3312_: *mut crate::leanh::LeanObject,
    mut v_goal_3313_: *mut crate::leanh::LeanObject,
    mut v_kp_3314_: *mut crate::leanh::LeanObject,
    mut v_a_3315_: *mut crate::leanh::LeanObject,
    mut v_a_3316_: *mut crate::leanh::LeanObject,
    mut v_a_3317_: *mut crate::leanh::LeanObject,
    mut v_a_3318_: *mut crate::leanh::LeanObject,
    mut v_a_3319_: *mut crate::leanh::LeanObject,
    mut v_a_3320_: *mut crate::leanh::LeanObject,
    mut v_a_3321_: *mut crate::leanh::LeanObject,
    mut v_a_3322_: *mut crate::leanh::LeanObject,
    mut v_a_3323_: *mut crate::leanh::LeanObject,
    mut v_a_3324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3325_ = l_Lean_Meta_Grind_Action_loop___redArg(
        v_n_3311_,
        v_x_3312_,
        v_goal_3313_,
        v_kp_3314_,
        v_a_3315_,
        v_a_3316_,
        v_a_3317_,
        v_a_3318_,
        v_a_3319_,
        v_a_3320_,
        v_a_3321_,
        v_a_3322_,
        v_a_3323_,
    );
    crate::leanh::lean_dec(v_a_3323_);
    crate::leanh::lean_dec_ref(v_a_3322_);
    crate::leanh::lean_dec(v_a_3321_);
    crate::leanh::lean_dec_ref(v_a_3320_);
    crate::leanh::lean_dec(v_a_3319_);
    crate::leanh::lean_dec_ref(v_a_3318_);
    crate::leanh::lean_dec(v_a_3317_);
    crate::leanh::lean_dec_ref(v_a_3316_);
    crate::leanh::lean_dec(v_a_3315_);
    crate::leanh::lean_dec(v_n_3311_);
    return v_res_3325_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_loop(
    mut v_n_3326_: *mut crate::leanh::LeanObject,
    mut v_x_3327_: *mut crate::leanh::LeanObject,
    mut v_goal_3328_: *mut crate::leanh::LeanObject,
    mut v_x_3329_: *mut crate::leanh::LeanObject,
    mut v_kp_3330_: *mut crate::leanh::LeanObject,
    mut v_a_3331_: *mut crate::leanh::LeanObject,
    mut v_a_3332_: *mut crate::leanh::LeanObject,
    mut v_a_3333_: *mut crate::leanh::LeanObject,
    mut v_a_3334_: *mut crate::leanh::LeanObject,
    mut v_a_3335_: *mut crate::leanh::LeanObject,
    mut v_a_3336_: *mut crate::leanh::LeanObject,
    mut v_a_3337_: *mut crate::leanh::LeanObject,
    mut v_a_3338_: *mut crate::leanh::LeanObject,
    mut v_a_3339_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3341_ = l_Lean_Meta_Grind_Action_loop___redArg(
        v_n_3326_,
        v_x_3327_,
        v_goal_3328_,
        v_kp_3330_,
        v_a_3331_,
        v_a_3332_,
        v_a_3333_,
        v_a_3334_,
        v_a_3335_,
        v_a_3336_,
        v_a_3337_,
        v_a_3338_,
        v_a_3339_,
    );
    return v___x_3341_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_loop___boxed(
    mut v_n_3342_: *mut crate::leanh::LeanObject,
    mut v_x_3343_: *mut crate::leanh::LeanObject,
    mut v_goal_3344_: *mut crate::leanh::LeanObject,
    mut v_x_3345_: *mut crate::leanh::LeanObject,
    mut v_kp_3346_: *mut crate::leanh::LeanObject,
    mut v_a_3347_: *mut crate::leanh::LeanObject,
    mut v_a_3348_: *mut crate::leanh::LeanObject,
    mut v_a_3349_: *mut crate::leanh::LeanObject,
    mut v_a_3350_: *mut crate::leanh::LeanObject,
    mut v_a_3351_: *mut crate::leanh::LeanObject,
    mut v_a_3352_: *mut crate::leanh::LeanObject,
    mut v_a_3353_: *mut crate::leanh::LeanObject,
    mut v_a_3354_: *mut crate::leanh::LeanObject,
    mut v_a_3355_: *mut crate::leanh::LeanObject,
    mut v_a_3356_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3357_ = l_Lean_Meta_Grind_Action_loop(
        v_n_3342_,
        v_x_3343_,
        v_goal_3344_,
        v_x_3345_,
        v_kp_3346_,
        v_a_3347_,
        v_a_3348_,
        v_a_3349_,
        v_a_3350_,
        v_a_3351_,
        v_a_3352_,
        v_a_3353_,
        v_a_3354_,
        v_a_3355_,
    );
    crate::leanh::lean_dec(v_a_3355_);
    crate::leanh::lean_dec_ref(v_a_3354_);
    crate::leanh::lean_dec(v_a_3353_);
    crate::leanh::lean_dec_ref(v_a_3352_);
    crate::leanh::lean_dec(v_a_3351_);
    crate::leanh::lean_dec_ref(v_a_3350_);
    crate::leanh::lean_dec(v_a_3349_);
    crate::leanh::lean_dec_ref(v_a_3348_);
    crate::leanh::lean_dec(v_a_3347_);
    crate::leanh::lean_dec_ref(v_x_3345_);
    crate::leanh::lean_dec(v_n_3342_);
    return v_res_3357_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_loopRef___redArg___lam__0___boxed(
    mut v_n_3358_: *mut crate::leanh::LeanObject,
    mut v_x_3359_: *mut crate::leanh::LeanObject,
    mut v_kp_3360_: *mut crate::leanh::LeanObject,
    mut v_goal_x27_3361_: *mut crate::leanh::LeanObject,
    mut v___y_3362_: *mut crate::leanh::LeanObject,
    mut v___y_3363_: *mut crate::leanh::LeanObject,
    mut v___y_3364_: *mut crate::leanh::LeanObject,
    mut v___y_3365_: *mut crate::leanh::LeanObject,
    mut v___y_3366_: *mut crate::leanh::LeanObject,
    mut v___y_3367_: *mut crate::leanh::LeanObject,
    mut v___y_3368_: *mut crate::leanh::LeanObject,
    mut v___y_3369_: *mut crate::leanh::LeanObject,
    mut v___y_3370_: *mut crate::leanh::LeanObject,
    mut v___y_3371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3372_ = l_Lean_Meta_Grind_Action_loopRef___redArg___lam__0(
        v_n_3358_,
        v_x_3359_,
        v_kp_3360_,
        v_goal_x27_3361_,
        v___y_3362_,
        v___y_3363_,
        v___y_3364_,
        v___y_3365_,
        v___y_3366_,
        v___y_3367_,
        v___y_3368_,
        v___y_3369_,
        v___y_3370_,
    );
    crate::leanh::lean_dec(v___y_3370_);
    crate::leanh::lean_dec_ref(v___y_3369_);
    crate::leanh::lean_dec(v___y_3368_);
    crate::leanh::lean_dec_ref(v___y_3367_);
    crate::leanh::lean_dec(v___y_3366_);
    crate::leanh::lean_dec_ref(v___y_3365_);
    crate::leanh::lean_dec(v___y_3364_);
    crate::leanh::lean_dec_ref(v___y_3363_);
    crate::leanh::lean_dec(v___y_3362_);
    crate::leanh::lean_dec(v_n_3358_);
    return v_res_3372_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_loopRef___redArg(
    mut v_n_3373_: *mut crate::leanh::LeanObject,
    mut v_x_3374_: *mut crate::leanh::LeanObject,
    mut v_goal_3375_: *mut crate::leanh::LeanObject,
    mut v_kp_3376_: *mut crate::leanh::LeanObject,
    mut v_a_3377_: *mut crate::leanh::LeanObject,
    mut v_a_3378_: *mut crate::leanh::LeanObject,
    mut v_a_3379_: *mut crate::leanh::LeanObject,
    mut v_a_3380_: *mut crate::leanh::LeanObject,
    mut v_a_3381_: *mut crate::leanh::LeanObject,
    mut v_a_3382_: *mut crate::leanh::LeanObject,
    mut v_a_3383_: *mut crate::leanh::LeanObject,
    mut v_a_3384_: *mut crate::leanh::LeanObject,
    mut v_a_3385_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_3387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_3388_: u8 = 0;
    v_zero_3387_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_3388_ = lean_nat_dec_eq(v_n_3373_, v_zero_3387_);
    if v_isZero_3388_ == 1 {
        let mut v___x_3389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_x_3374_);
        crate::leanh::lean_inc(v_a_3385_);
        crate::leanh::lean_inc_ref(v_a_3384_);
        crate::leanh::lean_inc(v_a_3383_);
        crate::leanh::lean_inc_ref(v_a_3382_);
        crate::leanh::lean_inc(v_a_3381_);
        crate::leanh::lean_inc_ref(v_a_3380_);
        crate::leanh::lean_inc(v_a_3379_);
        crate::leanh::lean_inc_ref(v_a_3378_);
        crate::leanh::lean_inc(v_a_3377_);
        v___x_3389_ = crate::leanh::lean_apply_11(
            v_kp_3376_,
            v_goal_3375_,
            v_a_3377_,
            v_a_3378_,
            v_a_3379_,
            v_a_3380_,
            v_a_3381_,
            v_a_3382_,
            v_a_3383_,
            v_a_3384_,
            v_a_3385_,
            crate::leanh::lean_box(0),
        );
        return v___x_3389_;
    } else {
        let mut v_one_3390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_one_3390_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_3391_ = lean_nat_sub(v_n_3373_, v_one_3390_);
        crate::leanh::lean_inc_ref(v_kp_3376_);
        crate::leanh::lean_inc_ref(v_x_3374_);
        v___f_3392_ = crate::leanh::lean_alloc_closure(
            l_Lean_Meta_Grind_Action_loopRef___redArg___lam__0___boxed as *mut core::ffi::c_void,
            14,
            3,
        );
        crate::leanh::lean_closure_set(v___f_3392_, 0, v_n_3391_);
        crate::leanh::lean_closure_set(v___f_3392_, 1, v_x_3374_);
        crate::leanh::lean_closure_set(v___f_3392_, 2, v_kp_3376_);
        crate::leanh::lean_inc(v_a_3385_);
        crate::leanh::lean_inc_ref(v_a_3384_);
        crate::leanh::lean_inc(v_a_3383_);
        crate::leanh::lean_inc_ref(v_a_3382_);
        crate::leanh::lean_inc(v_a_3381_);
        crate::leanh::lean_inc_ref(v_a_3380_);
        crate::leanh::lean_inc(v_a_3379_);
        crate::leanh::lean_inc_ref(v_a_3378_);
        crate::leanh::lean_inc(v_a_3377_);
        v___x_3393_ = crate::leanh::lean_apply_13(
            v_x_3374_,
            v_goal_3375_,
            v_kp_3376_,
            v___f_3392_,
            v_a_3377_,
            v_a_3378_,
            v_a_3379_,
            v_a_3380_,
            v_a_3381_,
            v_a_3382_,
            v_a_3383_,
            v_a_3384_,
            v_a_3385_,
            crate::leanh::lean_box(0),
        );
        return v___x_3393_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Action_loopRef___redArg___lam__0(
    mut v_n_3394_: *mut crate::leanh::LeanObject,
    mut v_x_3395_: *mut crate::leanh::LeanObject,
    mut v_kp_3396_: *mut crate::leanh::LeanObject,
    mut v_goal_x27_3397_: *mut crate::leanh::LeanObject,
    mut v___y_3398_: *mut crate::leanh::LeanObject,
    mut v___y_3399_: *mut crate::leanh::LeanObject,
    mut v___y_3400_: *mut crate::leanh::LeanObject,
    mut v___y_3401_: *mut crate::leanh::LeanObject,
    mut v___y_3402_: *mut crate::leanh::LeanObject,
    mut v___y_3403_: *mut crate::leanh::LeanObject,
    mut v___y_3404_: *mut crate::leanh::LeanObject,
    mut v___y_3405_: *mut crate::leanh::LeanObject,
    mut v___y_3406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3408_ = l_Lean_Meta_Grind_Action_loopRef___redArg(
        v_n_3394_,
        v_x_3395_,
        v_goal_x27_3397_,
        v_kp_3396_,
        v___y_3398_,
        v___y_3399_,
        v___y_3400_,
        v___y_3401_,
        v___y_3402_,
        v___y_3403_,
        v___y_3404_,
        v___y_3405_,
        v___y_3406_,
    );
    return v___x_3408_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_loopRef___redArg___boxed(
    mut v_n_3409_: *mut crate::leanh::LeanObject,
    mut v_x_3410_: *mut crate::leanh::LeanObject,
    mut v_goal_3411_: *mut crate::leanh::LeanObject,
    mut v_kp_3412_: *mut crate::leanh::LeanObject,
    mut v_a_3413_: *mut crate::leanh::LeanObject,
    mut v_a_3414_: *mut crate::leanh::LeanObject,
    mut v_a_3415_: *mut crate::leanh::LeanObject,
    mut v_a_3416_: *mut crate::leanh::LeanObject,
    mut v_a_3417_: *mut crate::leanh::LeanObject,
    mut v_a_3418_: *mut crate::leanh::LeanObject,
    mut v_a_3419_: *mut crate::leanh::LeanObject,
    mut v_a_3420_: *mut crate::leanh::LeanObject,
    mut v_a_3421_: *mut crate::leanh::LeanObject,
    mut v_a_3422_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3423_ = l_Lean_Meta_Grind_Action_loopRef___redArg(
        v_n_3409_,
        v_x_3410_,
        v_goal_3411_,
        v_kp_3412_,
        v_a_3413_,
        v_a_3414_,
        v_a_3415_,
        v_a_3416_,
        v_a_3417_,
        v_a_3418_,
        v_a_3419_,
        v_a_3420_,
        v_a_3421_,
    );
    crate::leanh::lean_dec(v_a_3421_);
    crate::leanh::lean_dec_ref(v_a_3420_);
    crate::leanh::lean_dec(v_a_3419_);
    crate::leanh::lean_dec_ref(v_a_3418_);
    crate::leanh::lean_dec(v_a_3417_);
    crate::leanh::lean_dec_ref(v_a_3416_);
    crate::leanh::lean_dec(v_a_3415_);
    crate::leanh::lean_dec_ref(v_a_3414_);
    crate::leanh::lean_dec(v_a_3413_);
    crate::leanh::lean_dec(v_n_3409_);
    return v_res_3423_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_loopRef(
    mut v_n_3424_: *mut crate::leanh::LeanObject,
    mut v_x_3425_: *mut crate::leanh::LeanObject,
    mut v_goal_3426_: *mut crate::leanh::LeanObject,
    mut v_x_3427_: *mut crate::leanh::LeanObject,
    mut v_kp_3428_: *mut crate::leanh::LeanObject,
    mut v_a_3429_: *mut crate::leanh::LeanObject,
    mut v_a_3430_: *mut crate::leanh::LeanObject,
    mut v_a_3431_: *mut crate::leanh::LeanObject,
    mut v_a_3432_: *mut crate::leanh::LeanObject,
    mut v_a_3433_: *mut crate::leanh::LeanObject,
    mut v_a_3434_: *mut crate::leanh::LeanObject,
    mut v_a_3435_: *mut crate::leanh::LeanObject,
    mut v_a_3436_: *mut crate::leanh::LeanObject,
    mut v_a_3437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3439_ = l_Lean_Meta_Grind_Action_loopRef___redArg(
        v_n_3424_,
        v_x_3425_,
        v_goal_3426_,
        v_kp_3428_,
        v_a_3429_,
        v_a_3430_,
        v_a_3431_,
        v_a_3432_,
        v_a_3433_,
        v_a_3434_,
        v_a_3435_,
        v_a_3436_,
        v_a_3437_,
    );
    return v___x_3439_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_loopRef___boxed(
    mut v_n_3440_: *mut crate::leanh::LeanObject,
    mut v_x_3441_: *mut crate::leanh::LeanObject,
    mut v_goal_3442_: *mut crate::leanh::LeanObject,
    mut v_x_3443_: *mut crate::leanh::LeanObject,
    mut v_kp_3444_: *mut crate::leanh::LeanObject,
    mut v_a_3445_: *mut crate::leanh::LeanObject,
    mut v_a_3446_: *mut crate::leanh::LeanObject,
    mut v_a_3447_: *mut crate::leanh::LeanObject,
    mut v_a_3448_: *mut crate::leanh::LeanObject,
    mut v_a_3449_: *mut crate::leanh::LeanObject,
    mut v_a_3450_: *mut crate::leanh::LeanObject,
    mut v_a_3451_: *mut crate::leanh::LeanObject,
    mut v_a_3452_: *mut crate::leanh::LeanObject,
    mut v_a_3453_: *mut crate::leanh::LeanObject,
    mut v_a_3454_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3455_ = l_Lean_Meta_Grind_Action_loopRef(
        v_n_3440_,
        v_x_3441_,
        v_goal_3442_,
        v_x_3443_,
        v_kp_3444_,
        v_a_3445_,
        v_a_3446_,
        v_a_3447_,
        v_a_3448_,
        v_a_3449_,
        v_a_3450_,
        v_a_3451_,
        v_a_3452_,
        v_a_3453_,
    );
    crate::leanh::lean_dec(v_a_3453_);
    crate::leanh::lean_dec_ref(v_a_3452_);
    crate::leanh::lean_dec(v_a_3451_);
    crate::leanh::lean_dec_ref(v_a_3450_);
    crate::leanh::lean_dec(v_a_3449_);
    crate::leanh::lean_dec_ref(v_a_3448_);
    crate::leanh::lean_dec(v_a_3447_);
    crate::leanh::lean_dec_ref(v_a_3446_);
    crate::leanh::lean_dec(v_a_3445_);
    crate::leanh::lean_dec_ref(v_x_3443_);
    crate::leanh::lean_dec(v_n_3440_);
    return v_res_3455_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_run___lam__0(
    mut v_goal_3467_: *mut crate::leanh::LeanObject,
    mut v___y_3468_: *mut crate::leanh::LeanObject,
    mut v___y_3469_: *mut crate::leanh::LeanObject,
    mut v___y_3470_: *mut crate::leanh::LeanObject,
    mut v___y_3471_: *mut crate::leanh::LeanObject,
    mut v___y_3472_: *mut crate::leanh::LeanObject,
    mut v___y_3473_: *mut crate::leanh::LeanObject,
    mut v___y_3474_: *mut crate::leanh::LeanObject,
    mut v___y_3475_: *mut crate::leanh::LeanObject,
    mut v___y_3476_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toGoalState_3478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inconsistent_3479_: u8 = 0;
    let mut v_mvarId_3480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3487_: u8 = 0;
    let mut v___x_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trace_3495_: u8 = 0;
    let mut v_useSorry_3496_: u8 = 0;
    let mut v___x_3498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3499_: u8 = 0;
    let mut v___x_3500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3503_: u8 = 0;
    let mut v_ref_3504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3518_: u8 = 0;
    let mut v_unused_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3523_: u8 = 0;
    let mut v___x_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3527_: u8 = 0;
    let mut v_isSharedCheck_3528_: u8 = 0;
    let mut v_unused_3529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3531_: u8 = 0;
    let mut v_a_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3535_: u8 = 0;
    let mut v___x_3537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3539_: u8 = 0;
    let mut v_a_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3543_: u8 = 0;
    let mut v___x_3545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3547_: u8 = 0;
    let mut v___x_3548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toGoalState_3478_ = crate::leanh::lean_ctor_get(v_goal_3467_, 0);
                v_inconsistent_3479_ = crate::leanh::lean_ctor_get_uint8(
                    v_toGoalState_3478_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17) as u32,
                );
                if v_inconsistent_3479_ == 0 {
                    v_mvarId_3480_ = crate::leanh::lean_ctor_get(v_goal_3467_, 1);
                    v___x_3481_ = l_Lean_Meta_Grind_getConfig___redArg(v___y_3469_);
                    if crate::leanh::lean_obj_tag(v___x_3481_) == 0 {
                        v_a_3482_ = crate::leanh::lean_ctor_get(v___x_3481_, 0);
                        crate::leanh::lean_inc(v_a_3482_);
                        crate::leanh::lean_dec_ref_known(v___x_3481_, 1);
                        v___x_3483_ = l_Lean_Meta_Grind_getConfig___redArg(v___y_3469_);
                        if crate::leanh::lean_obj_tag(v___x_3483_) == 0 {
                            v_a_3484_ = crate::leanh::lean_ctor_get(v___x_3483_, 0);
                            v_isSharedCheck_3531_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3483_)) as u8;
                            if v_isSharedCheck_3531_ == 0 {
                                v___x_3486_ = v___x_3483_;
                                v_isShared_3487_ = v_isSharedCheck_3531_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3484_);
                                crate::leanh::lean_dec(v___x_3483_);
                                v___x_3486_ = crate::leanh::lean_box(0);
                                v_isShared_3487_ = v_isSharedCheck_3531_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3482_);
                            crate::leanh::lean_dec_ref(v_goal_3467_);
                            v_a_3532_ = crate::leanh::lean_ctor_get(v___x_3483_, 0);
                            v_isSharedCheck_3539_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3483_)) as u8;
                            if v_isSharedCheck_3539_ == 0 {
                                v___x_3534_ = v___x_3483_;
                                v_isShared_3535_ = v_isSharedCheck_3539_;
                                state = 10;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3532_);
                                crate::leanh::lean_dec(v___x_3483_);
                                v___x_3534_ = crate::leanh::lean_box(0);
                                v_isShared_3535_ = v_isSharedCheck_3539_;
                                state = 10;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_goal_3467_);
                        v_a_3540_ = crate::leanh::lean_ctor_get(v___x_3481_, 0);
                        v_isSharedCheck_3547_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3481_)) as u8;
                        if v_isSharedCheck_3547_ == 0 {
                            v___x_3542_ = v___x_3481_;
                            v_isShared_3543_ = v_isSharedCheck_3547_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3540_);
                            crate::leanh::lean_dec(v___x_3481_);
                            v___x_3542_ = crate::leanh::lean_box(0);
                            v_isShared_3543_ = v_isSharedCheck_3547_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_goal_3467_);
                    v___x_3548_ = l_Lean_Meta_Grind_Action_done___redArg___closed__0;
                    v___x_3549_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3549_, 0, v___x_3548_);
                    return v___x_3549_;
                }
            }
            1 => {
                v_trace_3495_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3482_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13) as u32,
                );
                crate::leanh::lean_dec(v_a_3482_);
                if v_trace_3495_ == 0 {
                    crate::leanh::lean_dec(v_a_3484_);
                    state = 2;
                    continue;
                } else {
                    v_useSorry_3496_ = crate::leanh::lean_ctor_get_uint8(
                        v_a_3484_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 28) as u32,
                    );
                    crate::leanh::lean_dec(v_a_3484_);
                    if v_useSorry_3496_ == 0 {
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_mvarId_3480_);
                        crate::leanh::lean_del_object(v___x_3486_);
                        v_isSharedCheck_3528_ =
                            (!crate::leanh::lean_is_exclusive(v_goal_3467_)) as u8;
                        if v_isSharedCheck_3528_ == 0 {
                            v_unused_3529_ = crate::leanh::lean_ctor_get(v_goal_3467_, 1);
                            crate::leanh::lean_dec(v_unused_3529_);
                            v_unused_3530_ = crate::leanh::lean_ctor_get(v_goal_3467_, 0);
                            crate::leanh::lean_dec(v_unused_3530_);
                            v___x_3498_ = v_goal_3467_;
                            v_isShared_3499_ = v_isSharedCheck_3528_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_goal_3467_);
                            v___x_3498_ = crate::leanh::lean_box(0);
                            v_isShared_3499_ = v_isSharedCheck_3528_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v___x_3489_ = crate::leanh::lean_box(0);
                v___x_3490_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3490_, 0, v_goal_3467_);
                crate::leanh::lean_ctor_set(v___x_3490_, 1, v___x_3489_);
                v___x_3491_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3491_, 0, v___x_3490_);
                if v_isShared_3487_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3486_, 0, v___x_3491_);
                    v___x_3493_ = v___x_3486_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3494_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3494_, 0, v___x_3491_);
                    v___x_3493_ = v_reuseFailAlloc_3494_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3493_;
            }
            4 => {
                v___x_3500_ = l_Lean_MVarId_admit(
                    v_mvarId_3480_,
                    v_useSorry_3496_,
                    v___y_3473_,
                    v___y_3474_,
                    v___y_3475_,
                    v___y_3476_,
                );
                if crate::leanh::lean_obj_tag(v___x_3500_) == 0 {
                    v_isSharedCheck_3518_ = (!crate::leanh::lean_is_exclusive(v___x_3500_)) as u8;
                    if v_isSharedCheck_3518_ == 0 {
                        v_unused_3519_ = crate::leanh::lean_ctor_get(v___x_3500_, 0);
                        crate::leanh::lean_dec(v_unused_3519_);
                        v___x_3502_ = v___x_3500_;
                        v_isShared_3503_ = v_isSharedCheck_3518_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_3500_);
                        v___x_3502_ = crate::leanh::lean_box(0);
                        v_isShared_3503_ = v_isSharedCheck_3518_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3498_);
                    v_a_3520_ = crate::leanh::lean_ctor_get(v___x_3500_, 0);
                    v_isSharedCheck_3527_ = (!crate::leanh::lean_is_exclusive(v___x_3500_)) as u8;
                    if v_isSharedCheck_3527_ == 0 {
                        v___x_3522_ = v___x_3500_;
                        v_isShared_3523_ = v_isSharedCheck_3527_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3520_);
                        crate::leanh::lean_dec(v___x_3500_);
                        v___x_3522_ = crate::leanh::lean_box(0);
                        v_isShared_3523_ = v_isSharedCheck_3527_;
                        state = 8;
                        continue;
                    }
                }
            }
            5 => {
                v_ref_3504_ = crate::leanh::lean_ctor_get(v___y_3475_, 5);
                v___x_3505_ = l_Lean_SourceInfo_fromRef(v_ref_3504_, v_inconsistent_3479_);
                v___x_3506_ = l_Lean_Meta_Grind_Action_run___lam__0___closed__4;
                v___x_3507_ = l_Lean_Meta_Grind_Action_run___lam__0___closed__5;
                crate::leanh::lean_inc(v___x_3505_);
                if v_isShared_3499_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3498_, 2);
                    crate::leanh::lean_ctor_set(v___x_3498_, 1, v___x_3506_);
                    crate::leanh::lean_ctor_set(v___x_3498_, 0, v___x_3505_);
                    v___x_3509_ = v___x_3498_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3517_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3517_, 0, v___x_3505_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3517_, 1, v___x_3506_);
                    v___x_3509_ = v_reuseFailAlloc_3517_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_3510_ = l_Lean_Syntax_node1(v___x_3505_, v___x_3507_, v___x_3509_);
                v___x_3511_ = crate::leanh::lean_box(0);
                v___x_3512_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3512_, 0, v___x_3510_);
                crate::leanh::lean_ctor_set(v___x_3512_, 1, v___x_3511_);
                v___x_3513_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3513_, 0, v___x_3512_);
                if v_isShared_3503_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3502_, 0, v___x_3513_);
                    v___x_3515_ = v___x_3502_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3516_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3516_, 0, v___x_3513_);
                    v___x_3515_ = v_reuseFailAlloc_3516_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3515_;
            }
            8 => {
                if v_isShared_3523_ == 0 {
                    v___x_3525_ = v___x_3522_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3526_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3526_, 0, v_a_3520_);
                    v___x_3525_ = v_reuseFailAlloc_3526_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3525_;
            }
            10 => {
                if v_isShared_3535_ == 0 {
                    v___x_3537_ = v___x_3534_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3538_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3538_, 0, v_a_3532_);
                    v___x_3537_ = v_reuseFailAlloc_3538_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3537_;
            }
            12 => {
                if v_isShared_3543_ == 0 {
                    v___x_3545_ = v___x_3542_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3546_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3546_, 0, v_a_3540_);
                    v___x_3545_ = v_reuseFailAlloc_3546_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3545_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Action_run___lam__0___boxed(
    mut v_goal_3550_: *mut crate::leanh::LeanObject,
    mut v___y_3551_: *mut crate::leanh::LeanObject,
    mut v___y_3552_: *mut crate::leanh::LeanObject,
    mut v___y_3553_: *mut crate::leanh::LeanObject,
    mut v___y_3554_: *mut crate::leanh::LeanObject,
    mut v___y_3555_: *mut crate::leanh::LeanObject,
    mut v___y_3556_: *mut crate::leanh::LeanObject,
    mut v___y_3557_: *mut crate::leanh::LeanObject,
    mut v___y_3558_: *mut crate::leanh::LeanObject,
    mut v___y_3559_: *mut crate::leanh::LeanObject,
    mut v___y_3560_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3561_ = l_Lean_Meta_Grind_Action_run___lam__0(
        v_goal_3550_,
        v___y_3551_,
        v___y_3552_,
        v___y_3553_,
        v___y_3554_,
        v___y_3555_,
        v___y_3556_,
        v___y_3557_,
        v___y_3558_,
        v___y_3559_,
    );
    crate::leanh::lean_dec(v___y_3559_);
    crate::leanh::lean_dec_ref(v___y_3558_);
    crate::leanh::lean_dec(v___y_3557_);
    crate::leanh::lean_dec_ref(v___y_3556_);
    crate::leanh::lean_dec(v___y_3555_);
    crate::leanh::lean_dec_ref(v___y_3554_);
    crate::leanh::lean_dec(v___y_3553_);
    crate::leanh::lean_dec_ref(v___y_3552_);
    crate::leanh::lean_dec(v___y_3551_);
    return v_res_3561_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_run(
    mut v_goal_3563_: *mut crate::leanh::LeanObject,
    mut v_a_3564_: *mut crate::leanh::LeanObject,
    mut v_a_3565_: *mut crate::leanh::LeanObject,
    mut v_a_3566_: *mut crate::leanh::LeanObject,
    mut v_a_3567_: *mut crate::leanh::LeanObject,
    mut v_a_3568_: *mut crate::leanh::LeanObject,
    mut v_a_3569_: *mut crate::leanh::LeanObject,
    mut v_a_3570_: *mut crate::leanh::LeanObject,
    mut v_a_3571_: *mut crate::leanh::LeanObject,
    mut v_a_3572_: *mut crate::leanh::LeanObject,
    mut v_a_3573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_k_3575_ = l_Lean_Meta_Grind_Action_run___closed__0;
    crate::leanh::lean_inc(v_a_3573_);
    crate::leanh::lean_inc_ref(v_a_3572_);
    crate::leanh::lean_inc(v_a_3571_);
    crate::leanh::lean_inc_ref(v_a_3570_);
    crate::leanh::lean_inc(v_a_3569_);
    crate::leanh::lean_inc_ref(v_a_3568_);
    crate::leanh::lean_inc(v_a_3567_);
    crate::leanh::lean_inc_ref(v_a_3566_);
    crate::leanh::lean_inc(v_a_3565_);
    v___x_3576_ = crate::leanh::lean_apply_13(
        v_a_3564_,
        v_goal_3563_,
        v_k_3575_,
        v_k_3575_,
        v_a_3565_,
        v_a_3566_,
        v_a_3567_,
        v_a_3568_,
        v_a_3569_,
        v_a_3570_,
        v_a_3571_,
        v_a_3572_,
        v_a_3573_,
        crate::leanh::lean_box(0),
    );
    return v___x_3576_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_run___boxed(
    mut v_goal_3577_: *mut crate::leanh::LeanObject,
    mut v_a_3578_: *mut crate::leanh::LeanObject,
    mut v_a_3579_: *mut crate::leanh::LeanObject,
    mut v_a_3580_: *mut crate::leanh::LeanObject,
    mut v_a_3581_: *mut crate::leanh::LeanObject,
    mut v_a_3582_: *mut crate::leanh::LeanObject,
    mut v_a_3583_: *mut crate::leanh::LeanObject,
    mut v_a_3584_: *mut crate::leanh::LeanObject,
    mut v_a_3585_: *mut crate::leanh::LeanObject,
    mut v_a_3586_: *mut crate::leanh::LeanObject,
    mut v_a_3587_: *mut crate::leanh::LeanObject,
    mut v_a_3588_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3589_ = l_Lean_Meta_Grind_Action_run(
        v_goal_3577_,
        v_a_3578_,
        v_a_3579_,
        v_a_3580_,
        v_a_3581_,
        v_a_3582_,
        v_a_3583_,
        v_a_3584_,
        v_a_3585_,
        v_a_3586_,
        v_a_3587_,
    );
    crate::leanh::lean_dec(v_a_3587_);
    crate::leanh::lean_dec_ref(v_a_3586_);
    crate::leanh::lean_dec(v_a_3585_);
    crate::leanh::lean_dec_ref(v_a_3584_);
    crate::leanh::lean_dec(v_a_3583_);
    crate::leanh::lean_dec_ref(v_a_3582_);
    crate::leanh::lean_dec(v_a_3581_);
    crate::leanh::lean_dec_ref(v_a_3580_);
    crate::leanh::lean_dec(v_a_3579_);
    return v_res_3589_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_skipIfNA___redArg(
    mut v_x_3590_: *mut crate::leanh::LeanObject,
    mut v_goal_3591_: *mut crate::leanh::LeanObject,
    mut v_kp_3592_: *mut crate::leanh::LeanObject,
    mut v_a_3593_: *mut crate::leanh::LeanObject,
    mut v_a_3594_: *mut crate::leanh::LeanObject,
    mut v_a_3595_: *mut crate::leanh::LeanObject,
    mut v_a_3596_: *mut crate::leanh::LeanObject,
    mut v_a_3597_: *mut crate::leanh::LeanObject,
    mut v_a_3598_: *mut crate::leanh::LeanObject,
    mut v_a_3599_: *mut crate::leanh::LeanObject,
    mut v_a_3600_: *mut crate::leanh::LeanObject,
    mut v_a_3601_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_3601_);
    crate::leanh::lean_inc_ref(v_a_3600_);
    crate::leanh::lean_inc(v_a_3599_);
    crate::leanh::lean_inc_ref(v_a_3598_);
    crate::leanh::lean_inc(v_a_3597_);
    crate::leanh::lean_inc_ref(v_a_3596_);
    crate::leanh::lean_inc(v_a_3595_);
    crate::leanh::lean_inc_ref(v_a_3594_);
    crate::leanh::lean_inc(v_a_3593_);
    crate::leanh::lean_inc_ref(v_kp_3592_);
    v___x_3603_ = crate::leanh::lean_apply_13(
        v_x_3590_,
        v_goal_3591_,
        v_kp_3592_,
        v_kp_3592_,
        v_a_3593_,
        v_a_3594_,
        v_a_3595_,
        v_a_3596_,
        v_a_3597_,
        v_a_3598_,
        v_a_3599_,
        v_a_3600_,
        v_a_3601_,
        crate::leanh::lean_box(0),
    );
    return v___x_3603_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_skipIfNA___redArg___boxed(
    mut v_x_3604_: *mut crate::leanh::LeanObject,
    mut v_goal_3605_: *mut crate::leanh::LeanObject,
    mut v_kp_3606_: *mut crate::leanh::LeanObject,
    mut v_a_3607_: *mut crate::leanh::LeanObject,
    mut v_a_3608_: *mut crate::leanh::LeanObject,
    mut v_a_3609_: *mut crate::leanh::LeanObject,
    mut v_a_3610_: *mut crate::leanh::LeanObject,
    mut v_a_3611_: *mut crate::leanh::LeanObject,
    mut v_a_3612_: *mut crate::leanh::LeanObject,
    mut v_a_3613_: *mut crate::leanh::LeanObject,
    mut v_a_3614_: *mut crate::leanh::LeanObject,
    mut v_a_3615_: *mut crate::leanh::LeanObject,
    mut v_a_3616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3617_ = l_Lean_Meta_Grind_Action_skipIfNA___redArg(
        v_x_3604_,
        v_goal_3605_,
        v_kp_3606_,
        v_a_3607_,
        v_a_3608_,
        v_a_3609_,
        v_a_3610_,
        v_a_3611_,
        v_a_3612_,
        v_a_3613_,
        v_a_3614_,
        v_a_3615_,
    );
    crate::leanh::lean_dec(v_a_3615_);
    crate::leanh::lean_dec_ref(v_a_3614_);
    crate::leanh::lean_dec(v_a_3613_);
    crate::leanh::lean_dec_ref(v_a_3612_);
    crate::leanh::lean_dec(v_a_3611_);
    crate::leanh::lean_dec_ref(v_a_3610_);
    crate::leanh::lean_dec(v_a_3609_);
    crate::leanh::lean_dec_ref(v_a_3608_);
    crate::leanh::lean_dec(v_a_3607_);
    return v_res_3617_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_skipIfNA(
    mut v_x_3618_: *mut crate::leanh::LeanObject,
    mut v_goal_3619_: *mut crate::leanh::LeanObject,
    mut v_x_3620_: *mut crate::leanh::LeanObject,
    mut v_kp_3621_: *mut crate::leanh::LeanObject,
    mut v_a_3622_: *mut crate::leanh::LeanObject,
    mut v_a_3623_: *mut crate::leanh::LeanObject,
    mut v_a_3624_: *mut crate::leanh::LeanObject,
    mut v_a_3625_: *mut crate::leanh::LeanObject,
    mut v_a_3626_: *mut crate::leanh::LeanObject,
    mut v_a_3627_: *mut crate::leanh::LeanObject,
    mut v_a_3628_: *mut crate::leanh::LeanObject,
    mut v_a_3629_: *mut crate::leanh::LeanObject,
    mut v_a_3630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_3630_);
    crate::leanh::lean_inc_ref(v_a_3629_);
    crate::leanh::lean_inc(v_a_3628_);
    crate::leanh::lean_inc_ref(v_a_3627_);
    crate::leanh::lean_inc(v_a_3626_);
    crate::leanh::lean_inc_ref(v_a_3625_);
    crate::leanh::lean_inc(v_a_3624_);
    crate::leanh::lean_inc_ref(v_a_3623_);
    crate::leanh::lean_inc(v_a_3622_);
    crate::leanh::lean_inc_ref(v_kp_3621_);
    v___x_3632_ = crate::leanh::lean_apply_13(
        v_x_3618_,
        v_goal_3619_,
        v_kp_3621_,
        v_kp_3621_,
        v_a_3622_,
        v_a_3623_,
        v_a_3624_,
        v_a_3625_,
        v_a_3626_,
        v_a_3627_,
        v_a_3628_,
        v_a_3629_,
        v_a_3630_,
        crate::leanh::lean_box(0),
    );
    return v___x_3632_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_skipIfNA___boxed(
    mut v_x_3633_: *mut crate::leanh::LeanObject,
    mut v_goal_3634_: *mut crate::leanh::LeanObject,
    mut v_x_3635_: *mut crate::leanh::LeanObject,
    mut v_kp_3636_: *mut crate::leanh::LeanObject,
    mut v_a_3637_: *mut crate::leanh::LeanObject,
    mut v_a_3638_: *mut crate::leanh::LeanObject,
    mut v_a_3639_: *mut crate::leanh::LeanObject,
    mut v_a_3640_: *mut crate::leanh::LeanObject,
    mut v_a_3641_: *mut crate::leanh::LeanObject,
    mut v_a_3642_: *mut crate::leanh::LeanObject,
    mut v_a_3643_: *mut crate::leanh::LeanObject,
    mut v_a_3644_: *mut crate::leanh::LeanObject,
    mut v_a_3645_: *mut crate::leanh::LeanObject,
    mut v_a_3646_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3647_ = l_Lean_Meta_Grind_Action_skipIfNA(
        v_x_3633_,
        v_goal_3634_,
        v_x_3635_,
        v_kp_3636_,
        v_a_3637_,
        v_a_3638_,
        v_a_3639_,
        v_a_3640_,
        v_a_3641_,
        v_a_3642_,
        v_a_3643_,
        v_a_3644_,
        v_a_3645_,
    );
    crate::leanh::lean_dec(v_a_3645_);
    crate::leanh::lean_dec_ref(v_a_3644_);
    crate::leanh::lean_dec(v_a_3643_);
    crate::leanh::lean_dec_ref(v_a_3642_);
    crate::leanh::lean_dec(v_a_3641_);
    crate::leanh::lean_dec_ref(v_a_3640_);
    crate::leanh::lean_dec(v_a_3639_);
    crate::leanh::lean_dec_ref(v_a_3638_);
    crate::leanh::lean_dec(v_a_3637_);
    crate::leanh::lean_dec_ref(v_x_3635_);
    return v_res_3647_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_mkGrindStep(
    mut v_t_3664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3665_ = l_Lean_Meta_Grind_Action_mkGrindStep___closed__1;
    v___x_3666_ = crate::leanh::lean_box(2);
    v___x_3667_ = l_Lean_Meta_Grind_Action_mkGrindStep___closed__5;
    v___x_3668_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_3669_ = lean_mk_empty_array_with_capacity(v___x_3668_);
    v___x_3670_ = lean_array_push(v___x_3669_, v_t_3664_);
    v___x_3671_ = lean_array_push(v___x_3670_, v___x_3667_);
    v___x_3672_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3672_, 0, v___x_3666_);
    crate::leanh::lean_ctor_set(v___x_3672_, 1, v___x_3665_);
    crate::leanh::lean_ctor_set(v___x_3672_, 2, v___x_3671_);
    return v___x_3672_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_TGrindStep_getTactic(
    mut v_x_3673_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: u8 = 0;
    v___x_3674_ = l_Lean_Meta_Grind_Action_mkGrindStep___closed__1;
    crate::leanh::lean_inc(v_x_3673_);
    v___x_3675_ = l_Lean_Syntax_isOfKind(v_x_3673_, v___x_3674_);
    if v___x_3675_ == 0 {
        let mut v___x_3676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_3673_);
        v___x_3676_ = l_Lean_Meta_Grind_Action_mkGrindStep___closed__5;
        return v___x_3676_;
    } else {
        let mut v___x_3677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tac_3678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3681_: u8 = 0;
        v___x_3677_ = crate::leanh::lean_unsigned_to_nat(0);
        v_tac_3678_ = l_Lean_Syntax_getArg(v_x_3673_, v___x_3677_);
        v___x_3679_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_3680_ = l_Lean_Syntax_getArg(v_x_3673_, v___x_3679_);
        crate::leanh::lean_dec(v_x_3673_);
        v___x_3681_ = l_Lean_Syntax_isNone(v___x_3680_);
        if v___x_3681_ == 0 {
            let mut v___x_3682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3683_: u8 = 0;
            v___x_3682_ = crate::leanh::lean_unsigned_to_nat(2);
            crate::leanh::lean_inc(v___x_3680_);
            v___x_3683_ = l_Lean_Syntax_matchesNull(v___x_3680_, v___x_3682_);
            if v___x_3683_ == 0 {
                let mut v___x_3684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v___x_3680_);
                crate::leanh::lean_dec(v_tac_3678_);
                v___x_3684_ = l_Lean_Meta_Grind_Action_mkGrindStep___closed__5;
                return v___x_3684_;
            } else {
                let mut v___x_3685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3686_: u8 = 0;
                v___x_3685_ = l_Lean_Syntax_getArg(v___x_3680_, v___x_3679_);
                crate::leanh::lean_dec(v___x_3680_);
                v___x_3686_ = l_Lean_Syntax_matchesNull(v___x_3685_, v___x_3679_);
                if v___x_3686_ == 0 {
                    let mut v___x_3687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_tac_3678_);
                    v___x_3687_ = l_Lean_Meta_Grind_Action_mkGrindStep___closed__5;
                    return v___x_3687_;
                } else {
                    return v_tac_3678_;
                }
            }
        } else {
            crate::leanh::lean_dec(v___x_3680_);
            return v_tac_3678_;
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Grind_Action_mkGrindSeq_spec__0(
    mut v_a_3688_: *mut crate::leanh::LeanObject,
    mut v_a_3689_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3695_: u8 = 0;
    let mut v___x_3696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3701_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_3688_) == 0 {
                    v___x_3690_ = l_List_reverse___redArg(v_a_3689_);
                    return v___x_3690_;
                } else {
                    v_head_3691_ = crate::leanh::lean_ctor_get(v_a_3688_, 0);
                    v_tail_3692_ = crate::leanh::lean_ctor_get(v_a_3688_, 1);
                    v_isSharedCheck_3701_ = (!crate::leanh::lean_is_exclusive(v_a_3688_)) as u8;
                    if v_isSharedCheck_3701_ == 0 {
                        v___x_3694_ = v_a_3688_;
                        v_isShared_3695_ = v_isSharedCheck_3701_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3692_);
                        crate::leanh::lean_inc(v_head_3691_);
                        crate::leanh::lean_dec(v_a_3688_);
                        v___x_3694_ = crate::leanh::lean_box(0);
                        v_isShared_3695_ = v_isSharedCheck_3701_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3696_ = l_Lean_Meta_Grind_Action_mkGrindStep(v_head_3691_);
                if v_isShared_3695_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3694_, 1, v_a_3689_);
                    crate::leanh::lean_ctor_set(v___x_3694_, 0, v___x_3696_);
                    v___x_3698_ = v___x_3694_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3700_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3700_, 0, v___x_3696_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3700_, 1, v_a_3689_);
                    v___x_3698_ = v_reuseFailAlloc_3700_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_3688_ = v_tail_3692_;
                v_a_3689_ = v___x_3698_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Action_mkGrindSeq(
    mut v_s_3722_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_3724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_3728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3723_ = crate::leanh::lean_box(0);
    v_s_3724_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Action_mkGrindSeq_spec__0(
        v_s_3722_,
        v___x_3723_,
    );
    v___x_3725_ = l_Lean_Meta_Grind_Action_mkGrindStep___closed__4;
    v___x_3726_ = crate::leanh::lean_box(2);
    v___x_3727_ = l_Lean_Meta_Grind_Action_mkGrindSeq___closed__1;
    v_s_3728_ = l_List_intersperseTR___redArg(v___x_3727_, v_s_3724_);
    v___x_3729_ = l_Lean_Meta_Grind_Action_mkGrindSeq___closed__3;
    v___x_3730_ = l_Lean_Meta_Grind_Action_mkGrindSeq___closed__5;
    v___x_3731_ = lean_array_mk(v_s_3728_);
    v___x_3732_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3732_, 0, v___x_3726_);
    crate::leanh::lean_ctor_set(v___x_3732_, 1, v___x_3725_);
    crate::leanh::lean_ctor_set(v___x_3732_, 2, v___x_3731_);
    v___x_3733_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_3734_ = lean_mk_empty_array_with_capacity(v___x_3733_);
    crate::leanh::lean_inc_ref(v___x_3734_);
    v___x_3735_ = lean_array_push(v___x_3734_, v___x_3732_);
    v___x_3736_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3736_, 0, v___x_3726_);
    crate::leanh::lean_ctor_set(v___x_3736_, 1, v___x_3730_);
    crate::leanh::lean_ctor_set(v___x_3736_, 2, v___x_3735_);
    v___x_3737_ = lean_array_push(v___x_3734_, v___x_3736_);
    v___x_3738_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3738_, 0, v___x_3726_);
    crate::leanh::lean_ctor_set(v___x_3738_, 1, v___x_3729_);
    crate::leanh::lean_ctor_set(v___x_3738_, 2, v___x_3737_);
    return v___x_3738_;
}
pub unsafe fn l_List_beq___at___00Lean_Meta_Grind_Action_mkGrindNext_spec__0(
    mut v_x_3739_: *mut crate::leanh::LeanObject,
    mut v_x_3740_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3741_: u8 = 0;
    let mut v___x_3742_: u8 = 0;
    let mut v___x_3743_: u8 = 0;
    let mut v_head_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3739_) == 0 {
                    if crate::leanh::lean_obj_tag(v_x_3740_) == 0 {
                        v___x_3741_ = 1;
                        return v___x_3741_;
                    } else {
                        crate::leanh::lean_dec_ref_known(v_x_3740_, 2);
                        v___x_3742_ = 0;
                        return v___x_3742_;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_x_3740_) == 0 {
                        crate::leanh::lean_dec_ref_known(v_x_3739_, 2);
                        v___x_3743_ = 0;
                        return v___x_3743_;
                    } else {
                        v_head_3744_ = crate::leanh::lean_ctor_get(v_x_3739_, 0);
                        crate::leanh::lean_inc(v_head_3744_);
                        v_tail_3745_ = crate::leanh::lean_ctor_get(v_x_3739_, 1);
                        crate::leanh::lean_inc(v_tail_3745_);
                        crate::leanh::lean_dec_ref_known(v_x_3739_, 2);
                        v_head_3746_ = crate::leanh::lean_ctor_get(v_x_3740_, 0);
                        crate::leanh::lean_inc(v_head_3746_);
                        v_tail_3747_ = crate::leanh::lean_ctor_get(v_x_3740_, 1);
                        crate::leanh::lean_inc(v_tail_3747_);
                        crate::leanh::lean_dec_ref_known(v_x_3740_, 2);
                        v___x_3748_ = l_Lean_Syntax_structEq(v_head_3744_, v_head_3746_);
                        if v___x_3748_ == 0 {
                            crate::leanh::lean_dec(v_tail_3747_);
                            crate::leanh::lean_dec(v_tail_3745_);
                            return v___x_3748_;
                        } else {
                            v_x_3739_ = v_tail_3745_;
                            v_x_3740_ = v_tail_3747_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_beq___at___00Lean_Meta_Grind_Action_mkGrindNext_spec__0___boxed(
    mut v_x_3750_: *mut crate::leanh::LeanObject,
    mut v_x_3751_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3752_: u8 = 0;
    let mut v_r_3753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3752_ =
        l_List_beq___at___00Lean_Meta_Grind_Action_mkGrindNext_spec__0(v_x_3750_, v_x_3751_);
    v_r_3753_ = crate::leanh::lean_box((v_res_3752_) as usize);
    return v_r_3753_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_mkGrindNext___redArg(
    mut v_s_3769_: *mut crate::leanh::LeanObject,
    mut v_a_3770_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_s_3773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_3775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3776_: u8 = 0;
    let mut v___x_3777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: u8 = 0;
    let mut v_ref_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: u8 = 0;
    let mut v___x_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3783_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_s_3769_);
                v___x_3784_ = l_List_beq___at___00Lean_Meta_Grind_Action_mkGrindNext_spec__0(
                    v_s_3769_,
                    v___x_3783_,
                );
                if v___x_3784_ == 0 {
                    v_ref_3785_ = crate::leanh::lean_ctor_get(v_a_3770_, 5);
                    v_s_3773_ = v_s_3769_;
                    v_ref_3774_ = v_ref_3785_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_s_3769_);
                    v_ref_3786_ = crate::leanh::lean_ctor_get(v_a_3770_, 5);
                    v___x_3787_ = 0;
                    v___x_3788_ = l_Lean_SourceInfo_fromRef(v_ref_3786_, v___x_3787_);
                    v___x_3789_ = l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__3;
                    v___x_3790_ = l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__4;
                    crate::leanh::lean_inc(v___x_3788_);
                    v___x_3791_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3791_, 0, v___x_3788_);
                    crate::leanh::lean_ctor_set(v___x_3791_, 1, v___x_3789_);
                    v___x_3792_ = l_Lean_Syntax_node1(v___x_3788_, v___x_3790_, v___x_3791_);
                    v___x_3793_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3793_, 0, v___x_3792_);
                    crate::leanh::lean_ctor_set(v___x_3793_, 1, v___x_3783_);
                    v_s_3773_ = v___x_3793_;
                    v_ref_3774_ = v_ref_3786_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_s_3775_ = l_Lean_Meta_Grind_Action_mkGrindSeq(v_s_3773_);
                v___x_3776_ = 0;
                v___x_3777_ = l_Lean_SourceInfo_fromRef(v_ref_3774_, v___x_3776_);
                v___x_3778_ = l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__1;
                v___x_3779_ = l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__2;
                crate::leanh::lean_inc(v___x_3777_);
                v___x_3780_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3780_, 0, v___x_3777_);
                crate::leanh::lean_ctor_set(v___x_3780_, 1, v___x_3779_);
                v___x_3781_ = l_Lean_Syntax_node2(v___x_3777_, v___x_3778_, v___x_3780_, v_s_3775_);
                v___x_3782_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3782_, 0, v___x_3781_);
                return v___x_3782_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Action_mkGrindNext___redArg___boxed(
    mut v_s_3794_: *mut crate::leanh::LeanObject,
    mut v_a_3795_: *mut crate::leanh::LeanObject,
    mut v_a_3796_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3797_ = l_Lean_Meta_Grind_Action_mkGrindNext___redArg(v_s_3794_, v_a_3795_);
    crate::leanh::lean_dec_ref(v_a_3795_);
    return v_res_3797_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_mkGrindNext(
    mut v_s_3798_: *mut crate::leanh::LeanObject,
    mut v_a_3799_: *mut crate::leanh::LeanObject,
    mut v_a_3800_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3802_ = l_Lean_Meta_Grind_Action_mkGrindNext___redArg(v_s_3798_, v_a_3799_);
    return v___x_3802_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_mkGrindNext___boxed(
    mut v_s_3803_: *mut crate::leanh::LeanObject,
    mut v_a_3804_: *mut crate::leanh::LeanObject,
    mut v_a_3805_: *mut crate::leanh::LeanObject,
    mut v_a_3806_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3807_ = l_Lean_Meta_Grind_Action_mkGrindNext(v_s_3803_, v_a_3804_, v_a_3805_);
    crate::leanh::lean_dec(v_a_3805_);
    crate::leanh::lean_dec_ref(v_a_3804_);
    return v_res_3807_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg(
    mut v_s_3824_: *mut crate::leanh::LeanObject,
    mut v_a_3825_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_s_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: u8 = 0;
    let mut v___x_3832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: u8 = 0;
    let mut v_ref_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: u8 = 0;
    let mut v___x_3845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3840_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_s_3824_);
                v___x_3841_ = l_List_beq___at___00Lean_Meta_Grind_Action_mkGrindNext_spec__0(
                    v_s_3824_,
                    v___x_3840_,
                );
                if v___x_3841_ == 0 {
                    v_ref_3842_ = crate::leanh::lean_ctor_get(v_a_3825_, 5);
                    v_s_3828_ = v_s_3824_;
                    v_ref_3829_ = v_ref_3842_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_s_3824_);
                    v_ref_3843_ = crate::leanh::lean_ctor_get(v_a_3825_, 5);
                    v___x_3844_ = 0;
                    v___x_3845_ = l_Lean_SourceInfo_fromRef(v_ref_3843_, v___x_3844_);
                    v___x_3846_ = l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__4;
                    v___x_3847_ = l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__5;
                    crate::leanh::lean_inc(v___x_3845_);
                    v___x_3848_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3848_, 0, v___x_3845_);
                    crate::leanh::lean_ctor_set(v___x_3848_, 1, v___x_3846_);
                    v___x_3849_ = l_Lean_Syntax_node1(v___x_3845_, v___x_3847_, v___x_3848_);
                    v___x_3850_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3850_, 0, v___x_3849_);
                    crate::leanh::lean_ctor_set(v___x_3850_, 1, v___x_3840_);
                    v_s_3828_ = v___x_3850_;
                    v_ref_3829_ = v_ref_3843_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_s_3830_ = l_Lean_Meta_Grind_Action_mkGrindSeq(v_s_3828_);
                v___x_3831_ = 0;
                v___x_3832_ = l_Lean_SourceInfo_fromRef(v_ref_3829_, v___x_3831_);
                v___x_3833_ = l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__1;
                v___x_3834_ = l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__2;
                crate::leanh::lean_inc_n(v___x_3832_, 2);
                v___x_3835_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3835_, 0, v___x_3832_);
                crate::leanh::lean_ctor_set(v___x_3835_, 1, v___x_3834_);
                v___x_3836_ = l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__3;
                v___x_3837_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3837_, 0, v___x_3832_);
                crate::leanh::lean_ctor_set(v___x_3837_, 1, v___x_3836_);
                v___x_3838_ = l_Lean_Syntax_node3(
                    v___x_3832_,
                    v___x_3833_,
                    v___x_3835_,
                    v_s_3830_,
                    v___x_3837_,
                );
                v___x_3839_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3839_, 0, v___x_3838_);
                return v___x_3839_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___boxed(
    mut v_s_3851_: *mut crate::leanh::LeanObject,
    mut v_a_3852_: *mut crate::leanh::LeanObject,
    mut v_a_3853_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3854_ =
        l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg(
            v_s_3851_, v_a_3852_,
        );
    crate::leanh::lean_dec_ref(v_a_3852_);
    return v_res_3854_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen(
    mut v_s_3855_: *mut crate::leanh::LeanObject,
    mut v_a_3856_: *mut crate::leanh::LeanObject,
    mut v_a_3857_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3859_ =
        l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg(
            v_s_3855_, v_a_3856_,
        );
    return v___x_3859_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___boxed(
    mut v_s_3860_: *mut crate::leanh::LeanObject,
    mut v_a_3861_: *mut crate::leanh::LeanObject,
    mut v_a_3862_: *mut crate::leanh::LeanObject,
    mut v_a_3863_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3864_ = l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen(
        v_s_3860_, v_a_3861_, v_a_3862_,
    );
    crate::leanh::lean_dec(v_a_3862_);
    crate::leanh::lean_dec_ref(v_a_3861_);
    return v_res_3864_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_group___redArg(
    mut v_goal_3865_: *mut crate::leanh::LeanObject,
    mut v_kp_3866_: *mut crate::leanh::LeanObject,
    mut v_a_3867_: *mut crate::leanh::LeanObject,
    mut v_a_3868_: *mut crate::leanh::LeanObject,
    mut v_a_3869_: *mut crate::leanh::LeanObject,
    mut v_a_3870_: *mut crate::leanh::LeanObject,
    mut v_a_3871_: *mut crate::leanh::LeanObject,
    mut v_a_3872_: *mut crate::leanh::LeanObject,
    mut v_a_3873_: *mut crate::leanh::LeanObject,
    mut v_a_3874_: *mut crate::leanh::LeanObject,
    mut v_a_3875_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3883_: u8 = 0;
    let mut v_trace_3884_: u8 = 0;
    let mut v___x_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_seq_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3891_: u8 = 0;
    let mut v___x_3892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3896_: u8 = 0;
    let mut v___x_3897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3905_: u8 = 0;
    let mut v_isSharedCheck_3906_: u8 = 0;
    let mut v___x_3908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3910_: u8 = 0;
    let mut v_a_3911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3914_: u8 = 0;
    let mut v___x_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3918_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_3875_);
                crate::leanh::lean_inc_ref(v_a_3874_);
                crate::leanh::lean_inc(v_a_3873_);
                crate::leanh::lean_inc_ref(v_a_3872_);
                crate::leanh::lean_inc(v_a_3871_);
                crate::leanh::lean_inc_ref(v_a_3870_);
                crate::leanh::lean_inc(v_a_3869_);
                crate::leanh::lean_inc_ref(v_a_3868_);
                crate::leanh::lean_inc(v_a_3867_);
                v___x_3877_ = crate::leanh::lean_apply_11(
                    v_kp_3866_,
                    v_goal_3865_,
                    v_a_3867_,
                    v_a_3868_,
                    v_a_3869_,
                    v_a_3870_,
                    v_a_3871_,
                    v_a_3872_,
                    v_a_3873_,
                    v_a_3874_,
                    v_a_3875_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_3877_) == 0 {
                    v_a_3878_ = crate::leanh::lean_ctor_get(v___x_3877_, 0);
                    crate::leanh::lean_inc(v_a_3878_);
                    crate::leanh::lean_dec_ref_known(v___x_3877_, 1);
                    v___x_3879_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_3868_);
                    if crate::leanh::lean_obj_tag(v___x_3879_) == 0 {
                        v_a_3880_ = crate::leanh::lean_ctor_get(v___x_3879_, 0);
                        v_isSharedCheck_3910_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3879_)) as u8;
                        if v_isSharedCheck_3910_ == 0 {
                            v___x_3882_ = v___x_3879_;
                            v_isShared_3883_ = v_isSharedCheck_3910_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3880_);
                            crate::leanh::lean_dec(v___x_3879_);
                            v___x_3882_ = crate::leanh::lean_box(0);
                            v_isShared_3883_ = v_isSharedCheck_3910_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3878_);
                        v_a_3911_ = crate::leanh::lean_ctor_get(v___x_3879_, 0);
                        v_isSharedCheck_3918_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3879_)) as u8;
                        if v_isSharedCheck_3918_ == 0 {
                            v___x_3913_ = v___x_3879_;
                            v_isShared_3914_ = v_isSharedCheck_3918_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3911_);
                            crate::leanh::lean_dec(v___x_3879_);
                            v___x_3913_ = crate::leanh::lean_box(0);
                            v_isShared_3914_ = v_isSharedCheck_3918_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    return v___x_3877_;
                }
            }
            1 => {
                v_trace_3884_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3880_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13) as u32,
                );
                crate::leanh::lean_dec(v_a_3880_);
                if v_trace_3884_ == 0 {
                    if v_isShared_3883_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3882_, 0, v_a_3878_);
                        v___x_3886_ = v___x_3882_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3887_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3887_, 0, v_a_3878_);
                        v___x_3886_ = v_reuseFailAlloc_3887_;
                        state = 2;
                        continue;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_a_3878_) == 0 {
                        crate::leanh::lean_del_object(v___x_3882_);
                        v_seq_3888_ = crate::leanh::lean_ctor_get(v_a_3878_, 0);
                        v_isSharedCheck_3906_ = (!crate::leanh::lean_is_exclusive(v_a_3878_)) as u8;
                        if v_isSharedCheck_3906_ == 0 {
                            v___x_3890_ = v_a_3878_;
                            v_isShared_3891_ = v_isSharedCheck_3906_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_seq_3888_);
                            crate::leanh::lean_dec(v_a_3878_);
                            v___x_3890_ = crate::leanh::lean_box(0);
                            v_isShared_3891_ = v_isSharedCheck_3906_;
                            state = 3;
                            continue;
                        }
                    } else {
                        if v_isShared_3883_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3882_, 0, v_a_3878_);
                            v___x_3908_ = v___x_3882_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_3909_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3909_, 0, v_a_3878_);
                            v___x_3908_ = v_reuseFailAlloc_3909_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3886_;
            }
            3 => {
                v___x_3892_ = l_Lean_Meta_Grind_Action_mkGrindNext___redArg(v_seq_3888_, v_a_3874_);
                v_a_3893_ = crate::leanh::lean_ctor_get(v___x_3892_, 0);
                v_isSharedCheck_3905_ = (!crate::leanh::lean_is_exclusive(v___x_3892_)) as u8;
                if v_isSharedCheck_3905_ == 0 {
                    v___x_3895_ = v___x_3892_;
                    v_isShared_3896_ = v_isSharedCheck_3905_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3893_);
                    crate::leanh::lean_dec(v___x_3892_);
                    v___x_3895_ = crate::leanh::lean_box(0);
                    v_isShared_3896_ = v_isSharedCheck_3905_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3897_ = crate::leanh::lean_box(0);
                v___x_3898_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3898_, 0, v_a_3893_);
                crate::leanh::lean_ctor_set(v___x_3898_, 1, v___x_3897_);
                if v_isShared_3891_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3890_, 0, v___x_3898_);
                    v___x_3900_ = v___x_3890_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3904_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3904_, 0, v___x_3898_);
                    v___x_3900_ = v_reuseFailAlloc_3904_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_3896_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3895_, 0, v___x_3900_);
                    v___x_3902_ = v___x_3895_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3903_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3903_, 0, v___x_3900_);
                    v___x_3902_ = v_reuseFailAlloc_3903_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3902_;
            }
            7 => {
                return v___x_3908_;
            }
            8 => {
                if v_isShared_3914_ == 0 {
                    v___x_3916_ = v___x_3913_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3917_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3917_, 0, v_a_3911_);
                    v___x_3916_ = v_reuseFailAlloc_3917_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3916_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Action_group___redArg___boxed(
    mut v_goal_3919_: *mut crate::leanh::LeanObject,
    mut v_kp_3920_: *mut crate::leanh::LeanObject,
    mut v_a_3921_: *mut crate::leanh::LeanObject,
    mut v_a_3922_: *mut crate::leanh::LeanObject,
    mut v_a_3923_: *mut crate::leanh::LeanObject,
    mut v_a_3924_: *mut crate::leanh::LeanObject,
    mut v_a_3925_: *mut crate::leanh::LeanObject,
    mut v_a_3926_: *mut crate::leanh::LeanObject,
    mut v_a_3927_: *mut crate::leanh::LeanObject,
    mut v_a_3928_: *mut crate::leanh::LeanObject,
    mut v_a_3929_: *mut crate::leanh::LeanObject,
    mut v_a_3930_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3931_ = l_Lean_Meta_Grind_Action_group___redArg(
        v_goal_3919_,
        v_kp_3920_,
        v_a_3921_,
        v_a_3922_,
        v_a_3923_,
        v_a_3924_,
        v_a_3925_,
        v_a_3926_,
        v_a_3927_,
        v_a_3928_,
        v_a_3929_,
    );
    crate::leanh::lean_dec(v_a_3929_);
    crate::leanh::lean_dec_ref(v_a_3928_);
    crate::leanh::lean_dec(v_a_3927_);
    crate::leanh::lean_dec_ref(v_a_3926_);
    crate::leanh::lean_dec(v_a_3925_);
    crate::leanh::lean_dec_ref(v_a_3924_);
    crate::leanh::lean_dec(v_a_3923_);
    crate::leanh::lean_dec_ref(v_a_3922_);
    crate::leanh::lean_dec(v_a_3921_);
    return v_res_3931_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_group(
    mut v_goal_3932_: *mut crate::leanh::LeanObject,
    mut v_x_3933_: *mut crate::leanh::LeanObject,
    mut v_kp_3934_: *mut crate::leanh::LeanObject,
    mut v_a_3935_: *mut crate::leanh::LeanObject,
    mut v_a_3936_: *mut crate::leanh::LeanObject,
    mut v_a_3937_: *mut crate::leanh::LeanObject,
    mut v_a_3938_: *mut crate::leanh::LeanObject,
    mut v_a_3939_: *mut crate::leanh::LeanObject,
    mut v_a_3940_: *mut crate::leanh::LeanObject,
    mut v_a_3941_: *mut crate::leanh::LeanObject,
    mut v_a_3942_: *mut crate::leanh::LeanObject,
    mut v_a_3943_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3945_ = l_Lean_Meta_Grind_Action_group___redArg(
        v_goal_3932_,
        v_kp_3934_,
        v_a_3935_,
        v_a_3936_,
        v_a_3937_,
        v_a_3938_,
        v_a_3939_,
        v_a_3940_,
        v_a_3941_,
        v_a_3942_,
        v_a_3943_,
    );
    return v___x_3945_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_group___boxed(
    mut v_goal_3946_: *mut crate::leanh::LeanObject,
    mut v_x_3947_: *mut crate::leanh::LeanObject,
    mut v_kp_3948_: *mut crate::leanh::LeanObject,
    mut v_a_3949_: *mut crate::leanh::LeanObject,
    mut v_a_3950_: *mut crate::leanh::LeanObject,
    mut v_a_3951_: *mut crate::leanh::LeanObject,
    mut v_a_3952_: *mut crate::leanh::LeanObject,
    mut v_a_3953_: *mut crate::leanh::LeanObject,
    mut v_a_3954_: *mut crate::leanh::LeanObject,
    mut v_a_3955_: *mut crate::leanh::LeanObject,
    mut v_a_3956_: *mut crate::leanh::LeanObject,
    mut v_a_3957_: *mut crate::leanh::LeanObject,
    mut v_a_3958_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3959_ = l_Lean_Meta_Grind_Action_group(
        v_goal_3946_,
        v_x_3947_,
        v_kp_3948_,
        v_a_3949_,
        v_a_3950_,
        v_a_3951_,
        v_a_3952_,
        v_a_3953_,
        v_a_3954_,
        v_a_3955_,
        v_a_3956_,
        v_a_3957_,
    );
    crate::leanh::lean_dec(v_a_3957_);
    crate::leanh::lean_dec_ref(v_a_3956_);
    crate::leanh::lean_dec(v_a_3955_);
    crate::leanh::lean_dec_ref(v_a_3954_);
    crate::leanh::lean_dec(v_a_3953_);
    crate::leanh::lean_dec_ref(v_a_3952_);
    crate::leanh::lean_dec(v_a_3951_);
    crate::leanh::lean_dec_ref(v_a_3950_);
    crate::leanh::lean_dec(v_a_3949_);
    crate::leanh::lean_dec_ref(v_x_3947_);
    return v_res_3959_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Grind_Action_ungroup_spec__0(
    mut v_a_3960_: *mut crate::leanh::LeanObject,
    mut v_a_3961_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3967_: u8 = 0;
    let mut v___x_3968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3973_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_3960_) == 0 {
                    v___x_3962_ = l_List_reverse___redArg(v_a_3961_);
                    return v___x_3962_;
                } else {
                    v_head_3963_ = crate::leanh::lean_ctor_get(v_a_3960_, 0);
                    v_tail_3964_ = crate::leanh::lean_ctor_get(v_a_3960_, 1);
                    v_isSharedCheck_3973_ = (!crate::leanh::lean_is_exclusive(v_a_3960_)) as u8;
                    if v_isSharedCheck_3973_ == 0 {
                        v___x_3966_ = v_a_3960_;
                        v_isShared_3967_ = v_isSharedCheck_3973_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3964_);
                        crate::leanh::lean_inc(v_head_3963_);
                        crate::leanh::lean_dec(v_a_3960_);
                        v___x_3966_ = crate::leanh::lean_box(0);
                        v_isShared_3967_ = v_isSharedCheck_3973_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3968_ = l_Lean_Meta_Grind_Action_TGrindStep_getTactic(v_head_3963_);
                if v_isShared_3967_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3966_, 1, v_a_3961_);
                    crate::leanh::lean_ctor_set(v___x_3966_, 0, v___x_3968_);
                    v___x_3970_ = v___x_3966_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3972_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3972_, 0, v___x_3968_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3972_, 1, v_a_3961_);
                    v___x_3970_ = v_reuseFailAlloc_3972_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_3960_ = v_tail_3964_;
                v_a_3961_ = v___x_3970_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Action_ungroup___redArg(
    mut v_goal_3981_: *mut crate::leanh::LeanObject,
    mut v_kp_3982_: *mut crate::leanh::LeanObject,
    mut v_a_3983_: *mut crate::leanh::LeanObject,
    mut v_a_3984_: *mut crate::leanh::LeanObject,
    mut v_a_3985_: *mut crate::leanh::LeanObject,
    mut v_a_3986_: *mut crate::leanh::LeanObject,
    mut v_a_3987_: *mut crate::leanh::LeanObject,
    mut v_a_3988_: *mut crate::leanh::LeanObject,
    mut v_a_3989_: *mut crate::leanh::LeanObject,
    mut v_a_3990_: *mut crate::leanh::LeanObject,
    mut v_a_3991_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3999_: u8 = 0;
    let mut v_trace_4000_: u8 = 0;
    let mut v___x_4002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_seq_4004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4008_: u8 = 0;
    let mut v___x_4009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: u8 = 0;
    let mut v___x_4012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: u8 = 0;
    let mut v___x_4019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: u8 = 0;
    let mut v___x_4026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4030_: u8 = 0;
    let mut v___x_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4042_: u8 = 0;
    let mut v_unused_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: u8 = 0;
    let mut v___x_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4054_: u8 = 0;
    let mut v___x_4056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: u8 = 0;
    let mut v___x_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4066_: u8 = 0;
    let mut v___x_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4078_: u8 = 0;
    let mut v_unused_4079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4089_: u8 = 0;
    let mut v_a_4090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4093_: u8 = 0;
    let mut v___x_4095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4097_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_3991_);
                crate::leanh::lean_inc_ref(v_a_3990_);
                crate::leanh::lean_inc(v_a_3989_);
                crate::leanh::lean_inc_ref(v_a_3988_);
                crate::leanh::lean_inc(v_a_3987_);
                crate::leanh::lean_inc_ref(v_a_3986_);
                crate::leanh::lean_inc(v_a_3985_);
                crate::leanh::lean_inc_ref(v_a_3984_);
                crate::leanh::lean_inc(v_a_3983_);
                v___x_3993_ = crate::leanh::lean_apply_11(
                    v_kp_3982_,
                    v_goal_3981_,
                    v_a_3983_,
                    v_a_3984_,
                    v_a_3985_,
                    v_a_3986_,
                    v_a_3987_,
                    v_a_3988_,
                    v_a_3989_,
                    v_a_3990_,
                    v_a_3991_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_3993_) == 0 {
                    v_a_3994_ = crate::leanh::lean_ctor_get(v___x_3993_, 0);
                    crate::leanh::lean_inc(v_a_3994_);
                    crate::leanh::lean_dec_ref_known(v___x_3993_, 1);
                    v___x_3995_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_3984_);
                    if crate::leanh::lean_obj_tag(v___x_3995_) == 0 {
                        v_a_3996_ = crate::leanh::lean_ctor_get(v___x_3995_, 0);
                        v_isSharedCheck_4089_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3995_)) as u8;
                        if v_isSharedCheck_4089_ == 0 {
                            v___x_3998_ = v___x_3995_;
                            v_isShared_3999_ = v_isSharedCheck_4089_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3996_);
                            crate::leanh::lean_dec(v___x_3995_);
                            v___x_3998_ = crate::leanh::lean_box(0);
                            v_isShared_3999_ = v_isSharedCheck_4089_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3994_);
                        v_a_4090_ = crate::leanh::lean_ctor_get(v___x_3995_, 0);
                        v_isSharedCheck_4097_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3995_)) as u8;
                        if v_isSharedCheck_4097_ == 0 {
                            v___x_4092_ = v___x_3995_;
                            v_isShared_4093_ = v_isSharedCheck_4097_;
                            state = 18;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4090_);
                            crate::leanh::lean_dec(v___x_3995_);
                            v___x_4092_ = crate::leanh::lean_box(0);
                            v_isShared_4093_ = v_isSharedCheck_4097_;
                            state = 18;
                            continue;
                        }
                    }
                } else {
                    return v___x_3993_;
                }
            }
            1 => {
                v_trace_4000_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3996_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13) as u32,
                );
                crate::leanh::lean_dec(v_a_3996_);
                if v_trace_4000_ == 0 {
                    if v_isShared_3999_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3998_, 0, v_a_3994_);
                        v___x_4002_ = v___x_3998_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4003_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4003_, 0, v_a_3994_);
                        v___x_4002_ = v_reuseFailAlloc_4003_;
                        state = 2;
                        continue;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_a_3994_) == 0 {
                        v_seq_4004_ = crate::leanh::lean_ctor_get(v_a_3994_, 0);
                        if crate::leanh::lean_obj_tag(v_seq_4004_) == 1 {
                            v_tail_4005_ = crate::leanh::lean_ctor_get(v_seq_4004_, 1);
                            if crate::leanh::lean_obj_tag(v_tail_4005_) == 0 {
                                v_head_4006_ = crate::leanh::lean_ctor_get(v_seq_4004_, 0);
                                v___x_4007_ = l_Lean_Meta_Grind_Action_ungroup___redArg___closed__1;
                                crate::leanh::lean_inc(v_head_4006_);
                                v___x_4008_ = l_Lean_Syntax_isOfKind(v_head_4006_, v___x_4007_);
                                if v___x_4008_ == 0 {
                                    v___x_4009_ =
                                        l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__1;
                                    crate::leanh::lean_inc(v_head_4006_);
                                    v___x_4010_ = l_Lean_Syntax_isOfKind(v_head_4006_, v___x_4009_);
                                    if v___x_4010_ == 0 {
                                        if v_isShared_3999_ == 0 {
                                            crate::leanh::lean_ctor_set(v___x_3998_, 0, v_a_3994_);
                                            v___x_4012_ = v___x_3998_;
                                            state = 3;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_4013_ =
                                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_4013_,
                                                0,
                                                v_a_3994_,
                                            );
                                            v___x_4012_ = v_reuseFailAlloc_4013_;
                                            state = 3;
                                            continue;
                                        }
                                    } else {
                                        v___x_4014_ = crate::leanh::lean_unsigned_to_nat(1);
                                        v___x_4015_ =
                                            l_Lean_Syntax_getArg(v_head_4006_, v___x_4014_);
                                        v___x_4016_ =
                                            l_Lean_Meta_Grind_Action_mkGrindSeq___closed__3;
                                        crate::leanh::lean_inc(v___x_4015_);
                                        v___x_4017_ =
                                            l_Lean_Syntax_isOfKind(v___x_4015_, v___x_4016_);
                                        if v___x_4017_ == 0 {
                                            crate::leanh::lean_dec(v___x_4015_);
                                            if v_isShared_3999_ == 0 {
                                                crate::leanh::lean_ctor_set(
                                                    v___x_3998_,
                                                    0,
                                                    v_a_3994_,
                                                );
                                                v___x_4019_ = v___x_3998_;
                                                state = 4;
                                                continue;
                                            } else {
                                                v_reuseFailAlloc_4020_ =
                                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                                crate::leanh::lean_ctor_set(
                                                    v_reuseFailAlloc_4020_,
                                                    0,
                                                    v_a_3994_,
                                                );
                                                v___x_4019_ = v_reuseFailAlloc_4020_;
                                                state = 4;
                                                continue;
                                            }
                                        } else {
                                            v___x_4021_ = crate::leanh::lean_unsigned_to_nat(0);
                                            v___x_4022_ =
                                                l_Lean_Syntax_getArg(v___x_4015_, v___x_4021_);
                                            crate::leanh::lean_dec(v___x_4015_);
                                            v___x_4023_ =
                                                l_Lean_Meta_Grind_Action_mkGrindSeq___closed__5;
                                            crate::leanh::lean_inc(v___x_4022_);
                                            v___x_4024_ =
                                                l_Lean_Syntax_isOfKind(v___x_4022_, v___x_4023_);
                                            if v___x_4024_ == 0 {
                                                crate::leanh::lean_dec(v___x_4022_);
                                                if v_isShared_3999_ == 0 {
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_3998_,
                                                        0,
                                                        v_a_3994_,
                                                    );
                                                    v___x_4026_ = v___x_3998_;
                                                    state = 5;
                                                    continue;
                                                } else {
                                                    v_reuseFailAlloc_4027_ =
                                                        crate::leanh::lean_alloc_ctor(
                                                            0,
                                                            1,
                                                            (0) as u32,
                                                        );
                                                    crate::leanh::lean_ctor_set(
                                                        v_reuseFailAlloc_4027_,
                                                        0,
                                                        v_a_3994_,
                                                    );
                                                    v___x_4026_ = v_reuseFailAlloc_4027_;
                                                    state = 5;
                                                    continue;
                                                }
                                            } else {
                                                crate::leanh::lean_inc(v_tail_4005_);
                                                v_isSharedCheck_4042_ =
                                                    (!crate::leanh::lean_is_exclusive(v_a_3994_))
                                                        as u8;
                                                if v_isSharedCheck_4042_ == 0 {
                                                    v_unused_4043_ =
                                                        crate::leanh::lean_ctor_get(v_a_3994_, 0);
                                                    crate::leanh::lean_dec(v_unused_4043_);
                                                    v___x_4029_ = v_a_3994_;
                                                    v_isShared_4030_ = v_isSharedCheck_4042_;
                                                    state = 6;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_dec(v_a_3994_);
                                                    v___x_4029_ = crate::leanh::lean_box(0);
                                                    v_isShared_4030_ = v_isSharedCheck_4042_;
                                                    state = 6;
                                                    continue;
                                                }
                                            }
                                        }
                                    }
                                } else {
                                    v___x_4044_ = crate::leanh::lean_unsigned_to_nat(0);
                                    v___x_4045_ = crate::leanh::lean_unsigned_to_nat(1);
                                    v___x_4046_ = l_Lean_Syntax_getArg(v_head_4006_, v___x_4045_);
                                    v___x_4047_ =
                                        l_Lean_Syntax_matchesNull(v___x_4046_, v___x_4044_);
                                    if v___x_4047_ == 0 {
                                        if v_isShared_3999_ == 0 {
                                            crate::leanh::lean_ctor_set(v___x_3998_, 0, v_a_3994_);
                                            v___x_4049_ = v___x_3998_;
                                            state = 9;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_4050_ =
                                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_4050_,
                                                0,
                                                v_a_3994_,
                                            );
                                            v___x_4049_ = v_reuseFailAlloc_4050_;
                                            state = 9;
                                            continue;
                                        }
                                    } else {
                                        v___x_4051_ = crate::leanh::lean_unsigned_to_nat(3);
                                        v___x_4052_ =
                                            l_Lean_Syntax_getArg(v_head_4006_, v___x_4051_);
                                        v___x_4053_ =
                                            l_Lean_Meta_Grind_Action_mkGrindSeq___closed__3;
                                        crate::leanh::lean_inc(v___x_4052_);
                                        v___x_4054_ =
                                            l_Lean_Syntax_isOfKind(v___x_4052_, v___x_4053_);
                                        if v___x_4054_ == 0 {
                                            crate::leanh::lean_dec(v___x_4052_);
                                            if v_isShared_3999_ == 0 {
                                                crate::leanh::lean_ctor_set(
                                                    v___x_3998_,
                                                    0,
                                                    v_a_3994_,
                                                );
                                                v___x_4056_ = v___x_3998_;
                                                state = 10;
                                                continue;
                                            } else {
                                                v_reuseFailAlloc_4057_ =
                                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                                crate::leanh::lean_ctor_set(
                                                    v_reuseFailAlloc_4057_,
                                                    0,
                                                    v_a_3994_,
                                                );
                                                v___x_4056_ = v_reuseFailAlloc_4057_;
                                                state = 10;
                                                continue;
                                            }
                                        } else {
                                            v___x_4058_ =
                                                l_Lean_Syntax_getArg(v___x_4052_, v___x_4044_);
                                            crate::leanh::lean_dec(v___x_4052_);
                                            v___x_4059_ =
                                                l_Lean_Meta_Grind_Action_mkGrindSeq___closed__5;
                                            crate::leanh::lean_inc(v___x_4058_);
                                            v___x_4060_ =
                                                l_Lean_Syntax_isOfKind(v___x_4058_, v___x_4059_);
                                            if v___x_4060_ == 0 {
                                                crate::leanh::lean_dec(v___x_4058_);
                                                if v_isShared_3999_ == 0 {
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_3998_,
                                                        0,
                                                        v_a_3994_,
                                                    );
                                                    v___x_4062_ = v___x_3998_;
                                                    state = 11;
                                                    continue;
                                                } else {
                                                    v_reuseFailAlloc_4063_ =
                                                        crate::leanh::lean_alloc_ctor(
                                                            0,
                                                            1,
                                                            (0) as u32,
                                                        );
                                                    crate::leanh::lean_ctor_set(
                                                        v_reuseFailAlloc_4063_,
                                                        0,
                                                        v_a_3994_,
                                                    );
                                                    v___x_4062_ = v_reuseFailAlloc_4063_;
                                                    state = 11;
                                                    continue;
                                                }
                                            } else {
                                                crate::leanh::lean_inc(v_tail_4005_);
                                                v_isSharedCheck_4078_ =
                                                    (!crate::leanh::lean_is_exclusive(v_a_3994_))
                                                        as u8;
                                                if v_isSharedCheck_4078_ == 0 {
                                                    v_unused_4079_ =
                                                        crate::leanh::lean_ctor_get(v_a_3994_, 0);
                                                    crate::leanh::lean_dec(v_unused_4079_);
                                                    v___x_4065_ = v_a_3994_;
                                                    v_isShared_4066_ = v_isSharedCheck_4078_;
                                                    state = 12;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_dec(v_a_3994_);
                                                    v___x_4065_ = crate::leanh::lean_box(0);
                                                    v_isShared_4066_ = v_isSharedCheck_4078_;
                                                    state = 12;
                                                    continue;
                                                }
                                            }
                                        }
                                    }
                                }
                            } else {
                                if v_isShared_3999_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_3998_, 0, v_a_3994_);
                                    v___x_4081_ = v___x_3998_;
                                    state = 15;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_4082_ =
                                        crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4082_,
                                        0,
                                        v_a_3994_,
                                    );
                                    v___x_4081_ = v_reuseFailAlloc_4082_;
                                    state = 15;
                                    continue;
                                }
                            }
                        } else {
                            if v_isShared_3999_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_3998_, 0, v_a_3994_);
                                v___x_4084_ = v___x_3998_;
                                state = 16;
                                continue;
                            } else {
                                v_reuseFailAlloc_4085_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4085_, 0, v_a_3994_);
                                v___x_4084_ = v_reuseFailAlloc_4085_;
                                state = 16;
                                continue;
                            }
                        }
                    } else {
                        if v_isShared_3999_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3998_, 0, v_a_3994_);
                            v___x_4087_ = v___x_3998_;
                            state = 17;
                            continue;
                        } else {
                            v_reuseFailAlloc_4088_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4088_, 0, v_a_3994_);
                            v___x_4087_ = v_reuseFailAlloc_4088_;
                            state = 17;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_4002_;
            }
            3 => {
                return v___x_4012_;
            }
            4 => {
                return v___x_4019_;
            }
            5 => {
                return v___x_4026_;
            }
            6 => {
                v___x_4031_ = l_Lean_Syntax_getArg(v___x_4022_, v___x_4021_);
                crate::leanh::lean_dec(v___x_4022_);
                v___x_4032_ = l_Lean_Syntax_getArgs(v___x_4031_);
                crate::leanh::lean_dec(v___x_4031_);
                v___x_4033_ = l_Lean_Syntax_TSepArray_getElems___redArg(v___x_4032_);
                crate::leanh::lean_dec_ref(v___x_4032_);
                v___x_4034_ = lean_array_to_list(v___x_4033_);
                v___x_4035_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Action_ungroup_spec__0(
                    v___x_4034_,
                    v_tail_4005_,
                );
                if v_isShared_4030_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4029_, 0, v___x_4035_);
                    v___x_4037_ = v___x_4029_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4041_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4041_, 0, v___x_4035_);
                    v___x_4037_ = v_reuseFailAlloc_4041_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_3999_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3998_, 0, v___x_4037_);
                    v___x_4039_ = v___x_3998_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4040_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4040_, 0, v___x_4037_);
                    v___x_4039_ = v_reuseFailAlloc_4040_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4039_;
            }
            9 => {
                return v___x_4049_;
            }
            10 => {
                return v___x_4056_;
            }
            11 => {
                return v___x_4062_;
            }
            12 => {
                v___x_4067_ = l_Lean_Syntax_getArg(v___x_4058_, v___x_4044_);
                crate::leanh::lean_dec(v___x_4058_);
                v___x_4068_ = l_Lean_Syntax_getArgs(v___x_4067_);
                crate::leanh::lean_dec(v___x_4067_);
                v___x_4069_ = l_Lean_Syntax_TSepArray_getElems___redArg(v___x_4068_);
                crate::leanh::lean_dec_ref(v___x_4068_);
                v___x_4070_ = lean_array_to_list(v___x_4069_);
                v___x_4071_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Action_ungroup_spec__0(
                    v___x_4070_,
                    v_tail_4005_,
                );
                if v_isShared_4066_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4065_, 0, v___x_4071_);
                    v___x_4073_ = v___x_4065_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4077_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4077_, 0, v___x_4071_);
                    v___x_4073_ = v_reuseFailAlloc_4077_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_3999_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3998_, 0, v___x_4073_);
                    v___x_4075_ = v___x_3998_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4076_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4076_, 0, v___x_4073_);
                    v___x_4075_ = v_reuseFailAlloc_4076_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4075_;
            }
            15 => {
                return v___x_4081_;
            }
            16 => {
                return v___x_4084_;
            }
            17 => {
                return v___x_4087_;
            }
            18 => {
                if v_isShared_4093_ == 0 {
                    v___x_4095_ = v___x_4092_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_4096_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4096_, 0, v_a_4090_);
                    v___x_4095_ = v_reuseFailAlloc_4096_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_4095_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Action_ungroup___redArg___boxed(
    mut v_goal_4098_: *mut crate::leanh::LeanObject,
    mut v_kp_4099_: *mut crate::leanh::LeanObject,
    mut v_a_4100_: *mut crate::leanh::LeanObject,
    mut v_a_4101_: *mut crate::leanh::LeanObject,
    mut v_a_4102_: *mut crate::leanh::LeanObject,
    mut v_a_4103_: *mut crate::leanh::LeanObject,
    mut v_a_4104_: *mut crate::leanh::LeanObject,
    mut v_a_4105_: *mut crate::leanh::LeanObject,
    mut v_a_4106_: *mut crate::leanh::LeanObject,
    mut v_a_4107_: *mut crate::leanh::LeanObject,
    mut v_a_4108_: *mut crate::leanh::LeanObject,
    mut v_a_4109_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4110_ = l_Lean_Meta_Grind_Action_ungroup___redArg(
        v_goal_4098_,
        v_kp_4099_,
        v_a_4100_,
        v_a_4101_,
        v_a_4102_,
        v_a_4103_,
        v_a_4104_,
        v_a_4105_,
        v_a_4106_,
        v_a_4107_,
        v_a_4108_,
    );
    crate::leanh::lean_dec(v_a_4108_);
    crate::leanh::lean_dec_ref(v_a_4107_);
    crate::leanh::lean_dec(v_a_4106_);
    crate::leanh::lean_dec_ref(v_a_4105_);
    crate::leanh::lean_dec(v_a_4104_);
    crate::leanh::lean_dec_ref(v_a_4103_);
    crate::leanh::lean_dec(v_a_4102_);
    crate::leanh::lean_dec_ref(v_a_4101_);
    crate::leanh::lean_dec(v_a_4100_);
    return v_res_4110_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_ungroup(
    mut v_goal_4111_: *mut crate::leanh::LeanObject,
    mut v_x_4112_: *mut crate::leanh::LeanObject,
    mut v_kp_4113_: *mut crate::leanh::LeanObject,
    mut v_a_4114_: *mut crate::leanh::LeanObject,
    mut v_a_4115_: *mut crate::leanh::LeanObject,
    mut v_a_4116_: *mut crate::leanh::LeanObject,
    mut v_a_4117_: *mut crate::leanh::LeanObject,
    mut v_a_4118_: *mut crate::leanh::LeanObject,
    mut v_a_4119_: *mut crate::leanh::LeanObject,
    mut v_a_4120_: *mut crate::leanh::LeanObject,
    mut v_a_4121_: *mut crate::leanh::LeanObject,
    mut v_a_4122_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4124_ = l_Lean_Meta_Grind_Action_ungroup___redArg(
        v_goal_4111_,
        v_kp_4113_,
        v_a_4114_,
        v_a_4115_,
        v_a_4116_,
        v_a_4117_,
        v_a_4118_,
        v_a_4119_,
        v_a_4120_,
        v_a_4121_,
        v_a_4122_,
    );
    return v___x_4124_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_ungroup___boxed(
    mut v_goal_4125_: *mut crate::leanh::LeanObject,
    mut v_x_4126_: *mut crate::leanh::LeanObject,
    mut v_kp_4127_: *mut crate::leanh::LeanObject,
    mut v_a_4128_: *mut crate::leanh::LeanObject,
    mut v_a_4129_: *mut crate::leanh::LeanObject,
    mut v_a_4130_: *mut crate::leanh::LeanObject,
    mut v_a_4131_: *mut crate::leanh::LeanObject,
    mut v_a_4132_: *mut crate::leanh::LeanObject,
    mut v_a_4133_: *mut crate::leanh::LeanObject,
    mut v_a_4134_: *mut crate::leanh::LeanObject,
    mut v_a_4135_: *mut crate::leanh::LeanObject,
    mut v_a_4136_: *mut crate::leanh::LeanObject,
    mut v_a_4137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4138_ = l_Lean_Meta_Grind_Action_ungroup(
        v_goal_4125_,
        v_x_4126_,
        v_kp_4127_,
        v_a_4128_,
        v_a_4129_,
        v_a_4130_,
        v_a_4131_,
        v_a_4132_,
        v_a_4133_,
        v_a_4134_,
        v_a_4135_,
        v_a_4136_,
    );
    crate::leanh::lean_dec(v_a_4136_);
    crate::leanh::lean_dec_ref(v_a_4135_);
    crate::leanh::lean_dec(v_a_4134_);
    crate::leanh::lean_dec_ref(v_a_4133_);
    crate::leanh::lean_dec(v_a_4132_);
    crate::leanh::lean_dec_ref(v_a_4131_);
    crate::leanh::lean_dec(v_a_4130_);
    crate::leanh::lean_dec_ref(v_a_4129_);
    crate::leanh::lean_dec(v_a_4128_);
    crate::leanh::lean_dec_ref(v_x_4126_);
    return v_res_4138_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_concatTactic(
    mut v_r_4139_: *mut crate::leanh::LeanObject,
    mut v_mk_4140_: *mut crate::leanh::LeanObject,
    mut v_a_4141_: *mut crate::leanh::LeanObject,
    mut v_a_4142_: *mut crate::leanh::LeanObject,
    mut v_a_4143_: *mut crate::leanh::LeanObject,
    mut v_a_4144_: *mut crate::leanh::LeanObject,
    mut v_a_4145_: *mut crate::leanh::LeanObject,
    mut v_a_4146_: *mut crate::leanh::LeanObject,
    mut v_a_4147_: *mut crate::leanh::LeanObject,
    mut v_a_4148_: *mut crate::leanh::LeanObject,
    mut v_a_4149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4155_: u8 = 0;
    let mut v_trace_4156_: u8 = 0;
    let mut v___x_4158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_seq_4160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4163_: u8 = 0;
    let mut v___x_4164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4168_: u8 = 0;
    let mut v___x_4169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4176_: u8 = 0;
    let mut v_a_4177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4180_: u8 = 0;
    let mut v___x_4182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4184_: u8 = 0;
    let mut v_isSharedCheck_4185_: u8 = 0;
    let mut v___x_4187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4189_: u8 = 0;
    let mut v_a_4190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4193_: u8 = 0;
    let mut v___x_4195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4197_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4151_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_4142_);
                if crate::leanh::lean_obj_tag(v___x_4151_) == 0 {
                    v_a_4152_ = crate::leanh::lean_ctor_get(v___x_4151_, 0);
                    v_isSharedCheck_4189_ = (!crate::leanh::lean_is_exclusive(v___x_4151_)) as u8;
                    if v_isSharedCheck_4189_ == 0 {
                        v___x_4154_ = v___x_4151_;
                        v_isShared_4155_ = v_isSharedCheck_4189_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4152_);
                        crate::leanh::lean_dec(v___x_4151_);
                        v___x_4154_ = crate::leanh::lean_box(0);
                        v_isShared_4155_ = v_isSharedCheck_4189_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_mk_4140_);
                    crate::leanh::lean_dec_ref(v_r_4139_);
                    v_a_4190_ = crate::leanh::lean_ctor_get(v___x_4151_, 0);
                    v_isSharedCheck_4197_ = (!crate::leanh::lean_is_exclusive(v___x_4151_)) as u8;
                    if v_isSharedCheck_4197_ == 0 {
                        v___x_4192_ = v___x_4151_;
                        v_isShared_4193_ = v_isSharedCheck_4197_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4190_);
                        crate::leanh::lean_dec(v___x_4151_);
                        v___x_4192_ = crate::leanh::lean_box(0);
                        v_isShared_4193_ = v_isSharedCheck_4197_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v_trace_4156_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_4152_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13) as u32,
                );
                crate::leanh::lean_dec(v_a_4152_);
                if v_trace_4156_ == 0 {
                    crate::leanh::lean_dec_ref(v_mk_4140_);
                    if v_isShared_4155_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4154_, 0, v_r_4139_);
                        v___x_4158_ = v___x_4154_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4159_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4159_, 0, v_r_4139_);
                        v___x_4158_ = v_reuseFailAlloc_4159_;
                        state = 2;
                        continue;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_r_4139_) == 0 {
                        crate::leanh::lean_del_object(v___x_4154_);
                        v_seq_4160_ = crate::leanh::lean_ctor_get(v_r_4139_, 0);
                        v_isSharedCheck_4185_ = (!crate::leanh::lean_is_exclusive(v_r_4139_)) as u8;
                        if v_isSharedCheck_4185_ == 0 {
                            v___x_4162_ = v_r_4139_;
                            v_isShared_4163_ = v_isSharedCheck_4185_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_seq_4160_);
                            crate::leanh::lean_dec(v_r_4139_);
                            v___x_4162_ = crate::leanh::lean_box(0);
                            v_isShared_4163_ = v_isSharedCheck_4185_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_mk_4140_);
                        if v_isShared_4155_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4154_, 0, v_r_4139_);
                            v___x_4187_ = v___x_4154_;
                            state = 9;
                            continue;
                        } else {
                            v_reuseFailAlloc_4188_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4188_, 0, v_r_4139_);
                            v___x_4187_ = v_reuseFailAlloc_4188_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_4158_;
            }
            3 => {
                crate::leanh::lean_inc(v_a_4149_);
                crate::leanh::lean_inc_ref(v_a_4148_);
                crate::leanh::lean_inc(v_a_4147_);
                crate::leanh::lean_inc_ref(v_a_4146_);
                crate::leanh::lean_inc(v_a_4145_);
                crate::leanh::lean_inc_ref(v_a_4144_);
                crate::leanh::lean_inc(v_a_4143_);
                crate::leanh::lean_inc_ref(v_a_4142_);
                crate::leanh::lean_inc(v_a_4141_);
                v___x_4164_ = crate::leanh::lean_apply_10(
                    v_mk_4140_,
                    v_a_4141_,
                    v_a_4142_,
                    v_a_4143_,
                    v_a_4144_,
                    v_a_4145_,
                    v_a_4146_,
                    v_a_4147_,
                    v_a_4148_,
                    v_a_4149_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_4164_) == 0 {
                    v_a_4165_ = crate::leanh::lean_ctor_get(v___x_4164_, 0);
                    v_isSharedCheck_4176_ = (!crate::leanh::lean_is_exclusive(v___x_4164_)) as u8;
                    if v_isSharedCheck_4176_ == 0 {
                        v___x_4167_ = v___x_4164_;
                        v_isShared_4168_ = v_isSharedCheck_4176_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4165_);
                        crate::leanh::lean_dec(v___x_4164_);
                        v___x_4167_ = crate::leanh::lean_box(0);
                        v_isShared_4168_ = v_isSharedCheck_4176_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4162_);
                    crate::leanh::lean_dec(v_seq_4160_);
                    v_a_4177_ = crate::leanh::lean_ctor_get(v___x_4164_, 0);
                    v_isSharedCheck_4184_ = (!crate::leanh::lean_is_exclusive(v___x_4164_)) as u8;
                    if v_isSharedCheck_4184_ == 0 {
                        v___x_4179_ = v___x_4164_;
                        v_isShared_4180_ = v_isSharedCheck_4184_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4177_);
                        crate::leanh::lean_dec(v___x_4164_);
                        v___x_4179_ = crate::leanh::lean_box(0);
                        v_isShared_4180_ = v_isSharedCheck_4184_;
                        state = 7;
                        continue;
                    }
                }
            }
            4 => {
                v___x_4169_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4169_, 0, v_a_4165_);
                crate::leanh::lean_ctor_set(v___x_4169_, 1, v_seq_4160_);
                if v_isShared_4163_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4162_, 0, v___x_4169_);
                    v___x_4171_ = v___x_4162_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4175_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4175_, 0, v___x_4169_);
                    v___x_4171_ = v_reuseFailAlloc_4175_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_4168_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4167_, 0, v___x_4171_);
                    v___x_4173_ = v___x_4167_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4174_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4174_, 0, v___x_4171_);
                    v___x_4173_ = v_reuseFailAlloc_4174_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4173_;
            }
            7 => {
                if v_isShared_4180_ == 0 {
                    v___x_4182_ = v___x_4179_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4183_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4183_, 0, v_a_4177_);
                    v___x_4182_ = v_reuseFailAlloc_4183_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4182_;
            }
            9 => {
                return v___x_4187_;
            }
            10 => {
                if v_isShared_4193_ == 0 {
                    v___x_4195_ = v___x_4192_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4196_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4196_, 0, v_a_4190_);
                    v___x_4195_ = v_reuseFailAlloc_4196_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4195_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Action_concatTactic___boxed(
    mut v_r_4198_: *mut crate::leanh::LeanObject,
    mut v_mk_4199_: *mut crate::leanh::LeanObject,
    mut v_a_4200_: *mut crate::leanh::LeanObject,
    mut v_a_4201_: *mut crate::leanh::LeanObject,
    mut v_a_4202_: *mut crate::leanh::LeanObject,
    mut v_a_4203_: *mut crate::leanh::LeanObject,
    mut v_a_4204_: *mut crate::leanh::LeanObject,
    mut v_a_4205_: *mut crate::leanh::LeanObject,
    mut v_a_4206_: *mut crate::leanh::LeanObject,
    mut v_a_4207_: *mut crate::leanh::LeanObject,
    mut v_a_4208_: *mut crate::leanh::LeanObject,
    mut v_a_4209_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4210_ = l_Lean_Meta_Grind_Action_concatTactic(
        v_r_4198_, v_mk_4199_, v_a_4200_, v_a_4201_, v_a_4202_, v_a_4203_, v_a_4204_, v_a_4205_,
        v_a_4206_, v_a_4207_, v_a_4208_,
    );
    crate::leanh::lean_dec(v_a_4208_);
    crate::leanh::lean_dec_ref(v_a_4207_);
    crate::leanh::lean_dec(v_a_4206_);
    crate::leanh::lean_dec_ref(v_a_4205_);
    crate::leanh::lean_dec(v_a_4204_);
    crate::leanh::lean_dec_ref(v_a_4203_);
    crate::leanh::lean_dec(v_a_4202_);
    crate::leanh::lean_dec_ref(v_a_4201_);
    crate::leanh::lean_dec(v_a_4200_);
    return v_res_4210_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_closeWith(
    mut v_mk_4211_: *mut crate::leanh::LeanObject,
    mut v_a_4212_: *mut crate::leanh::LeanObject,
    mut v_a_4213_: *mut crate::leanh::LeanObject,
    mut v_a_4214_: *mut crate::leanh::LeanObject,
    mut v_a_4215_: *mut crate::leanh::LeanObject,
    mut v_a_4216_: *mut crate::leanh::LeanObject,
    mut v_a_4217_: *mut crate::leanh::LeanObject,
    mut v_a_4218_: *mut crate::leanh::LeanObject,
    mut v_a_4219_: *mut crate::leanh::LeanObject,
    mut v_a_4220_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4226_: u8 = 0;
    let mut v_trace_4227_: u8 = 0;
    let mut v___x_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4236_: u8 = 0;
    let mut v___x_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4243_: u8 = 0;
    let mut v_a_4244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4247_: u8 = 0;
    let mut v___x_4249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4251_: u8 = 0;
    let mut v_isSharedCheck_4252_: u8 = 0;
    let mut v_a_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4256_: u8 = 0;
    let mut v___x_4258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4260_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4222_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_4213_);
                if crate::leanh::lean_obj_tag(v___x_4222_) == 0 {
                    v_a_4223_ = crate::leanh::lean_ctor_get(v___x_4222_, 0);
                    v_isSharedCheck_4252_ = (!crate::leanh::lean_is_exclusive(v___x_4222_)) as u8;
                    if v_isSharedCheck_4252_ == 0 {
                        v___x_4225_ = v___x_4222_;
                        v_isShared_4226_ = v_isSharedCheck_4252_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4223_);
                        crate::leanh::lean_dec(v___x_4222_);
                        v___x_4225_ = crate::leanh::lean_box(0);
                        v_isShared_4226_ = v_isSharedCheck_4252_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_mk_4211_);
                    v_a_4253_ = crate::leanh::lean_ctor_get(v___x_4222_, 0);
                    v_isSharedCheck_4260_ = (!crate::leanh::lean_is_exclusive(v___x_4222_)) as u8;
                    if v_isSharedCheck_4260_ == 0 {
                        v___x_4255_ = v___x_4222_;
                        v_isShared_4256_ = v_isSharedCheck_4260_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4253_);
                        crate::leanh::lean_dec(v___x_4222_);
                        v___x_4255_ = crate::leanh::lean_box(0);
                        v_isShared_4256_ = v_isSharedCheck_4260_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_trace_4227_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_4223_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13) as u32,
                );
                crate::leanh::lean_dec(v_a_4223_);
                if v_trace_4227_ == 0 {
                    crate::leanh::lean_dec_ref(v_mk_4211_);
                    v___x_4228_ = l_Lean_Meta_Grind_Action_done___redArg___closed__0;
                    if v_isShared_4226_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4225_, 0, v___x_4228_);
                        v___x_4230_ = v___x_4225_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4231_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4231_, 0, v___x_4228_);
                        v___x_4230_ = v_reuseFailAlloc_4231_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4225_);
                    crate::leanh::lean_inc(v_a_4220_);
                    crate::leanh::lean_inc_ref(v_a_4219_);
                    crate::leanh::lean_inc(v_a_4218_);
                    crate::leanh::lean_inc_ref(v_a_4217_);
                    crate::leanh::lean_inc(v_a_4216_);
                    crate::leanh::lean_inc_ref(v_a_4215_);
                    crate::leanh::lean_inc(v_a_4214_);
                    crate::leanh::lean_inc_ref(v_a_4213_);
                    crate::leanh::lean_inc(v_a_4212_);
                    v___x_4232_ = crate::leanh::lean_apply_10(
                        v_mk_4211_,
                        v_a_4212_,
                        v_a_4213_,
                        v_a_4214_,
                        v_a_4215_,
                        v_a_4216_,
                        v_a_4217_,
                        v_a_4218_,
                        v_a_4219_,
                        v_a_4220_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_4232_) == 0 {
                        v_a_4233_ = crate::leanh::lean_ctor_get(v___x_4232_, 0);
                        v_isSharedCheck_4243_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4232_)) as u8;
                        if v_isSharedCheck_4243_ == 0 {
                            v___x_4235_ = v___x_4232_;
                            v_isShared_4236_ = v_isSharedCheck_4243_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4233_);
                            crate::leanh::lean_dec(v___x_4232_);
                            v___x_4235_ = crate::leanh::lean_box(0);
                            v_isShared_4236_ = v_isSharedCheck_4243_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_4244_ = crate::leanh::lean_ctor_get(v___x_4232_, 0);
                        v_isSharedCheck_4251_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4232_)) as u8;
                        if v_isSharedCheck_4251_ == 0 {
                            v___x_4246_ = v___x_4232_;
                            v_isShared_4247_ = v_isSharedCheck_4251_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4244_);
                            crate::leanh::lean_dec(v___x_4232_);
                            v___x_4246_ = crate::leanh::lean_box(0);
                            v_isShared_4247_ = v_isSharedCheck_4251_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_4230_;
            }
            3 => {
                v___x_4237_ = crate::leanh::lean_box(0);
                v___x_4238_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4238_, 0, v_a_4233_);
                crate::leanh::lean_ctor_set(v___x_4238_, 1, v___x_4237_);
                v___x_4239_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4239_, 0, v___x_4238_);
                if v_isShared_4236_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4235_, 0, v___x_4239_);
                    v___x_4241_ = v___x_4235_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4242_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4242_, 0, v___x_4239_);
                    v___x_4241_ = v_reuseFailAlloc_4242_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4241_;
            }
            5 => {
                if v_isShared_4247_ == 0 {
                    v___x_4249_ = v___x_4246_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4250_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4250_, 0, v_a_4244_);
                    v___x_4249_ = v_reuseFailAlloc_4250_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4249_;
            }
            7 => {
                if v_isShared_4256_ == 0 {
                    v___x_4258_ = v___x_4255_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4259_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4259_, 0, v_a_4253_);
                    v___x_4258_ = v_reuseFailAlloc_4259_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4258_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Action_closeWith___boxed(
    mut v_mk_4261_: *mut crate::leanh::LeanObject,
    mut v_a_4262_: *mut crate::leanh::LeanObject,
    mut v_a_4263_: *mut crate::leanh::LeanObject,
    mut v_a_4264_: *mut crate::leanh::LeanObject,
    mut v_a_4265_: *mut crate::leanh::LeanObject,
    mut v_a_4266_: *mut crate::leanh::LeanObject,
    mut v_a_4267_: *mut crate::leanh::LeanObject,
    mut v_a_4268_: *mut crate::leanh::LeanObject,
    mut v_a_4269_: *mut crate::leanh::LeanObject,
    mut v_a_4270_: *mut crate::leanh::LeanObject,
    mut v_a_4271_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4272_ = l_Lean_Meta_Grind_Action_closeWith(
        v_mk_4261_, v_a_4262_, v_a_4263_, v_a_4264_, v_a_4265_, v_a_4266_, v_a_4267_, v_a_4268_,
        v_a_4269_, v_a_4270_,
    );
    crate::leanh::lean_dec(v_a_4270_);
    crate::leanh::lean_dec_ref(v_a_4269_);
    crate::leanh::lean_dec(v_a_4268_);
    crate::leanh::lean_dec_ref(v_a_4267_);
    crate::leanh::lean_dec(v_a_4266_);
    crate::leanh::lean_dec_ref(v_a_4265_);
    crate::leanh::lean_dec(v_a_4264_);
    crate::leanh::lean_dec_ref(v_a_4263_);
    crate::leanh::lean_dec(v_a_4262_);
    return v_res_4272_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg___lam__0(
    mut v_x_4273_: *mut crate::leanh::LeanObject,
    mut v___y_4274_: *mut crate::leanh::LeanObject,
    mut v___y_4275_: *mut crate::leanh::LeanObject,
    mut v___y_4276_: *mut crate::leanh::LeanObject,
    mut v___y_4277_: *mut crate::leanh::LeanObject,
    mut v___y_4278_: *mut crate::leanh::LeanObject,
    mut v___y_4279_: *mut crate::leanh::LeanObject,
    mut v___y_4280_: *mut crate::leanh::LeanObject,
    mut v___y_4281_: *mut crate::leanh::LeanObject,
    mut v___y_4282_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_4278_);
    crate::leanh::lean_inc_ref(v___y_4277_);
    crate::leanh::lean_inc(v___y_4276_);
    crate::leanh::lean_inc_ref(v___y_4275_);
    crate::leanh::lean_inc(v___y_4274_);
    v___x_4284_ = crate::leanh::lean_apply_10(
        v_x_4273_,
        v___y_4274_,
        v___y_4275_,
        v___y_4276_,
        v___y_4277_,
        v___y_4278_,
        v___y_4279_,
        v___y_4280_,
        v___y_4281_,
        v___y_4282_,
        crate::leanh::lean_box(0),
    );
    return v___x_4284_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg___lam__0___boxed(
    mut v_x_4285_: *mut crate::leanh::LeanObject,
    mut v___y_4286_: *mut crate::leanh::LeanObject,
    mut v___y_4287_: *mut crate::leanh::LeanObject,
    mut v___y_4288_: *mut crate::leanh::LeanObject,
    mut v___y_4289_: *mut crate::leanh::LeanObject,
    mut v___y_4290_: *mut crate::leanh::LeanObject,
    mut v___y_4291_: *mut crate::leanh::LeanObject,
    mut v___y_4292_: *mut crate::leanh::LeanObject,
    mut v___y_4293_: *mut crate::leanh::LeanObject,
    mut v___y_4294_: *mut crate::leanh::LeanObject,
    mut v___y_4295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4296_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg___lam__0(v_x_4285_, v___y_4286_, v___y_4287_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_, v___y_4292_, v___y_4293_, v___y_4294_);
    crate::leanh::lean_dec(v___y_4290_);
    crate::leanh::lean_dec_ref(v___y_4289_);
    crate::leanh::lean_dec(v___y_4288_);
    crate::leanh::lean_dec_ref(v___y_4287_);
    crate::leanh::lean_dec(v___y_4286_);
    return v_res_4296_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg(
    mut v_mvarId_4297_: *mut crate::leanh::LeanObject,
    mut v_x_4298_: *mut crate::leanh::LeanObject,
    mut v___y_4299_: *mut crate::leanh::LeanObject,
    mut v___y_4300_: *mut crate::leanh::LeanObject,
    mut v___y_4301_: *mut crate::leanh::LeanObject,
    mut v___y_4302_: *mut crate::leanh::LeanObject,
    mut v___y_4303_: *mut crate::leanh::LeanObject,
    mut v___y_4304_: *mut crate::leanh::LeanObject,
    mut v___y_4305_: *mut crate::leanh::LeanObject,
    mut v___y_4306_: *mut crate::leanh::LeanObject,
    mut v___y_4307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4314_: u8 = 0;
    let mut v___x_4316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4318_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_4303_);
                crate::leanh::lean_inc_ref(v___y_4302_);
                crate::leanh::lean_inc(v___y_4301_);
                crate::leanh::lean_inc_ref(v___y_4300_);
                crate::leanh::lean_inc(v___y_4299_);
                v___f_4309_ = crate::leanh::lean_alloc_closure(l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 11, 6);
                crate::leanh::lean_closure_set(v___f_4309_, 0, v_x_4298_);
                crate::leanh::lean_closure_set(v___f_4309_, 1, v___y_4299_);
                crate::leanh::lean_closure_set(v___f_4309_, 2, v___y_4300_);
                crate::leanh::lean_closure_set(v___f_4309_, 3, v___y_4301_);
                crate::leanh::lean_closure_set(v___f_4309_, 4, v___y_4302_);
                crate::leanh::lean_closure_set(v___f_4309_, 5, v___y_4303_);
                v___x_4310_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_4297_,
                    v___f_4309_,
                    v___y_4304_,
                    v___y_4305_,
                    v___y_4306_,
                    v___y_4307_,
                );
                if crate::leanh::lean_obj_tag(v___x_4310_) == 0 {
                    return v___x_4310_;
                } else {
                    v_a_4311_ = crate::leanh::lean_ctor_get(v___x_4310_, 0);
                    v_isSharedCheck_4318_ = (!crate::leanh::lean_is_exclusive(v___x_4310_)) as u8;
                    if v_isSharedCheck_4318_ == 0 {
                        v___x_4313_ = v___x_4310_;
                        v_isShared_4314_ = v_isSharedCheck_4318_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4311_);
                        crate::leanh::lean_dec(v___x_4310_);
                        v___x_4313_ = crate::leanh::lean_box(0);
                        v_isShared_4314_ = v_isSharedCheck_4318_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4314_ == 0 {
                    v___x_4316_ = v___x_4313_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4317_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4317_, 0, v_a_4311_);
                    v___x_4316_ = v_reuseFailAlloc_4317_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4316_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg___boxed(
    mut v_mvarId_4319_: *mut crate::leanh::LeanObject,
    mut v_x_4320_: *mut crate::leanh::LeanObject,
    mut v___y_4321_: *mut crate::leanh::LeanObject,
    mut v___y_4322_: *mut crate::leanh::LeanObject,
    mut v___y_4323_: *mut crate::leanh::LeanObject,
    mut v___y_4324_: *mut crate::leanh::LeanObject,
    mut v___y_4325_: *mut crate::leanh::LeanObject,
    mut v___y_4326_: *mut crate::leanh::LeanObject,
    mut v___y_4327_: *mut crate::leanh::LeanObject,
    mut v___y_4328_: *mut crate::leanh::LeanObject,
    mut v___y_4329_: *mut crate::leanh::LeanObject,
    mut v___y_4330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4331_ =
        l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg(
            v_mvarId_4319_,
            v_x_4320_,
            v___y_4321_,
            v___y_4322_,
            v___y_4323_,
            v___y_4324_,
            v___y_4325_,
            v___y_4326_,
            v___y_4327_,
            v___y_4328_,
            v___y_4329_,
        );
    crate::leanh::lean_dec(v___y_4329_);
    crate::leanh::lean_dec_ref(v___y_4328_);
    crate::leanh::lean_dec(v___y_4327_);
    crate::leanh::lean_dec_ref(v___y_4326_);
    crate::leanh::lean_dec(v___y_4325_);
    crate::leanh::lean_dec_ref(v___y_4324_);
    crate::leanh::lean_dec(v___y_4323_);
    crate::leanh::lean_dec_ref(v___y_4322_);
    crate::leanh::lean_dec(v___y_4321_);
    return v_res_4331_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0(
    mut v_00_u03b1_4332_: *mut crate::leanh::LeanObject,
    mut v_mvarId_4333_: *mut crate::leanh::LeanObject,
    mut v_x_4334_: *mut crate::leanh::LeanObject,
    mut v___y_4335_: *mut crate::leanh::LeanObject,
    mut v___y_4336_: *mut crate::leanh::LeanObject,
    mut v___y_4337_: *mut crate::leanh::LeanObject,
    mut v___y_4338_: *mut crate::leanh::LeanObject,
    mut v___y_4339_: *mut crate::leanh::LeanObject,
    mut v___y_4340_: *mut crate::leanh::LeanObject,
    mut v___y_4341_: *mut crate::leanh::LeanObject,
    mut v___y_4342_: *mut crate::leanh::LeanObject,
    mut v___y_4343_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4345_ =
        l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg(
            v_mvarId_4333_,
            v_x_4334_,
            v___y_4335_,
            v___y_4336_,
            v___y_4337_,
            v___y_4338_,
            v___y_4339_,
            v___y_4340_,
            v___y_4341_,
            v___y_4342_,
            v___y_4343_,
        );
    return v___x_4345_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___boxed(
    mut v_00_u03b1_4346_: *mut crate::leanh::LeanObject,
    mut v_mvarId_4347_: *mut crate::leanh::LeanObject,
    mut v_x_4348_: *mut crate::leanh::LeanObject,
    mut v___y_4349_: *mut crate::leanh::LeanObject,
    mut v___y_4350_: *mut crate::leanh::LeanObject,
    mut v___y_4351_: *mut crate::leanh::LeanObject,
    mut v___y_4352_: *mut crate::leanh::LeanObject,
    mut v___y_4353_: *mut crate::leanh::LeanObject,
    mut v___y_4354_: *mut crate::leanh::LeanObject,
    mut v___y_4355_: *mut crate::leanh::LeanObject,
    mut v___y_4356_: *mut crate::leanh::LeanObject,
    mut v___y_4357_: *mut crate::leanh::LeanObject,
    mut v___y_4358_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4359_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0(
        v_00_u03b1_4346_,
        v_mvarId_4347_,
        v_x_4348_,
        v___y_4349_,
        v___y_4350_,
        v___y_4351_,
        v___y_4352_,
        v___y_4353_,
        v___y_4354_,
        v___y_4355_,
        v___y_4356_,
        v___y_4357_,
    );
    crate::leanh::lean_dec(v___y_4357_);
    crate::leanh::lean_dec_ref(v___y_4356_);
    crate::leanh::lean_dec(v___y_4355_);
    crate::leanh::lean_dec_ref(v___y_4354_);
    crate::leanh::lean_dec(v___y_4353_);
    crate::leanh::lean_dec_ref(v___y_4352_);
    crate::leanh::lean_dec(v___y_4351_);
    crate::leanh::lean_dec_ref(v___y_4350_);
    crate::leanh::lean_dec(v___y_4349_);
    return v_res_4359_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_terminalAction___lam__0(
    mut v_goal_4360_: *mut crate::leanh::LeanObject,
    mut v_check_4361_: *mut crate::leanh::LeanObject,
    mut v___y_4362_: *mut crate::leanh::LeanObject,
    mut v___y_4363_: *mut crate::leanh::LeanObject,
    mut v___y_4364_: *mut crate::leanh::LeanObject,
    mut v___y_4365_: *mut crate::leanh::LeanObject,
    mut v___y_4366_: *mut crate::leanh::LeanObject,
    mut v___y_4367_: *mut crate::leanh::LeanObject,
    mut v___y_4368_: *mut crate::leanh::LeanObject,
    mut v___y_4369_: *mut crate::leanh::LeanObject,
    mut v___y_4370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4377_: u8 = 0;
    let mut v___x_4378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4383_: u8 = 0;
    let mut v_a_4384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4387_: u8 = 0;
    let mut v___x_4389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4391_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4372_ = lean_st_mk_ref(v_goal_4360_);
                crate::leanh::lean_inc(v___x_4372_);
                v___x_4373_ = crate::leanh::lean_apply_11(
                    v_check_4361_,
                    v___x_4372_,
                    v___y_4362_,
                    v___y_4363_,
                    v___y_4364_,
                    v___y_4365_,
                    v___y_4366_,
                    v___y_4367_,
                    v___y_4368_,
                    v___y_4369_,
                    v___y_4370_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_4373_) == 0 {
                    v_a_4374_ = crate::leanh::lean_ctor_get(v___x_4373_, 0);
                    v_isSharedCheck_4383_ = (!crate::leanh::lean_is_exclusive(v___x_4373_)) as u8;
                    if v_isSharedCheck_4383_ == 0 {
                        v___x_4376_ = v___x_4373_;
                        v_isShared_4377_ = v_isSharedCheck_4383_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4374_);
                        crate::leanh::lean_dec(v___x_4373_);
                        v___x_4376_ = crate::leanh::lean_box(0);
                        v_isShared_4377_ = v_isSharedCheck_4383_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4372_);
                    v_a_4384_ = crate::leanh::lean_ctor_get(v___x_4373_, 0);
                    v_isSharedCheck_4391_ = (!crate::leanh::lean_is_exclusive(v___x_4373_)) as u8;
                    if v_isSharedCheck_4391_ == 0 {
                        v___x_4386_ = v___x_4373_;
                        v_isShared_4387_ = v_isSharedCheck_4391_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4384_);
                        crate::leanh::lean_dec(v___x_4373_);
                        v___x_4386_ = crate::leanh::lean_box(0);
                        v_isShared_4387_ = v_isSharedCheck_4391_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4378_ = lean_st_ref_get(v___x_4372_);
                crate::leanh::lean_dec(v___x_4372_);
                v___x_4379_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4379_, 0, v_a_4374_);
                crate::leanh::lean_ctor_set(v___x_4379_, 1, v___x_4378_);
                if v_isShared_4377_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4376_, 0, v___x_4379_);
                    v___x_4381_ = v___x_4376_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4382_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4382_, 0, v___x_4379_);
                    v___x_4381_ = v_reuseFailAlloc_4382_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4381_;
            }
            3 => {
                if v_isShared_4387_ == 0 {
                    v___x_4389_ = v___x_4386_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4390_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4390_, 0, v_a_4384_);
                    v___x_4389_ = v_reuseFailAlloc_4390_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4389_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Action_terminalAction___lam__0___boxed(
    mut v_goal_4392_: *mut crate::leanh::LeanObject,
    mut v_check_4393_: *mut crate::leanh::LeanObject,
    mut v___y_4394_: *mut crate::leanh::LeanObject,
    mut v___y_4395_: *mut crate::leanh::LeanObject,
    mut v___y_4396_: *mut crate::leanh::LeanObject,
    mut v___y_4397_: *mut crate::leanh::LeanObject,
    mut v___y_4398_: *mut crate::leanh::LeanObject,
    mut v___y_4399_: *mut crate::leanh::LeanObject,
    mut v___y_4400_: *mut crate::leanh::LeanObject,
    mut v___y_4401_: *mut crate::leanh::LeanObject,
    mut v___y_4402_: *mut crate::leanh::LeanObject,
    mut v___y_4403_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4404_ = l_Lean_Meta_Grind_Action_terminalAction___lam__0(
        v_goal_4392_,
        v_check_4393_,
        v___y_4394_,
        v___y_4395_,
        v___y_4396_,
        v___y_4397_,
        v___y_4398_,
        v___y_4399_,
        v___y_4400_,
        v___y_4401_,
        v___y_4402_,
    );
    return v_res_4404_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_terminalAction(
    mut v_check_4405_: *mut crate::leanh::LeanObject,
    mut v_mkTac_4406_: *mut crate::leanh::LeanObject,
    mut v_goal_4407_: *mut crate::leanh::LeanObject,
    mut v_kna_4408_: *mut crate::leanh::LeanObject,
    mut v_kp_4409_: *mut crate::leanh::LeanObject,
    mut v_a_4410_: *mut crate::leanh::LeanObject,
    mut v_a_4411_: *mut crate::leanh::LeanObject,
    mut v_a_4412_: *mut crate::leanh::LeanObject,
    mut v_a_4413_: *mut crate::leanh::LeanObject,
    mut v_a_4414_: *mut crate::leanh::LeanObject,
    mut v_a_4415_: *mut crate::leanh::LeanObject,
    mut v_a_4416_: *mut crate::leanh::LeanObject,
    mut v_a_4417_: *mut crate::leanh::LeanObject,
    mut v_a_4418_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mvarId_4420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: u8 = 0;
    let mut v_snd_4426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toGoalState_4429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inconsistent_4430_: u8 = 0;
    let mut v___x_4431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4436_: u8 = 0;
    let mut v___x_4438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4440_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_mvarId_4420_ = crate::leanh::lean_ctor_get(v_goal_4407_, 1);
                crate::leanh::lean_inc(v_mvarId_4420_);
                v___f_4421_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Meta_Grind_Action_terminalAction___lam__0___boxed
                        as *mut core::ffi::c_void,
                    12,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_4421_, 0, v_goal_4407_);
                crate::leanh::lean_closure_set(v___f_4421_, 1, v_check_4405_);
                v___x_4422_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg(v_mvarId_4420_, v___f_4421_, v_a_4410_, v_a_4411_, v_a_4412_, v_a_4413_, v_a_4414_, v_a_4415_, v_a_4416_, v_a_4417_, v_a_4418_);
                if crate::leanh::lean_obj_tag(v___x_4422_) == 0 {
                    v_a_4423_ = crate::leanh::lean_ctor_get(v___x_4422_, 0);
                    crate::leanh::lean_inc(v_a_4423_);
                    crate::leanh::lean_dec_ref_known(v___x_4422_, 1);
                    v_fst_4424_ = crate::leanh::lean_ctor_get(v_a_4423_, 0);
                    v___x_4425_ = (crate::leanh::lean_unbox(v_fst_4424_) as u8);
                    if v___x_4425_ == 0 {
                        crate::leanh::lean_dec_ref(v_kp_4409_);
                        crate::leanh::lean_dec_ref(v_mkTac_4406_);
                        v_snd_4426_ = crate::leanh::lean_ctor_get(v_a_4423_, 1);
                        crate::leanh::lean_inc(v_snd_4426_);
                        crate::leanh::lean_dec(v_a_4423_);
                        crate::leanh::lean_inc(v_a_4418_);
                        crate::leanh::lean_inc_ref(v_a_4417_);
                        crate::leanh::lean_inc(v_a_4416_);
                        crate::leanh::lean_inc_ref(v_a_4415_);
                        crate::leanh::lean_inc(v_a_4414_);
                        crate::leanh::lean_inc_ref(v_a_4413_);
                        crate::leanh::lean_inc(v_a_4412_);
                        crate::leanh::lean_inc_ref(v_a_4411_);
                        crate::leanh::lean_inc(v_a_4410_);
                        v___x_4427_ = crate::leanh::lean_apply_11(
                            v_kna_4408_,
                            v_snd_4426_,
                            v_a_4410_,
                            v_a_4411_,
                            v_a_4412_,
                            v_a_4413_,
                            v_a_4414_,
                            v_a_4415_,
                            v_a_4416_,
                            v_a_4417_,
                            v_a_4418_,
                            crate::leanh::lean_box(0),
                        );
                        return v___x_4427_;
                    } else {
                        crate::leanh::lean_dec_ref(v_kna_4408_);
                        v_snd_4428_ = crate::leanh::lean_ctor_get(v_a_4423_, 1);
                        crate::leanh::lean_inc(v_snd_4428_);
                        crate::leanh::lean_dec(v_a_4423_);
                        v_toGoalState_4429_ = crate::leanh::lean_ctor_get(v_snd_4428_, 0);
                        v_inconsistent_4430_ = crate::leanh::lean_ctor_get_uint8(
                            v_toGoalState_4429_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17) as u32,
                        );
                        if v_inconsistent_4430_ == 0 {
                            crate::leanh::lean_dec_ref(v_mkTac_4406_);
                            crate::leanh::lean_inc(v_a_4418_);
                            crate::leanh::lean_inc_ref(v_a_4417_);
                            crate::leanh::lean_inc(v_a_4416_);
                            crate::leanh::lean_inc_ref(v_a_4415_);
                            crate::leanh::lean_inc(v_a_4414_);
                            crate::leanh::lean_inc_ref(v_a_4413_);
                            crate::leanh::lean_inc(v_a_4412_);
                            crate::leanh::lean_inc_ref(v_a_4411_);
                            crate::leanh::lean_inc(v_a_4410_);
                            v___x_4431_ = crate::leanh::lean_apply_11(
                                v_kp_4409_,
                                v_snd_4428_,
                                v_a_4410_,
                                v_a_4411_,
                                v_a_4412_,
                                v_a_4413_,
                                v_a_4414_,
                                v_a_4415_,
                                v_a_4416_,
                                v_a_4417_,
                                v_a_4418_,
                                crate::leanh::lean_box(0),
                            );
                            return v___x_4431_;
                        } else {
                            crate::leanh::lean_dec(v_snd_4428_);
                            crate::leanh::lean_dec_ref(v_kp_4409_);
                            v___x_4432_ = l_Lean_Meta_Grind_Action_closeWith(
                                v_mkTac_4406_,
                                v_a_4410_,
                                v_a_4411_,
                                v_a_4412_,
                                v_a_4413_,
                                v_a_4414_,
                                v_a_4415_,
                                v_a_4416_,
                                v_a_4417_,
                                v_a_4418_,
                            );
                            return v___x_4432_;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_kp_4409_);
                    crate::leanh::lean_dec_ref(v_kna_4408_);
                    crate::leanh::lean_dec_ref(v_mkTac_4406_);
                    v_a_4433_ = crate::leanh::lean_ctor_get(v___x_4422_, 0);
                    v_isSharedCheck_4440_ = (!crate::leanh::lean_is_exclusive(v___x_4422_)) as u8;
                    if v_isSharedCheck_4440_ == 0 {
                        v___x_4435_ = v___x_4422_;
                        v_isShared_4436_ = v_isSharedCheck_4440_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4433_);
                        crate::leanh::lean_dec(v___x_4422_);
                        v___x_4435_ = crate::leanh::lean_box(0);
                        v_isShared_4436_ = v_isSharedCheck_4440_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4436_ == 0 {
                    v___x_4438_ = v___x_4435_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4439_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4439_, 0, v_a_4433_);
                    v___x_4438_ = v_reuseFailAlloc_4439_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4438_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Action_terminalAction___boxed(
    mut v_check_4441_: *mut crate::leanh::LeanObject,
    mut v_mkTac_4442_: *mut crate::leanh::LeanObject,
    mut v_goal_4443_: *mut crate::leanh::LeanObject,
    mut v_kna_4444_: *mut crate::leanh::LeanObject,
    mut v_kp_4445_: *mut crate::leanh::LeanObject,
    mut v_a_4446_: *mut crate::leanh::LeanObject,
    mut v_a_4447_: *mut crate::leanh::LeanObject,
    mut v_a_4448_: *mut crate::leanh::LeanObject,
    mut v_a_4449_: *mut crate::leanh::LeanObject,
    mut v_a_4450_: *mut crate::leanh::LeanObject,
    mut v_a_4451_: *mut crate::leanh::LeanObject,
    mut v_a_4452_: *mut crate::leanh::LeanObject,
    mut v_a_4453_: *mut crate::leanh::LeanObject,
    mut v_a_4454_: *mut crate::leanh::LeanObject,
    mut v_a_4455_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4456_ = l_Lean_Meta_Grind_Action_terminalAction(
        v_check_4441_,
        v_mkTac_4442_,
        v_goal_4443_,
        v_kna_4444_,
        v_kp_4445_,
        v_a_4446_,
        v_a_4447_,
        v_a_4448_,
        v_a_4449_,
        v_a_4450_,
        v_a_4451_,
        v_a_4452_,
        v_a_4453_,
        v_a_4454_,
    );
    crate::leanh::lean_dec(v_a_4454_);
    crate::leanh::lean_dec_ref(v_a_4453_);
    crate::leanh::lean_dec(v_a_4452_);
    crate::leanh::lean_dec_ref(v_a_4451_);
    crate::leanh::lean_dec(v_a_4450_);
    crate::leanh::lean_dec_ref(v_a_4449_);
    crate::leanh::lean_dec(v_a_4448_);
    crate::leanh::lean_dec_ref(v_a_4447_);
    crate::leanh::lean_dec(v_a_4446_);
    return v_res_4456_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_saveStateIfTracing___redArg(
    mut v_a_4457_: *mut crate::leanh::LeanObject,
    mut v_a_4458_: *mut crate::leanh::LeanObject,
    mut v_a_4459_: *mut crate::leanh::LeanObject,
    mut v_a_4460_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4466_: u8 = 0;
    let mut v_trace_4467_: u8 = 0;
    let mut v___x_4468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4476_: u8 = 0;
    let mut v___x_4477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4481_: u8 = 0;
    let mut v_a_4482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4485_: u8 = 0;
    let mut v___x_4487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4489_: u8 = 0;
    let mut v_isSharedCheck_4490_: u8 = 0;
    let mut v_a_4491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4494_: u8 = 0;
    let mut v___x_4496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4498_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4462_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_4457_);
                if crate::leanh::lean_obj_tag(v___x_4462_) == 0 {
                    v_a_4463_ = crate::leanh::lean_ctor_get(v___x_4462_, 0);
                    v_isSharedCheck_4490_ = (!crate::leanh::lean_is_exclusive(v___x_4462_)) as u8;
                    if v_isSharedCheck_4490_ == 0 {
                        v___x_4465_ = v___x_4462_;
                        v_isShared_4466_ = v_isSharedCheck_4490_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4463_);
                        crate::leanh::lean_dec(v___x_4462_);
                        v___x_4465_ = crate::leanh::lean_box(0);
                        v_isShared_4466_ = v_isSharedCheck_4490_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4491_ = crate::leanh::lean_ctor_get(v___x_4462_, 0);
                    v_isSharedCheck_4498_ = (!crate::leanh::lean_is_exclusive(v___x_4462_)) as u8;
                    if v_isSharedCheck_4498_ == 0 {
                        v___x_4493_ = v___x_4462_;
                        v_isShared_4494_ = v_isSharedCheck_4498_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4491_);
                        crate::leanh::lean_dec(v___x_4462_);
                        v___x_4493_ = crate::leanh::lean_box(0);
                        v_isShared_4494_ = v_isSharedCheck_4498_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_trace_4467_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_4463_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13) as u32,
                );
                crate::leanh::lean_dec(v_a_4463_);
                if v_trace_4467_ == 0 {
                    v___x_4468_ = crate::leanh::lean_box(0);
                    if v_isShared_4466_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4465_, 0, v___x_4468_);
                        v___x_4470_ = v___x_4465_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4471_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4471_, 0, v___x_4468_);
                        v___x_4470_ = v_reuseFailAlloc_4471_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4465_);
                    v___x_4472_ =
                        l_Lean_Meta_Grind_saveState___redArg(v_a_4458_, v_a_4459_, v_a_4460_);
                    if crate::leanh::lean_obj_tag(v___x_4472_) == 0 {
                        v_a_4473_ = crate::leanh::lean_ctor_get(v___x_4472_, 0);
                        v_isSharedCheck_4481_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4472_)) as u8;
                        if v_isSharedCheck_4481_ == 0 {
                            v___x_4475_ = v___x_4472_;
                            v_isShared_4476_ = v_isSharedCheck_4481_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4473_);
                            crate::leanh::lean_dec(v___x_4472_);
                            v___x_4475_ = crate::leanh::lean_box(0);
                            v_isShared_4476_ = v_isSharedCheck_4481_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_4482_ = crate::leanh::lean_ctor_get(v___x_4472_, 0);
                        v_isSharedCheck_4489_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4472_)) as u8;
                        if v_isSharedCheck_4489_ == 0 {
                            v___x_4484_ = v___x_4472_;
                            v_isShared_4485_ = v_isSharedCheck_4489_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4482_);
                            crate::leanh::lean_dec(v___x_4472_);
                            v___x_4484_ = crate::leanh::lean_box(0);
                            v_isShared_4485_ = v_isSharedCheck_4489_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_4470_;
            }
            3 => {
                v___x_4477_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4477_, 0, v_a_4473_);
                if v_isShared_4476_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4475_, 0, v___x_4477_);
                    v___x_4479_ = v___x_4475_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4480_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4480_, 0, v___x_4477_);
                    v___x_4479_ = v_reuseFailAlloc_4480_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4479_;
            }
            5 => {
                if v_isShared_4485_ == 0 {
                    v___x_4487_ = v___x_4484_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4488_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4488_, 0, v_a_4482_);
                    v___x_4487_ = v_reuseFailAlloc_4488_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4487_;
            }
            7 => {
                if v_isShared_4494_ == 0 {
                    v___x_4496_ = v___x_4493_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4497_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4497_, 0, v_a_4491_);
                    v___x_4496_ = v_reuseFailAlloc_4497_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4496_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Action_saveStateIfTracing___redArg___boxed(
    mut v_a_4499_: *mut crate::leanh::LeanObject,
    mut v_a_4500_: *mut crate::leanh::LeanObject,
    mut v_a_4501_: *mut crate::leanh::LeanObject,
    mut v_a_4502_: *mut crate::leanh::LeanObject,
    mut v_a_4503_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4504_ = l_Lean_Meta_Grind_Action_saveStateIfTracing___redArg(
        v_a_4499_, v_a_4500_, v_a_4501_, v_a_4502_,
    );
    crate::leanh::lean_dec(v_a_4502_);
    crate::leanh::lean_dec(v_a_4501_);
    crate::leanh::lean_dec(v_a_4500_);
    crate::leanh::lean_dec_ref(v_a_4499_);
    return v_res_4504_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_saveStateIfTracing(
    mut v_a_4505_: *mut crate::leanh::LeanObject,
    mut v_a_4506_: *mut crate::leanh::LeanObject,
    mut v_a_4507_: *mut crate::leanh::LeanObject,
    mut v_a_4508_: *mut crate::leanh::LeanObject,
    mut v_a_4509_: *mut crate::leanh::LeanObject,
    mut v_a_4510_: *mut crate::leanh::LeanObject,
    mut v_a_4511_: *mut crate::leanh::LeanObject,
    mut v_a_4512_: *mut crate::leanh::LeanObject,
    mut v_a_4513_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4515_ = l_Lean_Meta_Grind_Action_saveStateIfTracing___redArg(
        v_a_4506_, v_a_4507_, v_a_4511_, v_a_4513_,
    );
    return v___x_4515_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_saveStateIfTracing___boxed(
    mut v_a_4516_: *mut crate::leanh::LeanObject,
    mut v_a_4517_: *mut crate::leanh::LeanObject,
    mut v_a_4518_: *mut crate::leanh::LeanObject,
    mut v_a_4519_: *mut crate::leanh::LeanObject,
    mut v_a_4520_: *mut crate::leanh::LeanObject,
    mut v_a_4521_: *mut crate::leanh::LeanObject,
    mut v_a_4522_: *mut crate::leanh::LeanObject,
    mut v_a_4523_: *mut crate::leanh::LeanObject,
    mut v_a_4524_: *mut crate::leanh::LeanObject,
    mut v_a_4525_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4526_ = l_Lean_Meta_Grind_Action_saveStateIfTracing(
        v_a_4516_, v_a_4517_, v_a_4518_, v_a_4519_, v_a_4520_, v_a_4521_, v_a_4522_, v_a_4523_,
        v_a_4524_,
    );
    crate::leanh::lean_dec(v_a_4524_);
    crate::leanh::lean_dec_ref(v_a_4523_);
    crate::leanh::lean_dec(v_a_4522_);
    crate::leanh::lean_dec_ref(v_a_4521_);
    crate::leanh::lean_dec(v_a_4520_);
    crate::leanh::lean_dec_ref(v_a_4519_);
    crate::leanh::lean_dec(v_a_4518_);
    crate::leanh::lean_dec_ref(v_a_4517_);
    crate::leanh::lean_dec(v_a_4516_);
    return v_res_4526_;
}
pub unsafe fn l_Lean_withoutModifyingState___at___00Lean_Meta_Grind_Action_checkSeqAt_spec__0___redArg(
    mut v_x_4527_: *mut crate::leanh::LeanObject,
    mut v___y_4528_: *mut crate::leanh::LeanObject,
    mut v___y_4529_: *mut crate::leanh::LeanObject,
    mut v___y_4530_: *mut crate::leanh::LeanObject,
    mut v___y_4531_: *mut crate::leanh::LeanObject,
    mut v___y_4532_: *mut crate::leanh::LeanObject,
    mut v___y_4533_: *mut crate::leanh::LeanObject,
    mut v___y_4534_: *mut crate::leanh::LeanObject,
    mut v___y_4535_: *mut crate::leanh::LeanObject,
    mut v___y_4536_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4545_: u8 = 0;
    let mut v___x_4547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4549_: u8 = 0;
    let mut v_unused_4550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4554_: u8 = 0;
    let mut v___x_4556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4558_: u8 = 0;
    let mut v_a_4559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4563_: u8 = 0;
    let mut v___x_4565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4567_: u8 = 0;
    let mut v_unused_4568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4572_: u8 = 0;
    let mut v___x_4574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4576_: u8 = 0;
    let mut v_a_4577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4580_: u8 = 0;
    let mut v___x_4582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4584_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4538_ =
                    l_Lean_Meta_Grind_saveState___redArg(v___y_4530_, v___y_4534_, v___y_4536_);
                if crate::leanh::lean_obj_tag(v___x_4538_) == 0 {
                    v_a_4539_ = crate::leanh::lean_ctor_get(v___x_4538_, 0);
                    crate::leanh::lean_inc(v_a_4539_);
                    crate::leanh::lean_dec_ref_known(v___x_4538_, 1);
                    crate::leanh::lean_inc(v___y_4536_);
                    crate::leanh::lean_inc_ref(v___y_4535_);
                    crate::leanh::lean_inc(v___y_4534_);
                    crate::leanh::lean_inc_ref(v___y_4533_);
                    crate::leanh::lean_inc(v___y_4532_);
                    crate::leanh::lean_inc_ref(v___y_4531_);
                    crate::leanh::lean_inc(v___y_4530_);
                    crate::leanh::lean_inc_ref(v___y_4529_);
                    crate::leanh::lean_inc(v___y_4528_);
                    v_r_4540_ = crate::leanh::lean_apply_10(
                        v_x_4527_,
                        v___y_4528_,
                        v___y_4529_,
                        v___y_4530_,
                        v___y_4531_,
                        v___y_4532_,
                        v___y_4533_,
                        v___y_4534_,
                        v___y_4535_,
                        v___y_4536_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v_r_4540_) == 0 {
                        v_a_4541_ = crate::leanh::lean_ctor_get(v_r_4540_, 0);
                        crate::leanh::lean_inc(v_a_4541_);
                        crate::leanh::lean_dec_ref_known(v_r_4540_, 1);
                        v___x_4542_ = l_Lean_Meta_Grind_SavedState_restore___redArg(
                            v_a_4539_,
                            v___y_4530_,
                            v___y_4534_,
                            v___y_4536_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4542_) == 0 {
                            v_isSharedCheck_4549_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4542_)) as u8;
                            if v_isSharedCheck_4549_ == 0 {
                                v_unused_4550_ = crate::leanh::lean_ctor_get(v___x_4542_, 0);
                                crate::leanh::lean_dec(v_unused_4550_);
                                v___x_4544_ = v___x_4542_;
                                v_isShared_4545_ = v_isSharedCheck_4549_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_4542_);
                                v___x_4544_ = crate::leanh::lean_box(0);
                                v_isShared_4545_ = v_isSharedCheck_4549_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_4541_);
                            v_a_4551_ = crate::leanh::lean_ctor_get(v___x_4542_, 0);
                            v_isSharedCheck_4558_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4542_)) as u8;
                            if v_isSharedCheck_4558_ == 0 {
                                v___x_4553_ = v___x_4542_;
                                v_isShared_4554_ = v_isSharedCheck_4558_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4551_);
                                crate::leanh::lean_dec(v___x_4542_);
                                v___x_4553_ = crate::leanh::lean_box(0);
                                v_isShared_4554_ = v_isSharedCheck_4558_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        v_a_4559_ = crate::leanh::lean_ctor_get(v_r_4540_, 0);
                        crate::leanh::lean_inc(v_a_4559_);
                        crate::leanh::lean_dec_ref_known(v_r_4540_, 1);
                        v___x_4560_ = l_Lean_Meta_Grind_SavedState_restore___redArg(
                            v_a_4539_,
                            v___y_4530_,
                            v___y_4534_,
                            v___y_4536_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4560_) == 0 {
                            v_isSharedCheck_4567_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4560_)) as u8;
                            if v_isSharedCheck_4567_ == 0 {
                                v_unused_4568_ = crate::leanh::lean_ctor_get(v___x_4560_, 0);
                                crate::leanh::lean_dec(v_unused_4568_);
                                v___x_4562_ = v___x_4560_;
                                v_isShared_4563_ = v_isSharedCheck_4567_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_4560_);
                                v___x_4562_ = crate::leanh::lean_box(0);
                                v_isShared_4563_ = v_isSharedCheck_4567_;
                                state = 5;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_4559_);
                            v_a_4569_ = crate::leanh::lean_ctor_get(v___x_4560_, 0);
                            v_isSharedCheck_4576_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4560_)) as u8;
                            if v_isSharedCheck_4576_ == 0 {
                                v___x_4571_ = v___x_4560_;
                                v_isShared_4572_ = v_isSharedCheck_4576_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4569_);
                                crate::leanh::lean_dec(v___x_4560_);
                                v___x_4571_ = crate::leanh::lean_box(0);
                                v_isShared_4572_ = v_isSharedCheck_4576_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_x_4527_);
                    v_a_4577_ = crate::leanh::lean_ctor_get(v___x_4538_, 0);
                    v_isSharedCheck_4584_ = (!crate::leanh::lean_is_exclusive(v___x_4538_)) as u8;
                    if v_isSharedCheck_4584_ == 0 {
                        v___x_4579_ = v___x_4538_;
                        v_isShared_4580_ = v_isSharedCheck_4584_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4577_);
                        crate::leanh::lean_dec(v___x_4538_);
                        v___x_4579_ = crate::leanh::lean_box(0);
                        v_isShared_4580_ = v_isSharedCheck_4584_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4545_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4544_, 0, v_a_4541_);
                    v___x_4547_ = v___x_4544_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4548_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4548_, 0, v_a_4541_);
                    v___x_4547_ = v_reuseFailAlloc_4548_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4547_;
            }
            3 => {
                if v_isShared_4554_ == 0 {
                    v___x_4556_ = v___x_4553_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4557_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4557_, 0, v_a_4551_);
                    v___x_4556_ = v_reuseFailAlloc_4557_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4556_;
            }
            5 => {
                if v_isShared_4563_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4562_, 1);
                    crate::leanh::lean_ctor_set(v___x_4562_, 0, v_a_4559_);
                    v___x_4565_ = v___x_4562_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4566_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4566_, 0, v_a_4559_);
                    v___x_4565_ = v_reuseFailAlloc_4566_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4565_;
            }
            7 => {
                if v_isShared_4572_ == 0 {
                    v___x_4574_ = v___x_4571_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4575_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4575_, 0, v_a_4569_);
                    v___x_4574_ = v_reuseFailAlloc_4575_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4574_;
            }
            9 => {
                if v_isShared_4580_ == 0 {
                    v___x_4582_ = v___x_4579_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4583_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4583_, 0, v_a_4577_);
                    v___x_4582_ = v_reuseFailAlloc_4583_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4582_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withoutModifyingState___at___00Lean_Meta_Grind_Action_checkSeqAt_spec__0___redArg___boxed(
    mut v_x_4585_: *mut crate::leanh::LeanObject,
    mut v___y_4586_: *mut crate::leanh::LeanObject,
    mut v___y_4587_: *mut crate::leanh::LeanObject,
    mut v___y_4588_: *mut crate::leanh::LeanObject,
    mut v___y_4589_: *mut crate::leanh::LeanObject,
    mut v___y_4590_: *mut crate::leanh::LeanObject,
    mut v___y_4591_: *mut crate::leanh::LeanObject,
    mut v___y_4592_: *mut crate::leanh::LeanObject,
    mut v___y_4593_: *mut crate::leanh::LeanObject,
    mut v___y_4594_: *mut crate::leanh::LeanObject,
    mut v___y_4595_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4596_ =
        l_Lean_withoutModifyingState___at___00Lean_Meta_Grind_Action_checkSeqAt_spec__0___redArg(
            v_x_4585_,
            v___y_4586_,
            v___y_4587_,
            v___y_4588_,
            v___y_4589_,
            v___y_4590_,
            v___y_4591_,
            v___y_4592_,
            v___y_4593_,
            v___y_4594_,
        );
    crate::leanh::lean_dec(v___y_4594_);
    crate::leanh::lean_dec_ref(v___y_4593_);
    crate::leanh::lean_dec(v___y_4592_);
    crate::leanh::lean_dec_ref(v___y_4591_);
    crate::leanh::lean_dec(v___y_4590_);
    crate::leanh::lean_dec_ref(v___y_4589_);
    crate::leanh::lean_dec(v___y_4588_);
    crate::leanh::lean_dec_ref(v___y_4587_);
    crate::leanh::lean_dec(v___y_4586_);
    return v_res_4596_;
}
pub unsafe fn l_Lean_withoutModifyingState___at___00Lean_Meta_Grind_Action_checkSeqAt_spec__0(
    mut v_00_u03b1_4597_: *mut crate::leanh::LeanObject,
    mut v_x_4598_: *mut crate::leanh::LeanObject,
    mut v___y_4599_: *mut crate::leanh::LeanObject,
    mut v___y_4600_: *mut crate::leanh::LeanObject,
    mut v___y_4601_: *mut crate::leanh::LeanObject,
    mut v___y_4602_: *mut crate::leanh::LeanObject,
    mut v___y_4603_: *mut crate::leanh::LeanObject,
    mut v___y_4604_: *mut crate::leanh::LeanObject,
    mut v___y_4605_: *mut crate::leanh::LeanObject,
    mut v___y_4606_: *mut crate::leanh::LeanObject,
    mut v___y_4607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4609_ =
        l_Lean_withoutModifyingState___at___00Lean_Meta_Grind_Action_checkSeqAt_spec__0___redArg(
            v_x_4598_,
            v___y_4599_,
            v___y_4600_,
            v___y_4601_,
            v___y_4602_,
            v___y_4603_,
            v___y_4604_,
            v___y_4605_,
            v___y_4606_,
            v___y_4607_,
        );
    return v___x_4609_;
}
pub unsafe fn l_Lean_withoutModifyingState___at___00Lean_Meta_Grind_Action_checkSeqAt_spec__0___boxed(
    mut v_00_u03b1_4610_: *mut crate::leanh::LeanObject,
    mut v_x_4611_: *mut crate::leanh::LeanObject,
    mut v___y_4612_: *mut crate::leanh::LeanObject,
    mut v___y_4613_: *mut crate::leanh::LeanObject,
    mut v___y_4614_: *mut crate::leanh::LeanObject,
    mut v___y_4615_: *mut crate::leanh::LeanObject,
    mut v___y_4616_: *mut crate::leanh::LeanObject,
    mut v___y_4617_: *mut crate::leanh::LeanObject,
    mut v___y_4618_: *mut crate::leanh::LeanObject,
    mut v___y_4619_: *mut crate::leanh::LeanObject,
    mut v___y_4620_: *mut crate::leanh::LeanObject,
    mut v___y_4621_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4622_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Grind_Action_checkSeqAt_spec__0(
        v_00_u03b1_4610_,
        v_x_4611_,
        v___y_4612_,
        v___y_4613_,
        v___y_4614_,
        v___y_4615_,
        v___y_4616_,
        v___y_4617_,
        v___y_4618_,
        v___y_4619_,
        v___y_4620_,
    );
    crate::leanh::lean_dec(v___y_4620_);
    crate::leanh::lean_dec_ref(v___y_4619_);
    crate::leanh::lean_dec(v___y_4618_);
    crate::leanh::lean_dec_ref(v___y_4617_);
    crate::leanh::lean_dec(v___y_4616_);
    crate::leanh::lean_dec_ref(v___y_4615_);
    crate::leanh::lean_dec(v___y_4614_);
    crate::leanh::lean_dec_ref(v___y_4613_);
    crate::leanh::lean_dec(v___y_4612_);
    return v_res_4622_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_checkSeqAt___lam__0(
    mut v_val_4623_: *mut crate::leanh::LeanObject,
    mut v_seq_4624_: *mut crate::leanh::LeanObject,
    mut v_goal_4625_: *mut crate::leanh::LeanObject,
    mut v___y_4626_: *mut crate::leanh::LeanObject,
    mut v___y_4627_: *mut crate::leanh::LeanObject,
    mut v___y_4628_: *mut crate::leanh::LeanObject,
    mut v___y_4629_: *mut crate::leanh::LeanObject,
    mut v___y_4630_: *mut crate::leanh::LeanObject,
    mut v___y_4631_: *mut crate::leanh::LeanObject,
    mut v___y_4632_: *mut crate::leanh::LeanObject,
    mut v___y_4633_: *mut crate::leanh::LeanObject,
    mut v___y_4634_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_4638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_simp_4640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_simpMethods_4641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_anchorRefs_x3f_4642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cheapCases_4643_: u8 = 0;
    let mut v_reportMVarIssue_4644_: u8 = 0;
    let mut v_splitSource_4645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ematchDiagSource_4646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_symPrios_4647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_4648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_4649_: u8 = 0;
    let mut v_ematchDiag_4650_: u8 = 0;
    let mut v_markInstances_4651_: u8 = 0;
    let mut v_lax_4652_: u8 = 0;
    let mut v_suggestions_4653_: u8 = 0;
    let mut v_locals_4654_: u8 = 0;
    let mut v_splits_4655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ematch_4656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_gen_4657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_genLocal_4658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_instances_4659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_matchEqs_4660_: u8 = 0;
    let mut v_splitMatch_4661_: u8 = 0;
    let mut v_splitIte_4662_: u8 = 0;
    let mut v_splitIndPred_4663_: u8 = 0;
    let mut v_splitImp_4664_: u8 = 0;
    let mut v_canonHeartbeats_4665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ext_4666_: u8 = 0;
    let mut v_extAll_4667_: u8 = 0;
    let mut v_etaStruct_4668_: u8 = 0;
    let mut v_funext_4669_: u8 = 0;
    let mut v_lookahead_4670_: u8 = 0;
    let mut v_verbose_4671_: u8 = 0;
    let mut v_clean_4672_: u8 = 0;
    let mut v_qlia_4673_: u8 = 0;
    let mut v_mbtc_4674_: u8 = 0;
    let mut v_zetaDelta_4675_: u8 = 0;
    let mut v_zeta_4676_: u8 = 0;
    let mut v_ring_4677_: u8 = 0;
    let mut v_ringSteps_4678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringMaxDegree_4679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_linarith_4680_: u8 = 0;
    let mut v_lia_4681_: u8 = 0;
    let mut v_ac_4682_: u8 = 0;
    let mut v_acSteps_4683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exp_4684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_abstractProof_4685_: u8 = 0;
    let mut v_inj_4686_: u8 = 0;
    let mut v_order_4687_: u8 = 0;
    let mut v_min_4688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_detailed_4689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_useSorry_4690_: u8 = 0;
    let mut v_revert_4691_: u8 = 0;
    let mut v_funCC_4692_: u8 = 0;
    let mut v_reducible_4693_: u8 = 0;
    let mut v_maxSuggestions_4694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4695_: u8 = 0;
    let mut v___x_4696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4702_: u8 = 0;
    let mut v___x_4703_: u8 = 0;
    let mut v___x_4704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4708_: u8 = 0;
    let mut v_a_4709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4712_: u8 = 0;
    let mut v___y_4714_: u8 = 0;
    let mut v___x_4715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4722_: u8 = 0;
    let mut v___x_4723_: u8 = 0;
    let mut v_isSharedCheck_4724_: u8 = 0;
    let mut v_a_4725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4728_: u8 = 0;
    let mut v___x_4730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4732_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4636_ = l_Lean_Meta_Grind_SavedState_restore___redArg(
                    v_val_4623_,
                    v___y_4628_,
                    v___y_4632_,
                    v___y_4634_,
                );
                if crate::leanh::lean_obj_tag(v___x_4636_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_4636_, 1);
                    v___x_4637_ = l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg(v_seq_4624_, v___y_4633_);
                    v_config_4638_ = crate::leanh::lean_ctor_get(v___y_4627_, 2);
                    v_a_4639_ = crate::leanh::lean_ctor_get(v___x_4637_, 0);
                    crate::leanh::lean_inc(v_a_4639_);
                    crate::leanh::lean_dec_ref(v___x_4637_);
                    v_simp_4640_ = crate::leanh::lean_ctor_get(v___y_4627_, 0);
                    v_simpMethods_4641_ = crate::leanh::lean_ctor_get(v___y_4627_, 1);
                    v_anchorRefs_x3f_4642_ = crate::leanh::lean_ctor_get(v___y_4627_, 3);
                    v_cheapCases_4643_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_4627_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                    );
                    v_reportMVarIssue_4644_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_4627_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 1) as u32,
                    );
                    v_splitSource_4645_ = crate::leanh::lean_ctor_get(v___y_4627_, 4);
                    v_ematchDiagSource_4646_ = crate::leanh::lean_ctor_get(v___y_4627_, 5);
                    v_symPrios_4647_ = crate::leanh::lean_ctor_get(v___y_4627_, 6);
                    v_extensions_4648_ = crate::leanh::lean_ctor_get(v___y_4627_, 7);
                    v_debug_4649_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_4627_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 2) as u32,
                    );
                    v_ematchDiag_4650_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_4627_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 3) as u32,
                    );
                    v_markInstances_4651_ = crate::leanh::lean_ctor_get_uint8(
                        v_config_4638_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 1) as u32,
                    );
                    v_lax_4652_ = crate::leanh::lean_ctor_get_uint8(
                        v_config_4638_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 2) as u32,
                    );
                    v_suggestions_4653_ = crate::leanh::lean_ctor_get_uint8(
                        v_config_4638_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 3) as u32,
                    );
                    v_locals_4654_ = crate::leanh::lean_ctor_get_uint8(
                        v_config_4638_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 4) as u32,
                    );
                    v_splits_4655_ = crate::leanh::lean_ctor_get(v_config_4638_, 0);
                    v_ematch_4656_ = crate::leanh::lean_ctor_get(v_config_4638_, 1);
                    v_gen_4657_ = crate::leanh::lean_ctor_get(v_config_4638_, 2);
                    v_genLocal_4658_ = crate::leanh::lean_ctor_get(v_config_4638_, 3);
                    v_instances_4659_ = crate::leanh::lean_ctor_get(v_config_4638_, 4);
                    v_matchEqs_4660_ = crate::leanh::lean_ctor_get_uint8(
                        v_config_4638_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 5) as u32,
                    );
                    v_splitMatch_4661_ = crate::leanh::lean_ctor_get_uint8(
                        v_config_4638_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 6) as u32,
                    );
                    v_splitIte_4662_ = crate::leanh::lean_ctor_get_uint8(
                        v_config_4638_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 7) as u32,
                    );
                    v_splitIndPred_4663_ = crate::leanh::lean_ctor_get_uint8(
                        v_config_4638_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 8) as u32,
                    );
                    v_splitImp_4664_ = crate::leanh::lean_ctor_get_uint8(
                        v_config_4638_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 9) as u32,
                    );
                    v_canonHeartbeats_4665_ = crate::leanh::lean_ctor_get(v_config_4638_, 5);
                    v_ext_4666_ = crate::leanh::lean_ctor_get_uint8(
                        v_config_4638_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 10) as u32,
                    );
                    v_extAll_4667_ = crate::leanh::lean_ctor_get_uint8(
                        v_config_4638_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 11) as u32,
                    );
                    v_etaStruct_4668_ = crate::leanh::lean_ctor_get_uint8(
                        v_config_4638_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 12) as u32,
                    );
                    v_funext_4669_ = crate::leanh::lean_ctor_get_uint8(
                        v_config_4638_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 13) as u32,
                    );
                    v_lookahead_4670_ = crate::leanh::lean_ctor_get_uint8(
                        v_config_4638_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 14) as u32,
                    );
                    v_verbose_4671_ = crate::leanh::lean_ctor_get_uint8(
                        v_config_4638_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 15) as u32,
                    );
                    v_clean_4672_ = crate::leanh::lean_ctor_get_uint8(
                        v_config_4638_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 16) as u32,
                    );
                    v_qlia_4673_ = crate::leanh::lean_ctor_get_uint8(
                        v_config_4638_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 17) as u32,
                    );
                    v_mbtc_4674_ = crate::leanh::lean_ctor_get_uint8(
                        v_config_4638_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 18) as u32,
                    );
                    v_zetaDelta_4675_ = crate::leanh::lean_ctor_get_uint8(
                        v_config_4638_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 19) as u32,
                    );
                    v_zeta_4676_ = crate::leanh::lean_ctor_get_uint8(
                        v_config_4638_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 20) as u32,
                    );
                    v_ring_4677_ = crate::leanh::lean_ctor_get_uint8(
                        v_config_4638_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 21) as u32,
                    );
                    v_ringSteps_4678_ = crate::leanh::lean_ctor_get(v_config_4638_, 6);
                    v_ringMaxDegree_4679_ = crate::leanh::lean_ctor_get(v_config_4638_, 7);
                    v_linarith_4680_ = crate::leanh::lean_ctor_get_uint8(
                        v_config_4638_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 22) as u32,
                    );
                    v_lia_4681_ = crate::leanh::lean_ctor_get_uint8(
                        v_config_4638_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 23) as u32,
                    );
                    v_ac_4682_ = crate::leanh::lean_ctor_get_uint8(
                        v_config_4638_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 24) as u32,
                    );
                    v_acSteps_4683_ = crate::leanh::lean_ctor_get(v_config_4638_, 8);
                    v_exp_4684_ = crate::leanh::lean_ctor_get(v_config_4638_, 9);
                    v_abstractProof_4685_ = crate::leanh::lean_ctor_get_uint8(
                        v_config_4638_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 25) as u32,
                    );
                    v_inj_4686_ = crate::leanh::lean_ctor_get_uint8(
                        v_config_4638_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 26) as u32,
                    );
                    v_order_4687_ = crate::leanh::lean_ctor_get_uint8(
                        v_config_4638_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 27) as u32,
                    );
                    v_min_4688_ = crate::leanh::lean_ctor_get(v_config_4638_, 10);
                    v_detailed_4689_ = crate::leanh::lean_ctor_get(v_config_4638_, 11);
                    v_useSorry_4690_ = crate::leanh::lean_ctor_get_uint8(
                        v_config_4638_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 28) as u32,
                    );
                    v_revert_4691_ = crate::leanh::lean_ctor_get_uint8(
                        v_config_4638_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 29) as u32,
                    );
                    v_funCC_4692_ = crate::leanh::lean_ctor_get_uint8(
                        v_config_4638_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 30) as u32,
                    );
                    v_reducible_4693_ = crate::leanh::lean_ctor_get_uint8(
                        v_config_4638_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 31) as u32,
                    );
                    v_maxSuggestions_4694_ = crate::leanh::lean_ctor_get(v_config_4638_, 12);
                    v___x_4695_ = 0;
                    crate::leanh::lean_inc(v_maxSuggestions_4694_);
                    crate::leanh::lean_inc(v_detailed_4689_);
                    crate::leanh::lean_inc(v_min_4688_);
                    crate::leanh::lean_inc(v_exp_4684_);
                    crate::leanh::lean_inc(v_acSteps_4683_);
                    crate::leanh::lean_inc(v_ringMaxDegree_4679_);
                    crate::leanh::lean_inc(v_ringSteps_4678_);
                    crate::leanh::lean_inc(v_canonHeartbeats_4665_);
                    crate::leanh::lean_inc(v_instances_4659_);
                    crate::leanh::lean_inc(v_genLocal_4658_);
                    crate::leanh::lean_inc(v_gen_4657_);
                    crate::leanh::lean_inc(v_ematch_4656_);
                    crate::leanh::lean_inc(v_splits_4655_);
                    v___x_4696_ = crate::leanh::lean_alloc_ctor(0, 13, (32) as u32);
                    crate::leanh::lean_ctor_set(v___x_4696_, 0, v_splits_4655_);
                    crate::leanh::lean_ctor_set(v___x_4696_, 1, v_ematch_4656_);
                    crate::leanh::lean_ctor_set(v___x_4696_, 2, v_gen_4657_);
                    crate::leanh::lean_ctor_set(v___x_4696_, 3, v_genLocal_4658_);
                    crate::leanh::lean_ctor_set(v___x_4696_, 4, v_instances_4659_);
                    crate::leanh::lean_ctor_set(v___x_4696_, 5, v_canonHeartbeats_4665_);
                    crate::leanh::lean_ctor_set(v___x_4696_, 6, v_ringSteps_4678_);
                    crate::leanh::lean_ctor_set(v___x_4696_, 7, v_ringMaxDegree_4679_);
                    crate::leanh::lean_ctor_set(v___x_4696_, 8, v_acSteps_4683_);
                    crate::leanh::lean_ctor_set(v___x_4696_, 9, v_exp_4684_);
                    crate::leanh::lean_ctor_set(v___x_4696_, 10, v_min_4688_);
                    crate::leanh::lean_ctor_set(v___x_4696_, 11, v_detailed_4689_);
                    crate::leanh::lean_ctor_set(v___x_4696_, 12, v_maxSuggestions_4694_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13) as u32,
                        v___x_4695_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 1) as u32,
                        v_markInstances_4651_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 2) as u32,
                        v_lax_4652_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 3) as u32,
                        v_suggestions_4653_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 4) as u32,
                        v_locals_4654_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 5) as u32,
                        v_matchEqs_4660_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 6) as u32,
                        v_splitMatch_4661_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 7) as u32,
                        v_splitIte_4662_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 8) as u32,
                        v_splitIndPred_4663_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 9) as u32,
                        v_splitImp_4664_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 10) as u32,
                        v_ext_4666_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 11) as u32,
                        v_extAll_4667_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 12) as u32,
                        v_etaStruct_4668_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 13) as u32,
                        v_funext_4669_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 14) as u32,
                        v_lookahead_4670_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 15) as u32,
                        v_verbose_4671_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 16) as u32,
                        v_clean_4672_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 17) as u32,
                        v_qlia_4673_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 18) as u32,
                        v_mbtc_4674_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 19) as u32,
                        v_zetaDelta_4675_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 20) as u32,
                        v_zeta_4676_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 21) as u32,
                        v_ring_4677_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 22) as u32,
                        v_linarith_4680_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 23) as u32,
                        v_lia_4681_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 24) as u32,
                        v_ac_4682_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 25) as u32,
                        v_abstractProof_4685_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 26) as u32,
                        v_inj_4686_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 27) as u32,
                        v_order_4687_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 28) as u32,
                        v_useSorry_4690_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 29) as u32,
                        v_revert_4691_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 30) as u32,
                        v_funCC_4692_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 31) as u32,
                        v_reducible_4693_,
                    );
                    crate::leanh::lean_inc_ref(v_extensions_4648_);
                    crate::leanh::lean_inc_ref(v_symPrios_4647_);
                    crate::leanh::lean_inc(v_ematchDiagSource_4646_);
                    crate::leanh::lean_inc(v_splitSource_4645_);
                    crate::leanh::lean_inc(v_anchorRefs_x3f_4642_);
                    crate::leanh::lean_inc_ref(v_simpMethods_4641_);
                    crate::leanh::lean_inc_ref(v_simp_4640_);
                    v___x_4697_ = crate::leanh::lean_alloc_ctor(0, 8, (4) as u32);
                    crate::leanh::lean_ctor_set(v___x_4697_, 0, v_simp_4640_);
                    crate::leanh::lean_ctor_set(v___x_4697_, 1, v_simpMethods_4641_);
                    crate::leanh::lean_ctor_set(v___x_4697_, 2, v___x_4696_);
                    crate::leanh::lean_ctor_set(v___x_4697_, 3, v_anchorRefs_x3f_4642_);
                    crate::leanh::lean_ctor_set(v___x_4697_, 4, v_splitSource_4645_);
                    crate::leanh::lean_ctor_set(v___x_4697_, 5, v_ematchDiagSource_4646_);
                    crate::leanh::lean_ctor_set(v___x_4697_, 6, v_symPrios_4647_);
                    crate::leanh::lean_ctor_set(v___x_4697_, 7, v_extensions_4648_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_4697_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                        v_cheapCases_4643_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_4697_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 1) as u32,
                        v_reportMVarIssue_4644_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_4697_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 2) as u32,
                        v_debug_4649_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_4697_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 3) as u32,
                        v_ematchDiag_4650_,
                    );
                    v___x_4698_ = l_Lean_Meta_Grind_evalTactic(
                        v_goal_4625_,
                        v_a_4639_,
                        v___y_4626_,
                        v___x_4697_,
                        v___y_4628_,
                        v___y_4629_,
                        v___y_4630_,
                        v___y_4631_,
                        v___y_4632_,
                        v___y_4633_,
                        v___y_4634_,
                    );
                    crate::leanh::lean_dec_ref_known(v___x_4697_, 8);
                    if crate::leanh::lean_obj_tag(v___x_4698_) == 0 {
                        v_a_4699_ = crate::leanh::lean_ctor_get(v___x_4698_, 0);
                        v_isSharedCheck_4708_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4698_)) as u8;
                        if v_isSharedCheck_4708_ == 0 {
                            v___x_4701_ = v___x_4698_;
                            v_isShared_4702_ = v_isSharedCheck_4708_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4699_);
                            crate::leanh::lean_dec(v___x_4698_);
                            v___x_4701_ = crate::leanh::lean_box(0);
                            v_isShared_4702_ = v_isSharedCheck_4708_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4709_ = crate::leanh::lean_ctor_get(v___x_4698_, 0);
                        v_isSharedCheck_4724_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4698_)) as u8;
                        if v_isSharedCheck_4724_ == 0 {
                            v___x_4711_ = v___x_4698_;
                            v_isShared_4712_ = v_isSharedCheck_4724_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4709_);
                            crate::leanh::lean_dec(v___x_4698_);
                            v___x_4711_ = crate::leanh::lean_box(0);
                            v_isShared_4712_ = v_isSharedCheck_4724_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_goal_4625_);
                    crate::leanh::lean_dec(v_seq_4624_);
                    v_a_4725_ = crate::leanh::lean_ctor_get(v___x_4636_, 0);
                    v_isSharedCheck_4732_ = (!crate::leanh::lean_is_exclusive(v___x_4636_)) as u8;
                    if v_isSharedCheck_4732_ == 0 {
                        v___x_4727_ = v___x_4636_;
                        v_isShared_4728_ = v_isSharedCheck_4732_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4725_);
                        crate::leanh::lean_dec(v___x_4636_);
                        v___x_4727_ = crate::leanh::lean_box(0);
                        v_isShared_4728_ = v_isSharedCheck_4732_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4703_ = l_List_isEmpty___redArg(v_a_4699_);
                crate::leanh::lean_dec(v_a_4699_);
                v___x_4704_ = crate::leanh::lean_box((v___x_4703_) as usize);
                if v_isShared_4702_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4701_, 0, v___x_4704_);
                    v___x_4706_ = v___x_4701_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4707_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4707_, 0, v___x_4704_);
                    v___x_4706_ = v_reuseFailAlloc_4707_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4706_;
            }
            3 => {
                v___x_4722_ = l_Lean_Exception_isInterrupt(v_a_4709_);
                if v___x_4722_ == 0 {
                    crate::leanh::lean_inc(v_a_4709_);
                    v___x_4723_ = l_Lean_Exception_isRuntime(v_a_4709_);
                    v___y_4714_ = v___x_4723_;
                    state = 4;
                    continue;
                } else {
                    v___y_4714_ = v___x_4722_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v___y_4714_ == 0 {
                    crate::leanh::lean_dec(v_a_4709_);
                    v___x_4715_ = crate::leanh::lean_box((v___y_4714_) as usize);
                    if v_isShared_4712_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_4711_, 0);
                        crate::leanh::lean_ctor_set(v___x_4711_, 0, v___x_4715_);
                        v___x_4717_ = v___x_4711_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4718_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4718_, 0, v___x_4715_);
                        v___x_4717_ = v_reuseFailAlloc_4718_;
                        state = 5;
                        continue;
                    }
                } else {
                    if v_isShared_4712_ == 0 {
                        v___x_4720_ = v___x_4711_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_4721_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4721_, 0, v_a_4709_);
                        v___x_4720_ = v_reuseFailAlloc_4721_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_4717_;
            }
            6 => {
                return v___x_4720_;
            }
            7 => {
                if v_isShared_4728_ == 0 {
                    v___x_4730_ = v___x_4727_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4731_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4731_, 0, v_a_4725_);
                    v___x_4730_ = v_reuseFailAlloc_4731_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4730_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Action_checkSeqAt___lam__0___boxed(
    mut v_val_4733_: *mut crate::leanh::LeanObject,
    mut v_seq_4734_: *mut crate::leanh::LeanObject,
    mut v_goal_4735_: *mut crate::leanh::LeanObject,
    mut v___y_4736_: *mut crate::leanh::LeanObject,
    mut v___y_4737_: *mut crate::leanh::LeanObject,
    mut v___y_4738_: *mut crate::leanh::LeanObject,
    mut v___y_4739_: *mut crate::leanh::LeanObject,
    mut v___y_4740_: *mut crate::leanh::LeanObject,
    mut v___y_4741_: *mut crate::leanh::LeanObject,
    mut v___y_4742_: *mut crate::leanh::LeanObject,
    mut v___y_4743_: *mut crate::leanh::LeanObject,
    mut v___y_4744_: *mut crate::leanh::LeanObject,
    mut v___y_4745_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4746_ = l_Lean_Meta_Grind_Action_checkSeqAt___lam__0(
        v_val_4733_,
        v_seq_4734_,
        v_goal_4735_,
        v___y_4736_,
        v___y_4737_,
        v___y_4738_,
        v___y_4739_,
        v___y_4740_,
        v___y_4741_,
        v___y_4742_,
        v___y_4743_,
        v___y_4744_,
    );
    crate::leanh::lean_dec(v___y_4744_);
    crate::leanh::lean_dec_ref(v___y_4743_);
    crate::leanh::lean_dec(v___y_4742_);
    crate::leanh::lean_dec_ref(v___y_4741_);
    crate::leanh::lean_dec(v___y_4740_);
    crate::leanh::lean_dec_ref(v___y_4739_);
    crate::leanh::lean_dec(v___y_4738_);
    crate::leanh::lean_dec_ref(v___y_4737_);
    crate::leanh::lean_dec(v___y_4736_);
    return v_res_4746_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_checkSeqAt(
    mut v_s_x3f_4747_: *mut crate::leanh::LeanObject,
    mut v_goal_4748_: *mut crate::leanh::LeanObject,
    mut v_seq_4749_: *mut crate::leanh::LeanObject,
    mut v_a_4750_: *mut crate::leanh::LeanObject,
    mut v_a_4751_: *mut crate::leanh::LeanObject,
    mut v_a_4752_: *mut crate::leanh::LeanObject,
    mut v_a_4753_: *mut crate::leanh::LeanObject,
    mut v_a_4754_: *mut crate::leanh::LeanObject,
    mut v_a_4755_: *mut crate::leanh::LeanObject,
    mut v_a_4756_: *mut crate::leanh::LeanObject,
    mut v_a_4757_: *mut crate::leanh::LeanObject,
    mut v_a_4758_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_s_x3f_4747_) == 1 {
        let mut v_val_4760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_4760_ = crate::leanh::lean_ctor_get(v_s_x3f_4747_, 0);
        crate::leanh::lean_inc(v_val_4760_);
        crate::leanh::lean_dec_ref_known(v_s_x3f_4747_, 1);
        v___f_4761_ = crate::leanh::lean_alloc_closure(
            l_Lean_Meta_Grind_Action_checkSeqAt___lam__0___boxed as *mut core::ffi::c_void,
            13,
            3,
        );
        crate::leanh::lean_closure_set(v___f_4761_, 0, v_val_4760_);
        crate::leanh::lean_closure_set(v___f_4761_, 1, v_seq_4749_);
        crate::leanh::lean_closure_set(v___f_4761_, 2, v_goal_4748_);
        v___x_4762_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Grind_Action_checkSeqAt_spec__0___redArg(v___f_4761_, v_a_4750_, v_a_4751_, v_a_4752_, v_a_4753_, v_a_4754_, v_a_4755_, v_a_4756_, v_a_4757_, v_a_4758_);
        return v___x_4762_;
    } else {
        let mut v___x_4763_: u8 = 0;
        let mut v___x_4764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_seq_4749_);
        crate::leanh::lean_dec_ref(v_goal_4748_);
        crate::leanh::lean_dec(v_s_x3f_4747_);
        v___x_4763_ = 1;
        v___x_4764_ = crate::leanh::lean_box((v___x_4763_) as usize);
        v___x_4765_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4765_, 0, v___x_4764_);
        return v___x_4765_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Action_checkSeqAt___boxed(
    mut v_s_x3f_4766_: *mut crate::leanh::LeanObject,
    mut v_goal_4767_: *mut crate::leanh::LeanObject,
    mut v_seq_4768_: *mut crate::leanh::LeanObject,
    mut v_a_4769_: *mut crate::leanh::LeanObject,
    mut v_a_4770_: *mut crate::leanh::LeanObject,
    mut v_a_4771_: *mut crate::leanh::LeanObject,
    mut v_a_4772_: *mut crate::leanh::LeanObject,
    mut v_a_4773_: *mut crate::leanh::LeanObject,
    mut v_a_4774_: *mut crate::leanh::LeanObject,
    mut v_a_4775_: *mut crate::leanh::LeanObject,
    mut v_a_4776_: *mut crate::leanh::LeanObject,
    mut v_a_4777_: *mut crate::leanh::LeanObject,
    mut v_a_4778_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4779_ = l_Lean_Meta_Grind_Action_checkSeqAt(
        v_s_x3f_4766_,
        v_goal_4767_,
        v_seq_4768_,
        v_a_4769_,
        v_a_4770_,
        v_a_4771_,
        v_a_4772_,
        v_a_4773_,
        v_a_4774_,
        v_a_4775_,
        v_a_4776_,
        v_a_4777_,
    );
    crate::leanh::lean_dec(v_a_4777_);
    crate::leanh::lean_dec_ref(v_a_4776_);
    crate::leanh::lean_dec(v_a_4775_);
    crate::leanh::lean_dec_ref(v_a_4774_);
    crate::leanh::lean_dec(v_a_4773_);
    crate::leanh::lean_dec_ref(v_a_4772_);
    crate::leanh::lean_dec(v_a_4771_);
    crate::leanh::lean_dec_ref(v_a_4770_);
    crate::leanh::lean_dec(v_a_4769_);
    return v_res_4779_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0_spec__0(
    mut v_msgData_4780_: *mut crate::leanh::LeanObject,
    mut v___y_4781_: *mut crate::leanh::LeanObject,
    mut v___y_4782_: *mut crate::leanh::LeanObject,
    mut v___y_4783_: *mut crate::leanh::LeanObject,
    mut v___y_4784_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_4790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4786_ = lean_st_ref_get(v___y_4784_);
    v_env_4787_ = crate::leanh::lean_ctor_get(v___x_4786_, 0);
    crate::leanh::lean_inc_ref(v_env_4787_);
    crate::leanh::lean_dec(v___x_4786_);
    v___x_4788_ = lean_st_ref_get(v___y_4782_);
    v_mctx_4789_ = crate::leanh::lean_ctor_get(v___x_4788_, 0);
    crate::leanh::lean_inc_ref(v_mctx_4789_);
    crate::leanh::lean_dec(v___x_4788_);
    v_lctx_4790_ = crate::leanh::lean_ctor_get(v___y_4781_, 2);
    v_options_4791_ = crate::leanh::lean_ctor_get(v___y_4783_, 2);
    crate::leanh::lean_inc_ref(v_options_4791_);
    crate::leanh::lean_inc_ref(v_lctx_4790_);
    v___x_4792_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4792_, 0, v_env_4787_);
    crate::leanh::lean_ctor_set(v___x_4792_, 1, v_mctx_4789_);
    crate::leanh::lean_ctor_set(v___x_4792_, 2, v_lctx_4790_);
    crate::leanh::lean_ctor_set(v___x_4792_, 3, v_options_4791_);
    v___x_4793_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4793_, 0, v___x_4792_);
    crate::leanh::lean_ctor_set(v___x_4793_, 1, v_msgData_4780_);
    v___x_4794_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4794_, 0, v___x_4793_);
    return v___x_4794_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0_spec__0___boxed(
    mut v_msgData_4795_: *mut crate::leanh::LeanObject,
    mut v___y_4796_: *mut crate::leanh::LeanObject,
    mut v___y_4797_: *mut crate::leanh::LeanObject,
    mut v___y_4798_: *mut crate::leanh::LeanObject,
    mut v___y_4799_: *mut crate::leanh::LeanObject,
    mut v___y_4800_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4801_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0_spec__0(v_msgData_4795_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_);
    crate::leanh::lean_dec(v___y_4799_);
    crate::leanh::lean_dec_ref(v___y_4798_);
    crate::leanh::lean_dec(v___y_4797_);
    crate::leanh::lean_dec_ref(v___y_4796_);
    return v_res_4801_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0___redArg(
    mut v_msg_4802_: *mut crate::leanh::LeanObject,
    mut v___y_4803_: *mut crate::leanh::LeanObject,
    mut v___y_4804_: *mut crate::leanh::LeanObject,
    mut v___y_4805_: *mut crate::leanh::LeanObject,
    mut v___y_4806_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_4808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4813_: u8 = 0;
    let mut v___x_4814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4818_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4808_ = crate::leanh::lean_ctor_get(v___y_4805_, 5);
                v___x_4809_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0_spec__0(v_msg_4802_, v___y_4803_, v___y_4804_, v___y_4805_, v___y_4806_);
                v_a_4810_ = crate::leanh::lean_ctor_get(v___x_4809_, 0);
                v_isSharedCheck_4818_ = (!crate::leanh::lean_is_exclusive(v___x_4809_)) as u8;
                if v_isSharedCheck_4818_ == 0 {
                    v___x_4812_ = v___x_4809_;
                    v_isShared_4813_ = v_isSharedCheck_4818_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_4810_);
                    crate::leanh::lean_dec(v___x_4809_);
                    v___x_4812_ = crate::leanh::lean_box(0);
                    v_isShared_4813_ = v_isSharedCheck_4818_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_4808_);
                v___x_4814_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4814_, 0, v_ref_4808_);
                crate::leanh::lean_ctor_set(v___x_4814_, 1, v_a_4810_);
                if v_isShared_4813_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4812_, 1);
                    crate::leanh::lean_ctor_set(v___x_4812_, 0, v___x_4814_);
                    v___x_4816_ = v___x_4812_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4817_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4817_, 0, v___x_4814_);
                    v___x_4816_ = v_reuseFailAlloc_4817_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4816_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0___redArg___boxed(
    mut v_msg_4819_: *mut crate::leanh::LeanObject,
    mut v___y_4820_: *mut crate::leanh::LeanObject,
    mut v___y_4821_: *mut crate::leanh::LeanObject,
    mut v___y_4822_: *mut crate::leanh::LeanObject,
    mut v___y_4823_: *mut crate::leanh::LeanObject,
    mut v___y_4824_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4825_ = l_Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0___redArg(
        v_msg_4819_,
        v___y_4820_,
        v___y_4821_,
        v___y_4822_,
        v___y_4823_,
    );
    crate::leanh::lean_dec(v___y_4823_);
    crate::leanh::lean_dec_ref(v___y_4822_);
    crate::leanh::lean_dec(v___y_4821_);
    crate::leanh::lean_dec_ref(v___y_4820_);
    return v_res_4825_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3_spec__4(
    mut v_opts_4826_: *mut crate::leanh::LeanObject,
    mut v_opt_4827_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_4828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_4829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_4830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_4828_ = crate::leanh::lean_ctor_get(v_opt_4827_, 0);
    v_defValue_4829_ = crate::leanh::lean_ctor_get(v_opt_4827_, 1);
    v_map_4830_ = crate::leanh::lean_ctor_get(v_opts_4826_, 0);
    v___x_4831_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_4830_,
            v_name_4828_,
        );
    if crate::leanh::lean_obj_tag(v___x_4831_) == 0 {
        let mut v___x_4832_: u8 = 0;
        v___x_4832_ = (crate::leanh::lean_unbox(v_defValue_4829_) as u8);
        return v___x_4832_;
    } else {
        let mut v_val_4833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_4833_ = crate::leanh::lean_ctor_get(v___x_4831_, 0);
        crate::leanh::lean_inc(v_val_4833_);
        crate::leanh::lean_dec_ref_known(v___x_4831_, 1);
        if crate::leanh::lean_obj_tag(v_val_4833_) == 1 {
            let mut v_v_4834_: u8 = 0;
            v_v_4834_ = crate::leanh::lean_ctor_get_uint8(v_val_4833_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_4833_, 0);
            return v_v_4834_;
        } else {
            let mut v___x_4835_: u8 = 0;
            crate::leanh::lean_dec(v_val_4833_);
            v___x_4835_ = (crate::leanh::lean_unbox(v_defValue_4829_) as u8);
            return v___x_4835_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3_spec__4___boxed(
    mut v_opts_4836_: *mut crate::leanh::LeanObject,
    mut v_opt_4837_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4838_: u8 = 0;
    let mut v_r_4839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4838_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3_spec__4(v_opts_4836_, v_opt_4837_);
    crate::leanh::lean_dec_ref(v_opt_4837_);
    crate::leanh::lean_dec_ref(v_opts_4836_);
    v_r_4839_ = crate::leanh::lean_box((v_res_4838_) as usize);
    return v_r_4839_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0(
    mut v___y_4847_: u8,
    mut v_suppressElabErrors_4848_: u8,
    mut v_x_4849_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_4849_) == 1 {
        let mut v_pre_4850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_pre_4850_ = crate::leanh::lean_ctor_get(v_x_4849_, 0);
        match crate::leanh::lean_obj_tag(v_pre_4850_) {
            1 => {
                let mut v_pre_4851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_pre_4851_ = crate::leanh::lean_ctor_get(v_pre_4850_, 0);
                match crate::leanh::lean_obj_tag(v_pre_4851_) {
                    0 => {
                        let mut v_str_4852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v_str_4853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_4854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_4855_: u8 = 0;
                        v_str_4852_ = crate::leanh::lean_ctor_get(v_x_4849_, 1);
                        v_str_4853_ = crate::leanh::lean_ctor_get(v_pre_4850_, 1);
                        v___x_4854_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__0;
                        v___x_4855_ = lean_string_dec_eq(v_str_4853_, v___x_4854_);
                        if v___x_4855_ == 0 {
                            let mut v___x_4856_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4857_: u8 = 0;
                            v___x_4856_ = l_Lean_Meta_Grind_Action_run___lam__0___closed__2;
                            v___x_4857_ = lean_string_dec_eq(v_str_4853_, v___x_4856_);
                            if v___x_4857_ == 0 {
                                return v___y_4847_;
                            } else {
                                let mut v___x_4858_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_4859_: u8 = 0;
                                v___x_4858_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__1;
                                v___x_4859_ = lean_string_dec_eq(v_str_4852_, v___x_4858_);
                                if v___x_4859_ == 0 {
                                    return v___y_4847_;
                                } else {
                                    return v_suppressElabErrors_4848_;
                                }
                            }
                        } else {
                            let mut v___x_4860_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4861_: u8 = 0;
                            v___x_4860_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__2;
                            v___x_4861_ = lean_string_dec_eq(v_str_4852_, v___x_4860_);
                            if v___x_4861_ == 0 {
                                return v___y_4847_;
                            } else {
                                return v_suppressElabErrors_4848_;
                            }
                        }
                    }
                    1 => {
                        let mut v_pre_4862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v_pre_4862_ = crate::leanh::lean_ctor_get(v_pre_4851_, 0);
                        if crate::leanh::lean_obj_tag(v_pre_4862_) == 0 {
                            let mut v_str_4863_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_4864_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_4865_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4866_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4867_: u8 = 0;
                            v_str_4863_ = crate::leanh::lean_ctor_get(v_x_4849_, 1);
                            v_str_4864_ = crate::leanh::lean_ctor_get(v_pre_4850_, 1);
                            v_str_4865_ = crate::leanh::lean_ctor_get(v_pre_4851_, 1);
                            v___x_4866_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__3;
                            v___x_4867_ = lean_string_dec_eq(v_str_4865_, v___x_4866_);
                            if v___x_4867_ == 0 {
                                return v___y_4847_;
                            } else {
                                let mut v___x_4868_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_4869_: u8 = 0;
                                v___x_4868_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__4;
                                v___x_4869_ = lean_string_dec_eq(v_str_4864_, v___x_4868_);
                                if v___x_4869_ == 0 {
                                    return v___y_4847_;
                                } else {
                                    let mut v___x_4870_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_4871_: u8 = 0;
                                    v___x_4870_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__5;
                                    v___x_4871_ = lean_string_dec_eq(v_str_4863_, v___x_4870_);
                                    if v___x_4871_ == 0 {
                                        return v___y_4847_;
                                    } else {
                                        return v_suppressElabErrors_4848_;
                                    }
                                }
                            }
                        } else {
                            return v___y_4847_;
                        }
                    }
                    _ => {
                        return v___y_4847_;
                    }
                }
            }
            0 => {
                let mut v_str_4872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4874_: u8 = 0;
                v_str_4872_ = crate::leanh::lean_ctor_get(v_x_4849_, 1);
                v___x_4873_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__6;
                v___x_4874_ = lean_string_dec_eq(v_str_4872_, v___x_4873_);
                if v___x_4874_ == 0 {
                    return v___y_4847_;
                } else {
                    return v_suppressElabErrors_4848_;
                }
            }
            _ => {
                return v___y_4847_;
            }
        }
    } else {
        return v___y_4847_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___boxed(
    mut v___y_4875_: *mut crate::leanh::LeanObject,
    mut v_suppressElabErrors_4876_: *mut crate::leanh::LeanObject,
    mut v_x_4877_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_29452__boxed_4878_: u8 = 0;
    let mut v_suppressElabErrors_boxed_4879_: u8 = 0;
    let mut v_res_4880_: u8 = 0;
    let mut v_r_4881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_29452__boxed_4878_ = (crate::leanh::lean_unbox(v___y_4875_) as u8);
    v_suppressElabErrors_boxed_4879_ = (crate::leanh::lean_unbox(v_suppressElabErrors_4876_) as u8);
    v_res_4880_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0(v___y_29452__boxed_4878_, v_suppressElabErrors_boxed_4879_, v_x_4877_);
    crate::leanh::lean_dec(v_x_4877_);
    v_r_4881_ = crate::leanh::lean_box((v_res_4880_) as usize);
    return v_r_4881_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg(
    mut v_ref_4883_: *mut crate::leanh::LeanObject,
    mut v_msgData_4884_: *mut crate::leanh::LeanObject,
    mut v_severity_4885_: u8,
    mut v_isSilent_4886_: u8,
    mut v___y_4887_: *mut crate::leanh::LeanObject,
    mut v___y_4888_: *mut crate::leanh::LeanObject,
    mut v___y_4889_: *mut crate::leanh::LeanObject,
    mut v___y_4890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4893_: u8 = 0;
    let mut v___y_4894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4899_: u8 = 0;
    let mut v___y_4900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4916_: u8 = 0;
    let mut v___x_4917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4927_: u8 = 0;
    let mut v___y_4929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4930_: u8 = 0;
    let mut v___y_4931_: u8 = 0;
    let mut v___y_4932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4934_: u8 = 0;
    let mut v___y_4935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4942_: u8 = 0;
    let mut v___x_4943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4947_: u8 = 0;
    let mut v___x_4948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4952_: u8 = 0;
    let mut v___y_4954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4955_: u8 = 0;
    let mut v___y_4956_: u8 = 0;
    let mut v___y_4957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4960_: u8 = 0;
    let mut v___y_4961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4966_: u8 = 0;
    let mut v___y_4967_: u8 = 0;
    let mut v___y_4968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4971_: u8 = 0;
    let mut v_ref_4972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4976_: u8 = 0;
    let mut v___y_4978_: u8 = 0;
    let mut v___y_4979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4983_: u8 = 0;
    let mut v___y_4984_: u8 = 0;
    let mut v___y_4986_: u8 = 0;
    let mut v_fileName_4987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4991_: u8 = 0;
    let mut v___x_4992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4995_: u8 = 0;
    let mut v___x_4996_: u8 = 0;
    let mut v___x_4997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4998_: u8 = 0;
    let mut v___x_4999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5001_: u8 = 0;
    let mut v___x_5002_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4976_ = 2;
                v___x_5001_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4885_, v___x_4976_);
                if v___x_5001_ == 0 {
                    v___y_4986_ = v___x_5001_;
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_msgData_4884_);
                    v___x_5002_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_4884_);
                    v___y_4986_ = v___x_5002_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_4902_ = lean_st_ref_take(v___y_4901_);
                v_currNamespace_4903_ = crate::leanh::lean_ctor_get(v___y_4900_, 6);
                v_openDecls_4904_ = crate::leanh::lean_ctor_get(v___y_4900_, 7);
                v_env_4905_ = crate::leanh::lean_ctor_get(v___x_4902_, 0);
                v_nextMacroScope_4906_ = crate::leanh::lean_ctor_get(v___x_4902_, 1);
                v_ngen_4907_ = crate::leanh::lean_ctor_get(v___x_4902_, 2);
                v_auxDeclNGen_4908_ = crate::leanh::lean_ctor_get(v___x_4902_, 3);
                v_traceState_4909_ = crate::leanh::lean_ctor_get(v___x_4902_, 4);
                v_cache_4910_ = crate::leanh::lean_ctor_get(v___x_4902_, 5);
                v_messages_4911_ = crate::leanh::lean_ctor_get(v___x_4902_, 6);
                v_infoState_4912_ = crate::leanh::lean_ctor_get(v___x_4902_, 7);
                v_snapshotTasks_4913_ = crate::leanh::lean_ctor_get(v___x_4902_, 8);
                v_isSharedCheck_4927_ = (!crate::leanh::lean_is_exclusive(v___x_4902_)) as u8;
                if v_isSharedCheck_4927_ == 0 {
                    v___x_4915_ = v___x_4902_;
                    v_isShared_4916_ = v_isSharedCheck_4927_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_4913_);
                    crate::leanh::lean_inc(v_infoState_4912_);
                    crate::leanh::lean_inc(v_messages_4911_);
                    crate::leanh::lean_inc(v_cache_4910_);
                    crate::leanh::lean_inc(v_traceState_4909_);
                    crate::leanh::lean_inc(v_auxDeclNGen_4908_);
                    crate::leanh::lean_inc(v_ngen_4907_);
                    crate::leanh::lean_inc(v_nextMacroScope_4906_);
                    crate::leanh::lean_inc(v_env_4905_);
                    crate::leanh::lean_dec(v___x_4902_);
                    v___x_4915_ = crate::leanh::lean_box(0);
                    v_isShared_4916_ = v_isSharedCheck_4927_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_openDecls_4904_);
                crate::leanh::lean_inc(v_currNamespace_4903_);
                v___x_4917_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4917_, 0, v_currNamespace_4903_);
                crate::leanh::lean_ctor_set(v___x_4917_, 1, v_openDecls_4904_);
                v___x_4918_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4918_, 0, v___x_4917_);
                crate::leanh::lean_ctor_set(v___x_4918_, 1, v___y_4897_);
                crate::leanh::lean_inc_ref(v___y_4895_);
                crate::leanh::lean_inc_ref(v___y_4898_);
                v___x_4919_ = crate::leanh::lean_alloc_ctor(0, 5, (3) as u32);
                crate::leanh::lean_ctor_set(v___x_4919_, 0, v___y_4898_);
                crate::leanh::lean_ctor_set(v___x_4919_, 1, v___y_4896_);
                crate::leanh::lean_ctor_set(v___x_4919_, 2, v___y_4894_);
                crate::leanh::lean_ctor_set(v___x_4919_, 3, v___y_4895_);
                crate::leanh::lean_ctor_set(v___x_4919_, 4, v___x_4918_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4919_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v___y_4893_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4919_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_4899_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4919_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_4886_,
                );
                v___x_4920_ = l_Lean_MessageLog_add(v___x_4919_, v_messages_4911_);
                if v_isShared_4916_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4915_, 6, v___x_4920_);
                    v___x_4922_ = v___x_4915_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4926_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4926_, 0, v_env_4905_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4926_, 1, v_nextMacroScope_4906_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4926_, 2, v_ngen_4907_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4926_, 3, v_auxDeclNGen_4908_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4926_, 4, v_traceState_4909_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4926_, 5, v_cache_4910_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4926_, 6, v___x_4920_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4926_, 7, v_infoState_4912_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4926_, 8, v_snapshotTasks_4913_);
                    v___x_4922_ = v_reuseFailAlloc_4926_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4923_ = lean_st_ref_set(v___y_4901_, v___x_4922_);
                v___x_4924_ = crate::leanh::lean_box(0);
                v___x_4925_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4925_, 0, v___x_4924_);
                return v___x_4925_;
            }
            4 => {
                v___x_4937_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_4884_,
                    );
                v___x_4938_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0_spec__0(v___x_4937_, v___y_4887_, v___y_4888_, v___y_4889_, v___y_4890_);
                v_a_4939_ = crate::leanh::lean_ctor_get(v___x_4938_, 0);
                v_isSharedCheck_4952_ = (!crate::leanh::lean_is_exclusive(v___x_4938_)) as u8;
                if v_isSharedCheck_4952_ == 0 {
                    v___x_4941_ = v___x_4938_;
                    v_isShared_4942_ = v_isSharedCheck_4952_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_4939_);
                    crate::leanh::lean_dec(v___x_4938_);
                    v___x_4941_ = crate::leanh::lean_box(0);
                    v_isShared_4942_ = v_isSharedCheck_4952_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc_ref_n(v___y_4932_, 2);
                v___x_4943_ = l_Lean_FileMap_toPosition(v___y_4932_, v___y_4935_);
                crate::leanh::lean_dec(v___y_4935_);
                v___x_4944_ = l_Lean_FileMap_toPosition(v___y_4932_, v___y_4936_);
                crate::leanh::lean_dec(v___y_4936_);
                v___x_4945_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4945_, 0, v___x_4944_);
                v___x_4946_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___closed__0;
                if v___y_4931_ == 0 {
                    crate::leanh::lean_del_object(v___x_4941_);
                    crate::leanh::lean_dec_ref(v___y_4929_);
                    v___y_4893_ = v___y_4930_;
                    v___y_4894_ = v___x_4945_;
                    v___y_4895_ = v___x_4946_;
                    v___y_4896_ = v___x_4943_;
                    v___y_4897_ = v_a_4939_;
                    v___y_4898_ = v___y_4933_;
                    v___y_4899_ = v___y_4934_;
                    v___y_4900_ = v___y_4889_;
                    v___y_4901_ = v___y_4890_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_4939_);
                    v___x_4947_ = l_Lean_MessageData_hasTag(v___y_4929_, v_a_4939_);
                    if v___x_4947_ == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_4945_, 1);
                        crate::leanh::lean_dec_ref(v___x_4943_);
                        crate::leanh::lean_dec(v_a_4939_);
                        v___x_4948_ = crate::leanh::lean_box(0);
                        if v_isShared_4942_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4941_, 0, v___x_4948_);
                            v___x_4950_ = v___x_4941_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_4951_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4951_, 0, v___x_4948_);
                            v___x_4950_ = v_reuseFailAlloc_4951_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_4941_);
                        v___y_4893_ = v___y_4930_;
                        v___y_4894_ = v___x_4945_;
                        v___y_4895_ = v___x_4946_;
                        v___y_4896_ = v___x_4943_;
                        v___y_4897_ = v_a_4939_;
                        v___y_4898_ = v___y_4933_;
                        v___y_4899_ = v___y_4934_;
                        v___y_4900_ = v___y_4889_;
                        v___y_4901_ = v___y_4890_;
                        state = 1;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_4950_;
            }
            7 => {
                v___x_4962_ = l_Lean_Syntax_getTailPos_x3f(v___y_4958_, v___y_4955_);
                crate::leanh::lean_dec(v___y_4958_);
                if crate::leanh::lean_obj_tag(v___x_4962_) == 0 {
                    crate::leanh::lean_inc(v___y_4961_);
                    v___y_4929_ = v___y_4954_;
                    v___y_4930_ = v___y_4955_;
                    v___y_4931_ = v___y_4956_;
                    v___y_4932_ = v___y_4957_;
                    v___y_4933_ = v___y_4959_;
                    v___y_4934_ = v___y_4960_;
                    v___y_4935_ = v___y_4961_;
                    v___y_4936_ = v___y_4961_;
                    state = 4;
                    continue;
                } else {
                    v_val_4963_ = crate::leanh::lean_ctor_get(v___x_4962_, 0);
                    crate::leanh::lean_inc(v_val_4963_);
                    crate::leanh::lean_dec_ref_known(v___x_4962_, 1);
                    v___y_4929_ = v___y_4954_;
                    v___y_4930_ = v___y_4955_;
                    v___y_4931_ = v___y_4956_;
                    v___y_4932_ = v___y_4957_;
                    v___y_4933_ = v___y_4959_;
                    v___y_4934_ = v___y_4960_;
                    v___y_4935_ = v___y_4961_;
                    v___y_4936_ = v_val_4963_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                v_ref_4972_ = l_Lean_replaceRef(v_ref_4883_, v___y_4970_);
                v___x_4973_ = l_Lean_Syntax_getPos_x3f(v_ref_4972_, v___y_4966_);
                if crate::leanh::lean_obj_tag(v___x_4973_) == 0 {
                    v___x_4974_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_4954_ = v___y_4965_;
                    v___y_4955_ = v___y_4966_;
                    v___y_4956_ = v___y_4967_;
                    v___y_4957_ = v___y_4968_;
                    v___y_4958_ = v_ref_4972_;
                    v___y_4959_ = v___y_4969_;
                    v___y_4960_ = v___y_4971_;
                    v___y_4961_ = v___x_4974_;
                    state = 7;
                    continue;
                } else {
                    v_val_4975_ = crate::leanh::lean_ctor_get(v___x_4973_, 0);
                    crate::leanh::lean_inc(v_val_4975_);
                    crate::leanh::lean_dec_ref_known(v___x_4973_, 1);
                    v___y_4954_ = v___y_4965_;
                    v___y_4955_ = v___y_4966_;
                    v___y_4956_ = v___y_4967_;
                    v___y_4957_ = v___y_4968_;
                    v___y_4958_ = v_ref_4972_;
                    v___y_4959_ = v___y_4969_;
                    v___y_4960_ = v___y_4971_;
                    v___y_4961_ = v_val_4975_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if v___y_4984_ == 0 {
                    v___y_4965_ = v___y_4981_;
                    v___y_4966_ = v___y_4983_;
                    v___y_4967_ = v___y_4978_;
                    v___y_4968_ = v___y_4979_;
                    v___y_4969_ = v___y_4980_;
                    v___y_4970_ = v___y_4982_;
                    v___y_4971_ = v_severity_4885_;
                    state = 8;
                    continue;
                } else {
                    v___y_4965_ = v___y_4981_;
                    v___y_4966_ = v___y_4983_;
                    v___y_4967_ = v___y_4978_;
                    v___y_4968_ = v___y_4979_;
                    v___y_4969_ = v___y_4980_;
                    v___y_4970_ = v___y_4982_;
                    v___y_4971_ = v___x_4976_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                if v___y_4986_ == 0 {
                    v_fileName_4987_ = crate::leanh::lean_ctor_get(v___y_4889_, 0);
                    v_fileMap_4988_ = crate::leanh::lean_ctor_get(v___y_4889_, 1);
                    v_options_4989_ = crate::leanh::lean_ctor_get(v___y_4889_, 2);
                    v_ref_4990_ = crate::leanh::lean_ctor_get(v___y_4889_, 5);
                    v_suppressElabErrors_4991_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_4889_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_4992_ = crate::leanh::lean_box((v___y_4986_) as usize);
                    v___x_4993_ = crate::leanh::lean_box((v_suppressElabErrors_4991_) as usize);
                    v___f_4994_ = crate::leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    crate::leanh::lean_closure_set(v___f_4994_, 0, v___x_4992_);
                    crate::leanh::lean_closure_set(v___f_4994_, 1, v___x_4993_);
                    v___x_4995_ = 1;
                    v___x_4996_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4885_, v___x_4995_);
                    if v___x_4996_ == 0 {
                        v___y_4978_ = v_suppressElabErrors_4991_;
                        v___y_4979_ = v_fileMap_4988_;
                        v___y_4980_ = v_fileName_4987_;
                        v___y_4981_ = v___f_4994_;
                        v___y_4982_ = v_ref_4990_;
                        v___y_4983_ = v___y_4986_;
                        v___y_4984_ = v___x_4996_;
                        state = 9;
                        continue;
                    } else {
                        v___x_4997_ = l_Lean_warningAsError;
                        v___x_4998_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3_spec__4(v_options_4989_, v___x_4997_);
                        v___y_4978_ = v_suppressElabErrors_4991_;
                        v___y_4979_ = v_fileMap_4988_;
                        v___y_4980_ = v_fileName_4987_;
                        v___y_4981_ = v___f_4994_;
                        v___y_4982_ = v_ref_4990_;
                        v___y_4983_ = v___y_4986_;
                        v___y_4984_ = v___x_4998_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msgData_4884_);
                    v___x_4999_ = crate::leanh::lean_box(0);
                    v___x_5000_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5000_, 0, v___x_4999_);
                    return v___x_5000_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___boxed(
    mut v_ref_5003_: *mut crate::leanh::LeanObject,
    mut v_msgData_5004_: *mut crate::leanh::LeanObject,
    mut v_severity_5005_: *mut crate::leanh::LeanObject,
    mut v_isSilent_5006_: *mut crate::leanh::LeanObject,
    mut v___y_5007_: *mut crate::leanh::LeanObject,
    mut v___y_5008_: *mut crate::leanh::LeanObject,
    mut v___y_5009_: *mut crate::leanh::LeanObject,
    mut v___y_5010_: *mut crate::leanh::LeanObject,
    mut v___y_5011_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_5012_: u8 = 0;
    let mut v_isSilent_boxed_5013_: u8 = 0;
    let mut v_res_5014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_5012_ = (crate::leanh::lean_unbox(v_severity_5005_) as u8);
    v_isSilent_boxed_5013_ = (crate::leanh::lean_unbox(v_isSilent_5006_) as u8);
    v_res_5014_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg(v_ref_5003_, v_msgData_5004_, v_severity_boxed_5012_, v_isSilent_boxed_5013_, v___y_5007_, v___y_5008_, v___y_5009_, v___y_5010_);
    crate::leanh::lean_dec(v___y_5010_);
    crate::leanh::lean_dec_ref(v___y_5009_);
    crate::leanh::lean_dec(v___y_5008_);
    crate::leanh::lean_dec_ref(v___y_5007_);
    crate::leanh::lean_dec(v_ref_5003_);
    return v_res_5014_;
}
pub unsafe fn l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2(
    mut v_msgData_5015_: *mut crate::leanh::LeanObject,
    mut v_severity_5016_: u8,
    mut v_isSilent_5017_: u8,
    mut v___y_5018_: *mut crate::leanh::LeanObject,
    mut v___y_5019_: *mut crate::leanh::LeanObject,
    mut v___y_5020_: *mut crate::leanh::LeanObject,
    mut v___y_5021_: *mut crate::leanh::LeanObject,
    mut v___y_5022_: *mut crate::leanh::LeanObject,
    mut v___y_5023_: *mut crate::leanh::LeanObject,
    mut v___y_5024_: *mut crate::leanh::LeanObject,
    mut v___y_5025_: *mut crate::leanh::LeanObject,
    mut v___y_5026_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_5028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_5028_ = crate::leanh::lean_ctor_get(v___y_5025_, 5);
    v___x_5029_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg(v_ref_5028_, v_msgData_5015_, v_severity_5016_, v_isSilent_5017_, v___y_5023_, v___y_5024_, v___y_5025_, v___y_5026_);
    return v___x_5029_;
}
pub unsafe fn l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2___boxed(
    mut v_msgData_5030_: *mut crate::leanh::LeanObject,
    mut v_severity_5031_: *mut crate::leanh::LeanObject,
    mut v_isSilent_5032_: *mut crate::leanh::LeanObject,
    mut v___y_5033_: *mut crate::leanh::LeanObject,
    mut v___y_5034_: *mut crate::leanh::LeanObject,
    mut v___y_5035_: *mut crate::leanh::LeanObject,
    mut v___y_5036_: *mut crate::leanh::LeanObject,
    mut v___y_5037_: *mut crate::leanh::LeanObject,
    mut v___y_5038_: *mut crate::leanh::LeanObject,
    mut v___y_5039_: *mut crate::leanh::LeanObject,
    mut v___y_5040_: *mut crate::leanh::LeanObject,
    mut v___y_5041_: *mut crate::leanh::LeanObject,
    mut v___y_5042_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_5043_: u8 = 0;
    let mut v_isSilent_boxed_5044_: u8 = 0;
    let mut v_res_5045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_5043_ = (crate::leanh::lean_unbox(v_severity_5031_) as u8);
    v_isSilent_boxed_5044_ = (crate::leanh::lean_unbox(v_isSilent_5032_) as u8);
    v_res_5045_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2(v_msgData_5030_, v_severity_boxed_5043_, v_isSilent_boxed_5044_, v___y_5033_, v___y_5034_, v___y_5035_, v___y_5036_, v___y_5037_, v___y_5038_, v___y_5039_, v___y_5040_, v___y_5041_);
    crate::leanh::lean_dec(v___y_5041_);
    crate::leanh::lean_dec_ref(v___y_5040_);
    crate::leanh::lean_dec(v___y_5039_);
    crate::leanh::lean_dec_ref(v___y_5038_);
    crate::leanh::lean_dec(v___y_5037_);
    crate::leanh::lean_dec_ref(v___y_5036_);
    crate::leanh::lean_dec(v___y_5035_);
    crate::leanh::lean_dec_ref(v___y_5034_);
    crate::leanh::lean_dec(v___y_5033_);
    return v_res_5045_;
}
pub unsafe fn l_Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1(
    mut v_msgData_5046_: *mut crate::leanh::LeanObject,
    mut v___y_5047_: *mut crate::leanh::LeanObject,
    mut v___y_5048_: *mut crate::leanh::LeanObject,
    mut v___y_5049_: *mut crate::leanh::LeanObject,
    mut v___y_5050_: *mut crate::leanh::LeanObject,
    mut v___y_5051_: *mut crate::leanh::LeanObject,
    mut v___y_5052_: *mut crate::leanh::LeanObject,
    mut v___y_5053_: *mut crate::leanh::LeanObject,
    mut v___y_5054_: *mut crate::leanh::LeanObject,
    mut v___y_5055_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5057_: u8 = 0;
    let mut v___x_5058_: u8 = 0;
    let mut v___x_5059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5057_ = 1;
    v___x_5058_ = 0;
    v___x_5059_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2(v_msgData_5046_, v___x_5057_, v___x_5058_, v___y_5047_, v___y_5048_, v___y_5049_, v___y_5050_, v___y_5051_, v___y_5052_, v___y_5053_, v___y_5054_, v___y_5055_);
    return v___x_5059_;
}
pub unsafe fn l_Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1___boxed(
    mut v_msgData_5060_: *mut crate::leanh::LeanObject,
    mut v___y_5061_: *mut crate::leanh::LeanObject,
    mut v___y_5062_: *mut crate::leanh::LeanObject,
    mut v___y_5063_: *mut crate::leanh::LeanObject,
    mut v___y_5064_: *mut crate::leanh::LeanObject,
    mut v___y_5065_: *mut crate::leanh::LeanObject,
    mut v___y_5066_: *mut crate::leanh::LeanObject,
    mut v___y_5067_: *mut crate::leanh::LeanObject,
    mut v___y_5068_: *mut crate::leanh::LeanObject,
    mut v___y_5069_: *mut crate::leanh::LeanObject,
    mut v___y_5070_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5071_ = l_Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1(
        v_msgData_5060_,
        v___y_5061_,
        v___y_5062_,
        v___y_5063_,
        v___y_5064_,
        v___y_5065_,
        v___y_5066_,
        v___y_5067_,
        v___y_5068_,
        v___y_5069_,
    );
    crate::leanh::lean_dec(v___y_5069_);
    crate::leanh::lean_dec_ref(v___y_5068_);
    crate::leanh::lean_dec(v___y_5067_);
    crate::leanh::lean_dec_ref(v___y_5066_);
    crate::leanh::lean_dec(v___y_5065_);
    crate::leanh::lean_dec_ref(v___y_5064_);
    crate::leanh::lean_dec(v___y_5063_);
    crate::leanh::lean_dec_ref(v___y_5062_);
    crate::leanh::lean_dec(v___y_5061_);
    return v_res_5071_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5073_ = l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__0;
    v___x_5074_ = l_Lean_stringToMessageData(v___x_5073_);
    return v___x_5074_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5076_ = l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__2;
    v___x_5077_ = l_Lean_stringToMessageData(v___x_5076_);
    return v___x_5077_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_checkTactic___redArg(
    mut v_warnOnly_5078_: u8,
    mut v_goal_5079_: *mut crate::leanh::LeanObject,
    mut v_kp_5080_: *mut crate::leanh::LeanObject,
    mut v_a_5081_: *mut crate::leanh::LeanObject,
    mut v_a_5082_: *mut crate::leanh::LeanObject,
    mut v_a_5083_: *mut crate::leanh::LeanObject,
    mut v_a_5084_: *mut crate::leanh::LeanObject,
    mut v_a_5085_: *mut crate::leanh::LeanObject,
    mut v_a_5086_: *mut crate::leanh::LeanObject,
    mut v_a_5087_: *mut crate::leanh::LeanObject,
    mut v_a_5088_: *mut crate::leanh::LeanObject,
    mut v_a_5089_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_seq_5095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5100_: u8 = 0;
    let mut v___x_5101_: u8 = 0;
    let mut v___x_5102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5106_: u8 = 0;
    let mut v_mvarId_5107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5110_: u8 = 0;
    let mut v___x_5111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5125_: u8 = 0;
    let mut v___x_5127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5129_: u8 = 0;
    let mut v___x_5130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5133_: u8 = 0;
    let mut v___x_5135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5137_: u8 = 0;
    let mut v_unused_5138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5142_: u8 = 0;
    let mut v___x_5144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5146_: u8 = 0;
    let mut v_reuseFailAlloc_5147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5149_: u8 = 0;
    let mut v_unused_5150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5151_: u8 = 0;
    let mut v___x_5153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5155_: u8 = 0;
    let mut v_a_5156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5159_: u8 = 0;
    let mut v___x_5161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5163_: u8 = 0;
    let mut v_a_5164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5167_: u8 = 0;
    let mut v___x_5169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5171_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5091_ = l_Lean_Meta_Grind_Action_saveStateIfTracing___redArg(
                    v_a_5082_, v_a_5083_, v_a_5087_, v_a_5089_,
                );
                if crate::leanh::lean_obj_tag(v___x_5091_) == 0 {
                    v_a_5092_ = crate::leanh::lean_ctor_get(v___x_5091_, 0);
                    crate::leanh::lean_inc(v_a_5092_);
                    crate::leanh::lean_dec_ref_known(v___x_5091_, 1);
                    crate::leanh::lean_inc(v_a_5089_);
                    crate::leanh::lean_inc_ref(v_a_5088_);
                    crate::leanh::lean_inc(v_a_5087_);
                    crate::leanh::lean_inc_ref(v_a_5086_);
                    crate::leanh::lean_inc(v_a_5085_);
                    crate::leanh::lean_inc_ref(v_a_5084_);
                    crate::leanh::lean_inc(v_a_5083_);
                    crate::leanh::lean_inc_ref(v_a_5082_);
                    crate::leanh::lean_inc(v_a_5081_);
                    crate::leanh::lean_inc_ref(v_goal_5079_);
                    v___x_5093_ = crate::leanh::lean_apply_11(
                        v_kp_5080_,
                        v_goal_5079_,
                        v_a_5081_,
                        v_a_5082_,
                        v_a_5083_,
                        v_a_5084_,
                        v_a_5085_,
                        v_a_5086_,
                        v_a_5087_,
                        v_a_5088_,
                        v_a_5089_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_5093_) == 0 {
                        v_a_5094_ = crate::leanh::lean_ctor_get(v___x_5093_, 0);
                        crate::leanh::lean_inc(v_a_5094_);
                        if crate::leanh::lean_obj_tag(v_a_5094_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_5093_, 1);
                            v_seq_5095_ = crate::leanh::lean_ctor_get(v_a_5094_, 0);
                            crate::leanh::lean_inc(v_seq_5095_);
                            crate::leanh::lean_inc_ref(v_goal_5079_);
                            v___x_5096_ = l_Lean_Meta_Grind_Action_checkSeqAt(
                                v_a_5092_,
                                v_goal_5079_,
                                v_seq_5095_,
                                v_a_5081_,
                                v_a_5082_,
                                v_a_5083_,
                                v_a_5084_,
                                v_a_5085_,
                                v_a_5086_,
                                v_a_5087_,
                                v_a_5088_,
                                v_a_5089_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_5096_) == 0 {
                                v_a_5097_ = crate::leanh::lean_ctor_get(v___x_5096_, 0);
                                v_isSharedCheck_5155_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5096_)) as u8;
                                if v_isSharedCheck_5155_ == 0 {
                                    v___x_5099_ = v___x_5096_;
                                    v_isShared_5100_ = v_isSharedCheck_5155_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5097_);
                                    crate::leanh::lean_dec(v___x_5096_);
                                    v___x_5099_ = crate::leanh::lean_box(0);
                                    v_isShared_5100_ = v_isSharedCheck_5155_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v_a_5094_, 1);
                                crate::leanh::lean_dec_ref(v_goal_5079_);
                                v_a_5156_ = crate::leanh::lean_ctor_get(v___x_5096_, 0);
                                v_isSharedCheck_5163_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5096_)) as u8;
                                if v_isSharedCheck_5163_ == 0 {
                                    v___x_5158_ = v___x_5096_;
                                    v_isShared_5159_ = v_isSharedCheck_5163_;
                                    state = 13;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5156_);
                                    crate::leanh::lean_dec(v___x_5096_);
                                    v___x_5158_ = crate::leanh::lean_box(0);
                                    v_isShared_5159_ = v_isSharedCheck_5163_;
                                    state = 13;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_5094_);
                            crate::leanh::lean_dec(v_a_5092_);
                            crate::leanh::lean_dec_ref(v_goal_5079_);
                            return v___x_5093_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_5092_);
                        crate::leanh::lean_dec_ref(v_goal_5079_);
                        return v___x_5093_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_kp_5080_);
                    crate::leanh::lean_dec_ref(v_goal_5079_);
                    v_a_5164_ = crate::leanh::lean_ctor_get(v___x_5091_, 0);
                    v_isSharedCheck_5171_ = (!crate::leanh::lean_is_exclusive(v___x_5091_)) as u8;
                    if v_isSharedCheck_5171_ == 0 {
                        v___x_5166_ = v___x_5091_;
                        v_isShared_5167_ = v_isSharedCheck_5171_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5164_);
                        crate::leanh::lean_dec(v___x_5091_);
                        v___x_5166_ = crate::leanh::lean_box(0);
                        v_isShared_5167_ = v_isSharedCheck_5171_;
                        state = 15;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5101_ = (crate::leanh::lean_unbox(v_a_5097_) as u8);
                crate::leanh::lean_dec(v_a_5097_);
                if v___x_5101_ == 0 {
                    crate::leanh::lean_del_object(v___x_5099_);
                    crate::leanh::lean_inc(v_seq_5095_);
                    v___x_5102_ =
                        l_Lean_Meta_Grind_Action_mkGrindNext___redArg(v_seq_5095_, v_a_5088_);
                    v_a_5103_ = crate::leanh::lean_ctor_get(v___x_5102_, 0);
                    v_isSharedCheck_5151_ = (!crate::leanh::lean_is_exclusive(v___x_5102_)) as u8;
                    if v_isSharedCheck_5151_ == 0 {
                        v___x_5105_ = v___x_5102_;
                        v_isShared_5106_ = v_isSharedCheck_5151_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5103_);
                        crate::leanh::lean_dec(v___x_5102_);
                        v___x_5105_ = crate::leanh::lean_box(0);
                        v_isShared_5106_ = v_isSharedCheck_5151_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_goal_5079_);
                    if v_isShared_5100_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5099_, 0, v_a_5094_);
                        v___x_5153_ = v___x_5099_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_5154_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5154_, 0, v_a_5094_);
                        v___x_5153_ = v_reuseFailAlloc_5154_;
                        state = 12;
                        continue;
                    }
                }
            }
            2 => {
                v_mvarId_5107_ = crate::leanh::lean_ctor_get(v_goal_5079_, 1);
                v_isSharedCheck_5149_ = (!crate::leanh::lean_is_exclusive(v_goal_5079_)) as u8;
                if v_isSharedCheck_5149_ == 0 {
                    v_unused_5150_ = crate::leanh::lean_ctor_get(v_goal_5079_, 0);
                    crate::leanh::lean_dec(v_unused_5150_);
                    v___x_5109_ = v_goal_5079_;
                    v_isShared_5110_ = v_isSharedCheck_5149_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_mvarId_5107_);
                    crate::leanh::lean_dec(v_goal_5079_);
                    v___x_5109_ = crate::leanh::lean_box(0);
                    v_isShared_5110_ = v_isSharedCheck_5149_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5111_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__1_once
                    ),
                    _init_l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__1,
                );
                v___x_5112_ = l_Lean_MessageData_ofSyntax(v_a_5103_);
                v___x_5113_ = l_Lean_indentD(v___x_5112_);
                if v_isShared_5110_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5109_, 7);
                    crate::leanh::lean_ctor_set(v___x_5109_, 1, v___x_5113_);
                    crate::leanh::lean_ctor_set(v___x_5109_, 0, v___x_5111_);
                    v___x_5115_ = v___x_5109_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5148_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5148_, 0, v___x_5111_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5148_, 1, v___x_5113_);
                    v___x_5115_ = v_reuseFailAlloc_5148_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5116_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__3_once
                    ),
                    _init_l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__3,
                );
                v___x_5117_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5117_, 0, v___x_5115_);
                crate::leanh::lean_ctor_set(v___x_5117_, 1, v___x_5116_);
                if v_isShared_5106_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5105_, 1);
                    crate::leanh::lean_ctor_set(v___x_5105_, 0, v_mvarId_5107_);
                    v___x_5119_ = v___x_5105_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5147_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5147_, 0, v_mvarId_5107_);
                    v___x_5119_ = v_reuseFailAlloc_5147_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5120_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5120_, 0, v___x_5117_);
                crate::leanh::lean_ctor_set(v___x_5120_, 1, v___x_5119_);
                if v_warnOnly_5078_ == 0 {
                    crate::leanh::lean_dec_ref_known(v_a_5094_, 1);
                    v___x_5121_ = l_Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0___redArg(v___x_5120_, v_a_5086_, v_a_5087_, v_a_5088_, v_a_5089_);
                    v_a_5122_ = crate::leanh::lean_ctor_get(v___x_5121_, 0);
                    v_isSharedCheck_5129_ = (!crate::leanh::lean_is_exclusive(v___x_5121_)) as u8;
                    if v_isSharedCheck_5129_ == 0 {
                        v___x_5124_ = v___x_5121_;
                        v_isShared_5125_ = v_isSharedCheck_5129_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5122_);
                        crate::leanh::lean_dec(v___x_5121_);
                        v___x_5124_ = crate::leanh::lean_box(0);
                        v_isShared_5125_ = v_isSharedCheck_5129_;
                        state = 6;
                        continue;
                    }
                } else {
                    v___x_5130_ =
                        l_Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1(
                            v___x_5120_,
                            v_a_5081_,
                            v_a_5082_,
                            v_a_5083_,
                            v_a_5084_,
                            v_a_5085_,
                            v_a_5086_,
                            v_a_5087_,
                            v_a_5088_,
                            v_a_5089_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_5130_) == 0 {
                        v_isSharedCheck_5137_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5130_)) as u8;
                        if v_isSharedCheck_5137_ == 0 {
                            v_unused_5138_ = crate::leanh::lean_ctor_get(v___x_5130_, 0);
                            crate::leanh::lean_dec(v_unused_5138_);
                            v___x_5132_ = v___x_5130_;
                            v_isShared_5133_ = v_isSharedCheck_5137_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_5130_);
                            v___x_5132_ = crate::leanh::lean_box(0);
                            v_isShared_5133_ = v_isSharedCheck_5137_;
                            state = 8;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_a_5094_, 1);
                        v_a_5139_ = crate::leanh::lean_ctor_get(v___x_5130_, 0);
                        v_isSharedCheck_5146_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5130_)) as u8;
                        if v_isSharedCheck_5146_ == 0 {
                            v___x_5141_ = v___x_5130_;
                            v_isShared_5142_ = v_isSharedCheck_5146_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5139_);
                            crate::leanh::lean_dec(v___x_5130_);
                            v___x_5141_ = crate::leanh::lean_box(0);
                            v_isShared_5142_ = v_isSharedCheck_5146_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            6 => {
                if v_isShared_5125_ == 0 {
                    v___x_5127_ = v___x_5124_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5128_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5128_, 0, v_a_5122_);
                    v___x_5127_ = v_reuseFailAlloc_5128_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5127_;
            }
            8 => {
                if v_isShared_5133_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5132_, 0, v_a_5094_);
                    v___x_5135_ = v___x_5132_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5136_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5136_, 0, v_a_5094_);
                    v___x_5135_ = v_reuseFailAlloc_5136_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5135_;
            }
            10 => {
                if v_isShared_5142_ == 0 {
                    v___x_5144_ = v___x_5141_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5145_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5145_, 0, v_a_5139_);
                    v___x_5144_ = v_reuseFailAlloc_5145_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_5144_;
            }
            12 => {
                return v___x_5153_;
            }
            13 => {
                if v_isShared_5159_ == 0 {
                    v___x_5161_ = v___x_5158_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5162_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5162_, 0, v_a_5156_);
                    v___x_5161_ = v_reuseFailAlloc_5162_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_5161_;
            }
            15 => {
                if v_isShared_5167_ == 0 {
                    v___x_5169_ = v___x_5166_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_5170_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5170_, 0, v_a_5164_);
                    v___x_5169_ = v_reuseFailAlloc_5170_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_5169_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Action_checkTactic___redArg___boxed(
    mut v_warnOnly_5172_: *mut crate::leanh::LeanObject,
    mut v_goal_5173_: *mut crate::leanh::LeanObject,
    mut v_kp_5174_: *mut crate::leanh::LeanObject,
    mut v_a_5175_: *mut crate::leanh::LeanObject,
    mut v_a_5176_: *mut crate::leanh::LeanObject,
    mut v_a_5177_: *mut crate::leanh::LeanObject,
    mut v_a_5178_: *mut crate::leanh::LeanObject,
    mut v_a_5179_: *mut crate::leanh::LeanObject,
    mut v_a_5180_: *mut crate::leanh::LeanObject,
    mut v_a_5181_: *mut crate::leanh::LeanObject,
    mut v_a_5182_: *mut crate::leanh::LeanObject,
    mut v_a_5183_: *mut crate::leanh::LeanObject,
    mut v_a_5184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_warnOnly_boxed_5185_: u8 = 0;
    let mut v_res_5186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_warnOnly_boxed_5185_ = (crate::leanh::lean_unbox(v_warnOnly_5172_) as u8);
    v_res_5186_ = l_Lean_Meta_Grind_Action_checkTactic___redArg(
        v_warnOnly_boxed_5185_,
        v_goal_5173_,
        v_kp_5174_,
        v_a_5175_,
        v_a_5176_,
        v_a_5177_,
        v_a_5178_,
        v_a_5179_,
        v_a_5180_,
        v_a_5181_,
        v_a_5182_,
        v_a_5183_,
    );
    crate::leanh::lean_dec(v_a_5183_);
    crate::leanh::lean_dec_ref(v_a_5182_);
    crate::leanh::lean_dec(v_a_5181_);
    crate::leanh::lean_dec_ref(v_a_5180_);
    crate::leanh::lean_dec(v_a_5179_);
    crate::leanh::lean_dec_ref(v_a_5178_);
    crate::leanh::lean_dec(v_a_5177_);
    crate::leanh::lean_dec_ref(v_a_5176_);
    crate::leanh::lean_dec(v_a_5175_);
    return v_res_5186_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_checkTactic(
    mut v_warnOnly_5187_: u8,
    mut v_goal_5188_: *mut crate::leanh::LeanObject,
    mut v_x_5189_: *mut crate::leanh::LeanObject,
    mut v_kp_5190_: *mut crate::leanh::LeanObject,
    mut v_a_5191_: *mut crate::leanh::LeanObject,
    mut v_a_5192_: *mut crate::leanh::LeanObject,
    mut v_a_5193_: *mut crate::leanh::LeanObject,
    mut v_a_5194_: *mut crate::leanh::LeanObject,
    mut v_a_5195_: *mut crate::leanh::LeanObject,
    mut v_a_5196_: *mut crate::leanh::LeanObject,
    mut v_a_5197_: *mut crate::leanh::LeanObject,
    mut v_a_5198_: *mut crate::leanh::LeanObject,
    mut v_a_5199_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5201_ = l_Lean_Meta_Grind_Action_checkTactic___redArg(
        v_warnOnly_5187_,
        v_goal_5188_,
        v_kp_5190_,
        v_a_5191_,
        v_a_5192_,
        v_a_5193_,
        v_a_5194_,
        v_a_5195_,
        v_a_5196_,
        v_a_5197_,
        v_a_5198_,
        v_a_5199_,
    );
    return v___x_5201_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_checkTactic___boxed(
    mut v_warnOnly_5202_: *mut crate::leanh::LeanObject,
    mut v_goal_5203_: *mut crate::leanh::LeanObject,
    mut v_x_5204_: *mut crate::leanh::LeanObject,
    mut v_kp_5205_: *mut crate::leanh::LeanObject,
    mut v_a_5206_: *mut crate::leanh::LeanObject,
    mut v_a_5207_: *mut crate::leanh::LeanObject,
    mut v_a_5208_: *mut crate::leanh::LeanObject,
    mut v_a_5209_: *mut crate::leanh::LeanObject,
    mut v_a_5210_: *mut crate::leanh::LeanObject,
    mut v_a_5211_: *mut crate::leanh::LeanObject,
    mut v_a_5212_: *mut crate::leanh::LeanObject,
    mut v_a_5213_: *mut crate::leanh::LeanObject,
    mut v_a_5214_: *mut crate::leanh::LeanObject,
    mut v_a_5215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_warnOnly_boxed_5216_: u8 = 0;
    let mut v_res_5217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_warnOnly_boxed_5216_ = (crate::leanh::lean_unbox(v_warnOnly_5202_) as u8);
    v_res_5217_ = l_Lean_Meta_Grind_Action_checkTactic(
        v_warnOnly_boxed_5216_,
        v_goal_5203_,
        v_x_5204_,
        v_kp_5205_,
        v_a_5206_,
        v_a_5207_,
        v_a_5208_,
        v_a_5209_,
        v_a_5210_,
        v_a_5211_,
        v_a_5212_,
        v_a_5213_,
        v_a_5214_,
    );
    crate::leanh::lean_dec(v_a_5214_);
    crate::leanh::lean_dec_ref(v_a_5213_);
    crate::leanh::lean_dec(v_a_5212_);
    crate::leanh::lean_dec_ref(v_a_5211_);
    crate::leanh::lean_dec(v_a_5210_);
    crate::leanh::lean_dec_ref(v_a_5209_);
    crate::leanh::lean_dec(v_a_5208_);
    crate::leanh::lean_dec_ref(v_a_5207_);
    crate::leanh::lean_dec(v_a_5206_);
    crate::leanh::lean_dec_ref(v_x_5204_);
    return v_res_5217_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0(
    mut v_00_u03b1_5218_: *mut crate::leanh::LeanObject,
    mut v_msg_5219_: *mut crate::leanh::LeanObject,
    mut v___y_5220_: *mut crate::leanh::LeanObject,
    mut v___y_5221_: *mut crate::leanh::LeanObject,
    mut v___y_5222_: *mut crate::leanh::LeanObject,
    mut v___y_5223_: *mut crate::leanh::LeanObject,
    mut v___y_5224_: *mut crate::leanh::LeanObject,
    mut v___y_5225_: *mut crate::leanh::LeanObject,
    mut v___y_5226_: *mut crate::leanh::LeanObject,
    mut v___y_5227_: *mut crate::leanh::LeanObject,
    mut v___y_5228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5230_ = l_Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0___redArg(
        v_msg_5219_,
        v___y_5225_,
        v___y_5226_,
        v___y_5227_,
        v___y_5228_,
    );
    return v___x_5230_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0___boxed(
    mut v_00_u03b1_5231_: *mut crate::leanh::LeanObject,
    mut v_msg_5232_: *mut crate::leanh::LeanObject,
    mut v___y_5233_: *mut crate::leanh::LeanObject,
    mut v___y_5234_: *mut crate::leanh::LeanObject,
    mut v___y_5235_: *mut crate::leanh::LeanObject,
    mut v___y_5236_: *mut crate::leanh::LeanObject,
    mut v___y_5237_: *mut crate::leanh::LeanObject,
    mut v___y_5238_: *mut crate::leanh::LeanObject,
    mut v___y_5239_: *mut crate::leanh::LeanObject,
    mut v___y_5240_: *mut crate::leanh::LeanObject,
    mut v___y_5241_: *mut crate::leanh::LeanObject,
    mut v___y_5242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5243_ = l_Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0(
        v_00_u03b1_5231_,
        v_msg_5232_,
        v___y_5233_,
        v___y_5234_,
        v___y_5235_,
        v___y_5236_,
        v___y_5237_,
        v___y_5238_,
        v___y_5239_,
        v___y_5240_,
        v___y_5241_,
    );
    crate::leanh::lean_dec(v___y_5241_);
    crate::leanh::lean_dec_ref(v___y_5240_);
    crate::leanh::lean_dec(v___y_5239_);
    crate::leanh::lean_dec_ref(v___y_5238_);
    crate::leanh::lean_dec(v___y_5237_);
    crate::leanh::lean_dec_ref(v___y_5236_);
    crate::leanh::lean_dec(v___y_5235_);
    crate::leanh::lean_dec_ref(v___y_5234_);
    crate::leanh::lean_dec(v___y_5233_);
    return v_res_5243_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3(
    mut v_ref_5244_: *mut crate::leanh::LeanObject,
    mut v_msgData_5245_: *mut crate::leanh::LeanObject,
    mut v_severity_5246_: u8,
    mut v_isSilent_5247_: u8,
    mut v___y_5248_: *mut crate::leanh::LeanObject,
    mut v___y_5249_: *mut crate::leanh::LeanObject,
    mut v___y_5250_: *mut crate::leanh::LeanObject,
    mut v___y_5251_: *mut crate::leanh::LeanObject,
    mut v___y_5252_: *mut crate::leanh::LeanObject,
    mut v___y_5253_: *mut crate::leanh::LeanObject,
    mut v___y_5254_: *mut crate::leanh::LeanObject,
    mut v___y_5255_: *mut crate::leanh::LeanObject,
    mut v___y_5256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5258_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg(v_ref_5244_, v_msgData_5245_, v_severity_5246_, v_isSilent_5247_, v___y_5253_, v___y_5254_, v___y_5255_, v___y_5256_);
    return v___x_5258_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___boxed(
    mut v_ref_5259_: *mut crate::leanh::LeanObject,
    mut v_msgData_5260_: *mut crate::leanh::LeanObject,
    mut v_severity_5261_: *mut crate::leanh::LeanObject,
    mut v_isSilent_5262_: *mut crate::leanh::LeanObject,
    mut v___y_5263_: *mut crate::leanh::LeanObject,
    mut v___y_5264_: *mut crate::leanh::LeanObject,
    mut v___y_5265_: *mut crate::leanh::LeanObject,
    mut v___y_5266_: *mut crate::leanh::LeanObject,
    mut v___y_5267_: *mut crate::leanh::LeanObject,
    mut v___y_5268_: *mut crate::leanh::LeanObject,
    mut v___y_5269_: *mut crate::leanh::LeanObject,
    mut v___y_5270_: *mut crate::leanh::LeanObject,
    mut v___y_5271_: *mut crate::leanh::LeanObject,
    mut v___y_5272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_5273_: u8 = 0;
    let mut v_isSilent_boxed_5274_: u8 = 0;
    let mut v_res_5275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_5273_ = (crate::leanh::lean_unbox(v_severity_5261_) as u8);
    v_isSilent_boxed_5274_ = (crate::leanh::lean_unbox(v_isSilent_5262_) as u8);
    v_res_5275_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3(v_ref_5259_, v_msgData_5260_, v_severity_boxed_5273_, v_isSilent_boxed_5274_, v___y_5263_, v___y_5264_, v___y_5265_, v___y_5266_, v___y_5267_, v___y_5268_, v___y_5269_, v___y_5270_, v___y_5271_);
    crate::leanh::lean_dec(v___y_5271_);
    crate::leanh::lean_dec_ref(v___y_5270_);
    crate::leanh::lean_dec(v___y_5269_);
    crate::leanh::lean_dec_ref(v___y_5268_);
    crate::leanh::lean_dec(v___y_5267_);
    crate::leanh::lean_dec_ref(v___y_5266_);
    crate::leanh::lean_dec(v___y_5265_);
    crate::leanh::lean_dec_ref(v___y_5264_);
    crate::leanh::lean_dec(v___y_5263_);
    crate::leanh::lean_dec(v_ref_5259_);
    return v_res_5275_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_solverAction___lam__0(
    mut v_goal_5276_: *mut crate::leanh::LeanObject,
    mut v_check_5277_: *mut crate::leanh::LeanObject,
    mut v___y_5278_: *mut crate::leanh::LeanObject,
    mut v___y_5279_: *mut crate::leanh::LeanObject,
    mut v___y_5280_: *mut crate::leanh::LeanObject,
    mut v___y_5281_: *mut crate::leanh::LeanObject,
    mut v___y_5282_: *mut crate::leanh::LeanObject,
    mut v___y_5283_: *mut crate::leanh::LeanObject,
    mut v___y_5284_: *mut crate::leanh::LeanObject,
    mut v___y_5285_: *mut crate::leanh::LeanObject,
    mut v___y_5286_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5293_: u8 = 0;
    let mut v___x_5294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5299_: u8 = 0;
    let mut v_a_5300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5303_: u8 = 0;
    let mut v___x_5305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5307_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5288_ = lean_st_mk_ref(v_goal_5276_);
                crate::leanh::lean_inc(v___x_5288_);
                v___x_5289_ = crate::leanh::lean_apply_11(
                    v_check_5277_,
                    v___x_5288_,
                    v___y_5278_,
                    v___y_5279_,
                    v___y_5280_,
                    v___y_5281_,
                    v___y_5282_,
                    v___y_5283_,
                    v___y_5284_,
                    v___y_5285_,
                    v___y_5286_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_5289_) == 0 {
                    v_a_5290_ = crate::leanh::lean_ctor_get(v___x_5289_, 0);
                    v_isSharedCheck_5299_ = (!crate::leanh::lean_is_exclusive(v___x_5289_)) as u8;
                    if v_isSharedCheck_5299_ == 0 {
                        v___x_5292_ = v___x_5289_;
                        v_isShared_5293_ = v_isSharedCheck_5299_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5290_);
                        crate::leanh::lean_dec(v___x_5289_);
                        v___x_5292_ = crate::leanh::lean_box(0);
                        v_isShared_5293_ = v_isSharedCheck_5299_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5288_);
                    v_a_5300_ = crate::leanh::lean_ctor_get(v___x_5289_, 0);
                    v_isSharedCheck_5307_ = (!crate::leanh::lean_is_exclusive(v___x_5289_)) as u8;
                    if v_isSharedCheck_5307_ == 0 {
                        v___x_5302_ = v___x_5289_;
                        v_isShared_5303_ = v_isSharedCheck_5307_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5300_);
                        crate::leanh::lean_dec(v___x_5289_);
                        v___x_5302_ = crate::leanh::lean_box(0);
                        v_isShared_5303_ = v_isSharedCheck_5307_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5294_ = lean_st_ref_get(v___x_5288_);
                crate::leanh::lean_dec(v___x_5288_);
                v___x_5295_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5295_, 0, v_a_5290_);
                crate::leanh::lean_ctor_set(v___x_5295_, 1, v___x_5294_);
                if v_isShared_5293_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5292_, 0, v___x_5295_);
                    v___x_5297_ = v___x_5292_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5298_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5298_, 0, v___x_5295_);
                    v___x_5297_ = v_reuseFailAlloc_5298_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5297_;
            }
            3 => {
                if v_isShared_5303_ == 0 {
                    v___x_5305_ = v___x_5302_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5306_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5306_, 0, v_a_5300_);
                    v___x_5305_ = v_reuseFailAlloc_5306_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5305_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Action_solverAction___lam__0___boxed(
    mut v_goal_5308_: *mut crate::leanh::LeanObject,
    mut v_check_5309_: *mut crate::leanh::LeanObject,
    mut v___y_5310_: *mut crate::leanh::LeanObject,
    mut v___y_5311_: *mut crate::leanh::LeanObject,
    mut v___y_5312_: *mut crate::leanh::LeanObject,
    mut v___y_5313_: *mut crate::leanh::LeanObject,
    mut v___y_5314_: *mut crate::leanh::LeanObject,
    mut v___y_5315_: *mut crate::leanh::LeanObject,
    mut v___y_5316_: *mut crate::leanh::LeanObject,
    mut v___y_5317_: *mut crate::leanh::LeanObject,
    mut v___y_5318_: *mut crate::leanh::LeanObject,
    mut v___y_5319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5320_ = l_Lean_Meta_Grind_Action_solverAction___lam__0(
        v_goal_5308_,
        v_check_5309_,
        v___y_5310_,
        v___y_5311_,
        v___y_5312_,
        v___y_5313_,
        v___y_5314_,
        v___y_5315_,
        v___y_5316_,
        v___y_5317_,
        v___y_5318_,
    );
    return v_res_5320_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_solverAction___lam__1(
    mut v_snd_5321_: *mut crate::leanh::LeanObject,
    mut v___y_5322_: *mut crate::leanh::LeanObject,
    mut v___y_5323_: *mut crate::leanh::LeanObject,
    mut v___y_5324_: *mut crate::leanh::LeanObject,
    mut v___y_5325_: *mut crate::leanh::LeanObject,
    mut v___y_5326_: *mut crate::leanh::LeanObject,
    mut v___y_5327_: *mut crate::leanh::LeanObject,
    mut v___y_5328_: *mut crate::leanh::LeanObject,
    mut v___y_5329_: *mut crate::leanh::LeanObject,
    mut v___y_5330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5336_: u8 = 0;
    let mut v___x_5337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5342_: u8 = 0;
    let mut v_unused_5343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5347_: u8 = 0;
    let mut v___x_5349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5351_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5332_ = lean_st_mk_ref(v_snd_5321_);
                crate::leanh::lean_inc(v___y_5330_);
                crate::leanh::lean_inc_ref(v___y_5329_);
                crate::leanh::lean_inc(v___y_5328_);
                crate::leanh::lean_inc_ref(v___y_5327_);
                crate::leanh::lean_inc(v___y_5326_);
                crate::leanh::lean_inc_ref(v___y_5325_);
                crate::leanh::lean_inc(v___y_5324_);
                crate::leanh::lean_inc_ref(v___y_5323_);
                crate::leanh::lean_inc(v___y_5322_);
                crate::leanh::lean_inc(v___x_5332_);
                v___x_5333_ = lean_grind_process_new_facts(
                    v___x_5332_,
                    v___y_5322_,
                    v___y_5323_,
                    v___y_5324_,
                    v___y_5325_,
                    v___y_5326_,
                    v___y_5327_,
                    v___y_5328_,
                    v___y_5329_,
                    v___y_5330_,
                );
                if crate::leanh::lean_obj_tag(v___x_5333_) == 0 {
                    v_isSharedCheck_5342_ = (!crate::leanh::lean_is_exclusive(v___x_5333_)) as u8;
                    if v_isSharedCheck_5342_ == 0 {
                        v_unused_5343_ = crate::leanh::lean_ctor_get(v___x_5333_, 0);
                        crate::leanh::lean_dec(v_unused_5343_);
                        v___x_5335_ = v___x_5333_;
                        v_isShared_5336_ = v_isSharedCheck_5342_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_5333_);
                        v___x_5335_ = crate::leanh::lean_box(0);
                        v_isShared_5336_ = v_isSharedCheck_5342_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5332_);
                    v_a_5344_ = crate::leanh::lean_ctor_get(v___x_5333_, 0);
                    v_isSharedCheck_5351_ = (!crate::leanh::lean_is_exclusive(v___x_5333_)) as u8;
                    if v_isSharedCheck_5351_ == 0 {
                        v___x_5346_ = v___x_5333_;
                        v_isShared_5347_ = v_isSharedCheck_5351_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5344_);
                        crate::leanh::lean_dec(v___x_5333_);
                        v___x_5346_ = crate::leanh::lean_box(0);
                        v_isShared_5347_ = v_isSharedCheck_5351_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5337_ = lean_st_ref_get(v___x_5332_);
                v___x_5338_ = lean_st_ref_get(v___x_5332_);
                crate::leanh::lean_dec(v___x_5332_);
                crate::leanh::lean_dec(v___x_5338_);
                if v_isShared_5336_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5335_, 0, v___x_5337_);
                    v___x_5340_ = v___x_5335_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5341_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5341_, 0, v___x_5337_);
                    v___x_5340_ = v_reuseFailAlloc_5341_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5340_;
            }
            3 => {
                if v_isShared_5347_ == 0 {
                    v___x_5349_ = v___x_5346_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5350_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5350_, 0, v_a_5344_);
                    v___x_5349_ = v_reuseFailAlloc_5350_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5349_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Action_solverAction___lam__1___boxed(
    mut v_snd_5352_: *mut crate::leanh::LeanObject,
    mut v___y_5353_: *mut crate::leanh::LeanObject,
    mut v___y_5354_: *mut crate::leanh::LeanObject,
    mut v___y_5355_: *mut crate::leanh::LeanObject,
    mut v___y_5356_: *mut crate::leanh::LeanObject,
    mut v___y_5357_: *mut crate::leanh::LeanObject,
    mut v___y_5358_: *mut crate::leanh::LeanObject,
    mut v___y_5359_: *mut crate::leanh::LeanObject,
    mut v___y_5360_: *mut crate::leanh::LeanObject,
    mut v___y_5361_: *mut crate::leanh::LeanObject,
    mut v___y_5362_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5363_ = l_Lean_Meta_Grind_Action_solverAction___lam__1(
        v_snd_5352_,
        v___y_5353_,
        v___y_5354_,
        v___y_5355_,
        v___y_5356_,
        v___y_5357_,
        v___y_5358_,
        v___y_5359_,
        v___y_5360_,
        v___y_5361_,
    );
    crate::leanh::lean_dec(v___y_5361_);
    crate::leanh::lean_dec_ref(v___y_5360_);
    crate::leanh::lean_dec(v___y_5359_);
    crate::leanh::lean_dec_ref(v___y_5358_);
    crate::leanh::lean_dec(v___y_5357_);
    crate::leanh::lean_dec_ref(v___y_5356_);
    crate::leanh::lean_dec(v___y_5355_);
    crate::leanh::lean_dec_ref(v___y_5354_);
    crate::leanh::lean_dec(v___y_5353_);
    return v_res_5363_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_solverAction(
    mut v_check_5364_: *mut crate::leanh::LeanObject,
    mut v_mkTac_5365_: *mut crate::leanh::LeanObject,
    mut v_goal_5366_: *mut crate::leanh::LeanObject,
    mut v_kna_5367_: *mut crate::leanh::LeanObject,
    mut v_kp_5368_: *mut crate::leanh::LeanObject,
    mut v_a_5369_: *mut crate::leanh::LeanObject,
    mut v_a_5370_: *mut crate::leanh::LeanObject,
    mut v_a_5371_: *mut crate::leanh::LeanObject,
    mut v_a_5372_: *mut crate::leanh::LeanObject,
    mut v_a_5373_: *mut crate::leanh::LeanObject,
    mut v_a_5374_: *mut crate::leanh::LeanObject,
    mut v_a_5375_: *mut crate::leanh::LeanObject,
    mut v_a_5376_: *mut crate::leanh::LeanObject,
    mut v_a_5377_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_5381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5386_: u8 = 0;
    let mut v_snd_5387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5394_: u8 = 0;
    let mut v_mvarId_5395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toGoalState_5399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inconsistent_5400_: u8 = 0;
    let mut v___x_5401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trace_5403_: u8 = 0;
    let mut v___x_5404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_seq_5407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5412_: u8 = 0;
    let mut v___x_5413_: u8 = 0;
    let mut v___x_5415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5416_: u8 = 0;
    let mut v___x_5417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5421_: u8 = 0;
    let mut v___x_5423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5431_: u8 = 0;
    let mut v_a_5432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5435_: u8 = 0;
    let mut v___x_5437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5439_: u8 = 0;
    let mut v_isSharedCheck_5440_: u8 = 0;
    let mut v_unused_5441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5445_: u8 = 0;
    let mut v_a_5446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5449_: u8 = 0;
    let mut v___x_5451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5453_: u8 = 0;
    let mut v_a_5454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5457_: u8 = 0;
    let mut v___x_5459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5461_: u8 = 0;
    let mut v___x_5462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5466_: u8 = 0;
    let mut v___x_5468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5470_: u8 = 0;
    let mut v_isSharedCheck_5471_: u8 = 0;
    let mut v_unused_5472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5477_: u8 = 0;
    let mut v___x_5479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5481_: u8 = 0;
    let mut v_a_5482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5485_: u8 = 0;
    let mut v___x_5487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5489_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5379_ = l_Lean_Meta_Grind_Action_saveStateIfTracing___redArg(
                    v_a_5370_, v_a_5371_, v_a_5375_, v_a_5377_,
                );
                if crate::leanh::lean_obj_tag(v___x_5379_) == 0 {
                    v_a_5380_ = crate::leanh::lean_ctor_get(v___x_5379_, 0);
                    crate::leanh::lean_inc(v_a_5380_);
                    crate::leanh::lean_dec_ref_known(v___x_5379_, 1);
                    v_mvarId_5381_ = crate::leanh::lean_ctor_get(v_goal_5366_, 1);
                    crate::leanh::lean_inc_ref(v_goal_5366_);
                    v___f_5382_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Meta_Grind_Action_solverAction___lam__0___boxed
                            as *mut core::ffi::c_void,
                        12,
                        2,
                    );
                    crate::leanh::lean_closure_set(v___f_5382_, 0, v_goal_5366_);
                    crate::leanh::lean_closure_set(v___f_5382_, 1, v_check_5364_);
                    crate::leanh::lean_inc(v_mvarId_5381_);
                    v___x_5383_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg(v_mvarId_5381_, v___f_5382_, v_a_5369_, v_a_5370_, v_a_5371_, v_a_5372_, v_a_5373_, v_a_5374_, v_a_5375_, v_a_5376_, v_a_5377_);
                    if crate::leanh::lean_obj_tag(v___x_5383_) == 0 {
                        v_a_5384_ = crate::leanh::lean_ctor_get(v___x_5383_, 0);
                        crate::leanh::lean_inc(v_a_5384_);
                        crate::leanh::lean_dec_ref_known(v___x_5383_, 1);
                        v_fst_5385_ = crate::leanh::lean_ctor_get(v_a_5384_, 0);
                        v___x_5386_ = (crate::leanh::lean_unbox(v_fst_5385_) as u8);
                        match v___x_5386_ {
                            0 => {
                                crate::leanh::lean_dec(v_a_5380_);
                                crate::leanh::lean_dec_ref(v_kp_5368_);
                                crate::leanh::lean_dec_ref(v_goal_5366_);
                                crate::leanh::lean_dec_ref(v_mkTac_5365_);
                                v_snd_5387_ = crate::leanh::lean_ctor_get(v_a_5384_, 1);
                                crate::leanh::lean_inc(v_snd_5387_);
                                crate::leanh::lean_dec(v_a_5384_);
                                crate::leanh::lean_inc(v_a_5377_);
                                crate::leanh::lean_inc_ref(v_a_5376_);
                                crate::leanh::lean_inc(v_a_5375_);
                                crate::leanh::lean_inc_ref(v_a_5374_);
                                crate::leanh::lean_inc(v_a_5373_);
                                crate::leanh::lean_inc_ref(v_a_5372_);
                                crate::leanh::lean_inc(v_a_5371_);
                                crate::leanh::lean_inc_ref(v_a_5370_);
                                crate::leanh::lean_inc(v_a_5369_);
                                v___x_5388_ = crate::leanh::lean_apply_11(
                                    v_kna_5367_,
                                    v_snd_5387_,
                                    v_a_5369_,
                                    v_a_5370_,
                                    v_a_5371_,
                                    v_a_5372_,
                                    v_a_5373_,
                                    v_a_5374_,
                                    v_a_5375_,
                                    v_a_5376_,
                                    v_a_5377_,
                                    crate::leanh::lean_box(0),
                                );
                                return v___x_5388_;
                            }
                            1 => {
                                crate::leanh::lean_dec(v_a_5380_);
                                crate::leanh::lean_dec_ref(v_kna_5367_);
                                crate::leanh::lean_dec_ref(v_goal_5366_);
                                crate::leanh::lean_dec_ref(v_mkTac_5365_);
                                v_snd_5389_ = crate::leanh::lean_ctor_get(v_a_5384_, 1);
                                crate::leanh::lean_inc(v_snd_5389_);
                                crate::leanh::lean_dec(v_a_5384_);
                                crate::leanh::lean_inc(v_a_5377_);
                                crate::leanh::lean_inc_ref(v_a_5376_);
                                crate::leanh::lean_inc(v_a_5375_);
                                crate::leanh::lean_inc_ref(v_a_5374_);
                                crate::leanh::lean_inc(v_a_5373_);
                                crate::leanh::lean_inc_ref(v_a_5372_);
                                crate::leanh::lean_inc(v_a_5371_);
                                crate::leanh::lean_inc_ref(v_a_5370_);
                                crate::leanh::lean_inc(v_a_5369_);
                                v___x_5390_ = crate::leanh::lean_apply_11(
                                    v_kp_5368_,
                                    v_snd_5389_,
                                    v_a_5369_,
                                    v_a_5370_,
                                    v_a_5371_,
                                    v_a_5372_,
                                    v_a_5373_,
                                    v_a_5374_,
                                    v_a_5375_,
                                    v_a_5376_,
                                    v_a_5377_,
                                    crate::leanh::lean_box(0),
                                );
                                return v___x_5390_;
                            }
                            2 => {
                                crate::leanh::lean_dec_ref(v_kna_5367_);
                                v_snd_5391_ = crate::leanh::lean_ctor_get(v_a_5384_, 1);
                                v_isSharedCheck_5471_ =
                                    (!crate::leanh::lean_is_exclusive(v_a_5384_)) as u8;
                                if v_isSharedCheck_5471_ == 0 {
                                    v_unused_5472_ = crate::leanh::lean_ctor_get(v_a_5384_, 0);
                                    crate::leanh::lean_dec(v_unused_5472_);
                                    v___x_5393_ = v_a_5384_;
                                    v_isShared_5394_ = v_isSharedCheck_5471_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_snd_5391_);
                                    crate::leanh::lean_dec(v_a_5384_);
                                    v___x_5393_ = crate::leanh::lean_box(0);
                                    v_isShared_5394_ = v_isSharedCheck_5471_;
                                    state = 1;
                                    continue;
                                }
                            }
                            _ => {
                                crate::leanh::lean_dec(v_a_5384_);
                                crate::leanh::lean_dec(v_a_5380_);
                                crate::leanh::lean_dec_ref(v_kp_5368_);
                                crate::leanh::lean_dec_ref(v_kna_5367_);
                                crate::leanh::lean_dec_ref(v_goal_5366_);
                                v___x_5473_ = l_Lean_Meta_Grind_Action_closeWith(
                                    v_mkTac_5365_,
                                    v_a_5369_,
                                    v_a_5370_,
                                    v_a_5371_,
                                    v_a_5372_,
                                    v_a_5373_,
                                    v_a_5374_,
                                    v_a_5375_,
                                    v_a_5376_,
                                    v_a_5377_,
                                );
                                return v___x_5473_;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_5380_);
                        crate::leanh::lean_dec_ref(v_kp_5368_);
                        crate::leanh::lean_dec_ref(v_kna_5367_);
                        crate::leanh::lean_dec_ref(v_goal_5366_);
                        crate::leanh::lean_dec_ref(v_mkTac_5365_);
                        v_a_5474_ = crate::leanh::lean_ctor_get(v___x_5383_, 0);
                        v_isSharedCheck_5481_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5383_)) as u8;
                        if v_isSharedCheck_5481_ == 0 {
                            v___x_5476_ = v___x_5383_;
                            v_isShared_5477_ = v_isSharedCheck_5481_;
                            state = 17;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5474_);
                            crate::leanh::lean_dec(v___x_5383_);
                            v___x_5476_ = crate::leanh::lean_box(0);
                            v_isShared_5477_ = v_isSharedCheck_5481_;
                            state = 17;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_kp_5368_);
                    crate::leanh::lean_dec_ref(v_kna_5367_);
                    crate::leanh::lean_dec_ref(v_goal_5366_);
                    crate::leanh::lean_dec_ref(v_mkTac_5365_);
                    crate::leanh::lean_dec_ref(v_check_5364_);
                    v_a_5482_ = crate::leanh::lean_ctor_get(v___x_5379_, 0);
                    v_isSharedCheck_5489_ = (!crate::leanh::lean_is_exclusive(v___x_5379_)) as u8;
                    if v_isSharedCheck_5489_ == 0 {
                        v___x_5484_ = v___x_5379_;
                        v_isShared_5485_ = v_isSharedCheck_5489_;
                        state = 19;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5482_);
                        crate::leanh::lean_dec(v___x_5379_);
                        v___x_5484_ = crate::leanh::lean_box(0);
                        v_isShared_5485_ = v_isSharedCheck_5489_;
                        state = 19;
                        continue;
                    }
                }
            }
            1 => {
                v_mvarId_5395_ = crate::leanh::lean_ctor_get(v_snd_5391_, 1);
                crate::leanh::lean_inc(v_mvarId_5395_);
                v___f_5396_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Meta_Grind_Action_solverAction___lam__1___boxed
                        as *mut core::ffi::c_void,
                    11,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5396_, 0, v_snd_5391_);
                v___x_5397_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg(v_mvarId_5395_, v___f_5396_, v_a_5369_, v_a_5370_, v_a_5371_, v_a_5372_, v_a_5373_, v_a_5374_, v_a_5375_, v_a_5376_, v_a_5377_);
                if crate::leanh::lean_obj_tag(v___x_5397_) == 0 {
                    v_a_5398_ = crate::leanh::lean_ctor_get(v___x_5397_, 0);
                    crate::leanh::lean_inc(v_a_5398_);
                    crate::leanh::lean_dec_ref_known(v___x_5397_, 1);
                    v_toGoalState_5399_ = crate::leanh::lean_ctor_get(v_a_5398_, 0);
                    v_inconsistent_5400_ = crate::leanh::lean_ctor_get_uint8(
                        v_toGoalState_5399_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17) as u32,
                    );
                    if v_inconsistent_5400_ == 0 {
                        v___x_5401_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_5370_);
                        if crate::leanh::lean_obj_tag(v___x_5401_) == 0 {
                            v_a_5402_ = crate::leanh::lean_ctor_get(v___x_5401_, 0);
                            crate::leanh::lean_inc(v_a_5402_);
                            crate::leanh::lean_dec_ref_known(v___x_5401_, 1);
                            v_trace_5403_ = crate::leanh::lean_ctor_get_uint8(
                                v_a_5402_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13) as u32,
                            );
                            crate::leanh::lean_dec(v_a_5402_);
                            if v_trace_5403_ == 0 {
                                crate::leanh::lean_del_object(v___x_5393_);
                                crate::leanh::lean_dec(v_a_5380_);
                                crate::leanh::lean_dec_ref(v_goal_5366_);
                                crate::leanh::lean_dec_ref(v_mkTac_5365_);
                                crate::leanh::lean_inc(v_a_5377_);
                                crate::leanh::lean_inc_ref(v_a_5376_);
                                crate::leanh::lean_inc(v_a_5375_);
                                crate::leanh::lean_inc_ref(v_a_5374_);
                                crate::leanh::lean_inc(v_a_5373_);
                                crate::leanh::lean_inc_ref(v_a_5372_);
                                crate::leanh::lean_inc(v_a_5371_);
                                crate::leanh::lean_inc_ref(v_a_5370_);
                                crate::leanh::lean_inc(v_a_5369_);
                                v___x_5404_ = crate::leanh::lean_apply_11(
                                    v_kp_5368_,
                                    v_a_5398_,
                                    v_a_5369_,
                                    v_a_5370_,
                                    v_a_5371_,
                                    v_a_5372_,
                                    v_a_5373_,
                                    v_a_5374_,
                                    v_a_5375_,
                                    v_a_5376_,
                                    v_a_5377_,
                                    crate::leanh::lean_box(0),
                                );
                                return v___x_5404_;
                            } else {
                                crate::leanh::lean_inc(v_a_5377_);
                                crate::leanh::lean_inc_ref(v_a_5376_);
                                crate::leanh::lean_inc(v_a_5375_);
                                crate::leanh::lean_inc_ref(v_a_5374_);
                                crate::leanh::lean_inc(v_a_5373_);
                                crate::leanh::lean_inc_ref(v_a_5372_);
                                crate::leanh::lean_inc(v_a_5371_);
                                crate::leanh::lean_inc_ref(v_a_5370_);
                                crate::leanh::lean_inc(v_a_5369_);
                                v___x_5405_ = crate::leanh::lean_apply_11(
                                    v_kp_5368_,
                                    v_a_5398_,
                                    v_a_5369_,
                                    v_a_5370_,
                                    v_a_5371_,
                                    v_a_5372_,
                                    v_a_5373_,
                                    v_a_5374_,
                                    v_a_5375_,
                                    v_a_5376_,
                                    v_a_5377_,
                                    crate::leanh::lean_box(0),
                                );
                                if crate::leanh::lean_obj_tag(v___x_5405_) == 0 {
                                    v_a_5406_ = crate::leanh::lean_ctor_get(v___x_5405_, 0);
                                    crate::leanh::lean_inc(v_a_5406_);
                                    if crate::leanh::lean_obj_tag(v_a_5406_) == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_5405_, 1);
                                        v_seq_5407_ = crate::leanh::lean_ctor_get(v_a_5406_, 0);
                                        crate::leanh::lean_inc(v_seq_5407_);
                                        v___x_5408_ = l_Lean_Meta_Grind_Action_checkSeqAt(
                                            v_a_5380_,
                                            v_goal_5366_,
                                            v_seq_5407_,
                                            v_a_5369_,
                                            v_a_5370_,
                                            v_a_5371_,
                                            v_a_5372_,
                                            v_a_5373_,
                                            v_a_5374_,
                                            v_a_5375_,
                                            v_a_5376_,
                                            v_a_5377_,
                                        );
                                        if crate::leanh::lean_obj_tag(v___x_5408_) == 0 {
                                            v_a_5409_ = crate::leanh::lean_ctor_get(v___x_5408_, 0);
                                            v_isSharedCheck_5445_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_5408_))
                                                    as u8;
                                            if v_isSharedCheck_5445_ == 0 {
                                                v___x_5411_ = v___x_5408_;
                                                v_isShared_5412_ = v_isSharedCheck_5445_;
                                                state = 2;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_5409_);
                                                crate::leanh::lean_dec(v___x_5408_);
                                                v___x_5411_ = crate::leanh::lean_box(0);
                                                v_isShared_5412_ = v_isSharedCheck_5445_;
                                                state = 2;
                                                continue;
                                            }
                                        } else {
                                            crate::leanh::lean_dec_ref_known(v_a_5406_, 1);
                                            crate::leanh::lean_del_object(v___x_5393_);
                                            crate::leanh::lean_dec_ref(v_mkTac_5365_);
                                            v_a_5446_ = crate::leanh::lean_ctor_get(v___x_5408_, 0);
                                            v_isSharedCheck_5453_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_5408_))
                                                    as u8;
                                            if v_isSharedCheck_5453_ == 0 {
                                                v___x_5448_ = v___x_5408_;
                                                v_isShared_5449_ = v_isSharedCheck_5453_;
                                                state = 11;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_5446_);
                                                crate::leanh::lean_dec(v___x_5408_);
                                                v___x_5448_ = crate::leanh::lean_box(0);
                                                v_isShared_5449_ = v_isSharedCheck_5453_;
                                                state = 11;
                                                continue;
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_a_5406_);
                                        crate::leanh::lean_del_object(v___x_5393_);
                                        crate::leanh::lean_dec(v_a_5380_);
                                        crate::leanh::lean_dec_ref(v_goal_5366_);
                                        crate::leanh::lean_dec_ref(v_mkTac_5365_);
                                        return v___x_5405_;
                                    }
                                } else {
                                    crate::leanh::lean_del_object(v___x_5393_);
                                    crate::leanh::lean_dec(v_a_5380_);
                                    crate::leanh::lean_dec_ref(v_goal_5366_);
                                    crate::leanh::lean_dec_ref(v_mkTac_5365_);
                                    return v___x_5405_;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_5398_);
                            crate::leanh::lean_del_object(v___x_5393_);
                            crate::leanh::lean_dec(v_a_5380_);
                            crate::leanh::lean_dec_ref(v_kp_5368_);
                            crate::leanh::lean_dec_ref(v_goal_5366_);
                            crate::leanh::lean_dec_ref(v_mkTac_5365_);
                            v_a_5454_ = crate::leanh::lean_ctor_get(v___x_5401_, 0);
                            v_isSharedCheck_5461_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5401_)) as u8;
                            if v_isSharedCheck_5461_ == 0 {
                                v___x_5456_ = v___x_5401_;
                                v_isShared_5457_ = v_isSharedCheck_5461_;
                                state = 13;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5454_);
                                crate::leanh::lean_dec(v___x_5401_);
                                v___x_5456_ = crate::leanh::lean_box(0);
                                v_isShared_5457_ = v_isSharedCheck_5461_;
                                state = 13;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_5398_);
                        crate::leanh::lean_del_object(v___x_5393_);
                        crate::leanh::lean_dec(v_a_5380_);
                        crate::leanh::lean_dec_ref(v_kp_5368_);
                        crate::leanh::lean_dec_ref(v_goal_5366_);
                        v___x_5462_ = l_Lean_Meta_Grind_Action_closeWith(
                            v_mkTac_5365_,
                            v_a_5369_,
                            v_a_5370_,
                            v_a_5371_,
                            v_a_5372_,
                            v_a_5373_,
                            v_a_5374_,
                            v_a_5375_,
                            v_a_5376_,
                            v_a_5377_,
                        );
                        return v___x_5462_;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5393_);
                    crate::leanh::lean_dec(v_a_5380_);
                    crate::leanh::lean_dec_ref(v_kp_5368_);
                    crate::leanh::lean_dec_ref(v_goal_5366_);
                    crate::leanh::lean_dec_ref(v_mkTac_5365_);
                    v_a_5463_ = crate::leanh::lean_ctor_get(v___x_5397_, 0);
                    v_isSharedCheck_5470_ = (!crate::leanh::lean_is_exclusive(v___x_5397_)) as u8;
                    if v_isSharedCheck_5470_ == 0 {
                        v___x_5465_ = v___x_5397_;
                        v_isShared_5466_ = v_isSharedCheck_5470_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5463_);
                        crate::leanh::lean_dec(v___x_5397_);
                        v___x_5465_ = crate::leanh::lean_box(0);
                        v_isShared_5466_ = v_isSharedCheck_5470_;
                        state = 15;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5413_ = (crate::leanh::lean_unbox(v_a_5409_) as u8);
                crate::leanh::lean_dec(v_a_5409_);
                if v___x_5413_ == 0 {
                    crate::leanh::lean_inc(v_seq_5407_);
                    crate::leanh::lean_del_object(v___x_5411_);
                    v_isSharedCheck_5440_ = (!crate::leanh::lean_is_exclusive(v_a_5406_)) as u8;
                    if v_isSharedCheck_5440_ == 0 {
                        v_unused_5441_ = crate::leanh::lean_ctor_get(v_a_5406_, 0);
                        crate::leanh::lean_dec(v_unused_5441_);
                        v___x_5415_ = v_a_5406_;
                        v_isShared_5416_ = v_isSharedCheck_5440_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_a_5406_);
                        v___x_5415_ = crate::leanh::lean_box(0);
                        v_isShared_5416_ = v_isSharedCheck_5440_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5393_);
                    crate::leanh::lean_dec_ref(v_mkTac_5365_);
                    if v_isShared_5412_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5411_, 0, v_a_5406_);
                        v___x_5443_ = v___x_5411_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_5444_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5444_, 0, v_a_5406_);
                        v___x_5443_ = v_reuseFailAlloc_5444_;
                        state = 10;
                        continue;
                    }
                }
            }
            3 => {
                crate::leanh::lean_inc(v_a_5377_);
                crate::leanh::lean_inc_ref(v_a_5376_);
                crate::leanh::lean_inc(v_a_5375_);
                crate::leanh::lean_inc_ref(v_a_5374_);
                crate::leanh::lean_inc(v_a_5373_);
                crate::leanh::lean_inc_ref(v_a_5372_);
                crate::leanh::lean_inc(v_a_5371_);
                crate::leanh::lean_inc_ref(v_a_5370_);
                crate::leanh::lean_inc(v_a_5369_);
                v___x_5417_ = crate::leanh::lean_apply_10(
                    v_mkTac_5365_,
                    v_a_5369_,
                    v_a_5370_,
                    v_a_5371_,
                    v_a_5372_,
                    v_a_5373_,
                    v_a_5374_,
                    v_a_5375_,
                    v_a_5376_,
                    v_a_5377_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_5417_) == 0 {
                    v_a_5418_ = crate::leanh::lean_ctor_get(v___x_5417_, 0);
                    v_isSharedCheck_5431_ = (!crate::leanh::lean_is_exclusive(v___x_5417_)) as u8;
                    if v_isSharedCheck_5431_ == 0 {
                        v___x_5420_ = v___x_5417_;
                        v_isShared_5421_ = v_isSharedCheck_5431_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5418_);
                        crate::leanh::lean_dec(v___x_5417_);
                        v___x_5420_ = crate::leanh::lean_box(0);
                        v_isShared_5421_ = v_isSharedCheck_5431_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5415_);
                    crate::leanh::lean_dec(v_seq_5407_);
                    crate::leanh::lean_del_object(v___x_5393_);
                    v_a_5432_ = crate::leanh::lean_ctor_get(v___x_5417_, 0);
                    v_isSharedCheck_5439_ = (!crate::leanh::lean_is_exclusive(v___x_5417_)) as u8;
                    if v_isSharedCheck_5439_ == 0 {
                        v___x_5434_ = v___x_5417_;
                        v_isShared_5435_ = v_isSharedCheck_5439_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5432_);
                        crate::leanh::lean_dec(v___x_5417_);
                        v___x_5434_ = crate::leanh::lean_box(0);
                        v_isShared_5435_ = v_isSharedCheck_5439_;
                        state = 8;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_5394_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5393_, 1);
                    crate::leanh::lean_ctor_set(v___x_5393_, 1, v_seq_5407_);
                    crate::leanh::lean_ctor_set(v___x_5393_, 0, v_a_5418_);
                    v___x_5423_ = v___x_5393_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5430_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5430_, 0, v_a_5418_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5430_, 1, v_seq_5407_);
                    v___x_5423_ = v_reuseFailAlloc_5430_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_5416_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5415_, 0, v___x_5423_);
                    v___x_5425_ = v___x_5415_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5429_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5429_, 0, v___x_5423_);
                    v___x_5425_ = v_reuseFailAlloc_5429_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_5421_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5420_, 0, v___x_5425_);
                    v___x_5427_ = v___x_5420_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5428_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5428_, 0, v___x_5425_);
                    v___x_5427_ = v_reuseFailAlloc_5428_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5427_;
            }
            8 => {
                if v_isShared_5435_ == 0 {
                    v___x_5437_ = v___x_5434_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5438_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5438_, 0, v_a_5432_);
                    v___x_5437_ = v_reuseFailAlloc_5438_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5437_;
            }
            10 => {
                return v___x_5443_;
            }
            11 => {
                if v_isShared_5449_ == 0 {
                    v___x_5451_ = v___x_5448_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5452_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5452_, 0, v_a_5446_);
                    v___x_5451_ = v_reuseFailAlloc_5452_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5451_;
            }
            13 => {
                if v_isShared_5457_ == 0 {
                    v___x_5459_ = v___x_5456_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5460_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5460_, 0, v_a_5454_);
                    v___x_5459_ = v_reuseFailAlloc_5460_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_5459_;
            }
            15 => {
                if v_isShared_5466_ == 0 {
                    v___x_5468_ = v___x_5465_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_5469_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5469_, 0, v_a_5463_);
                    v___x_5468_ = v_reuseFailAlloc_5469_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_5468_;
            }
            17 => {
                if v_isShared_5477_ == 0 {
                    v___x_5479_ = v___x_5476_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_5480_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5480_, 0, v_a_5474_);
                    v___x_5479_ = v_reuseFailAlloc_5480_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_5479_;
            }
            19 => {
                if v_isShared_5485_ == 0 {
                    v___x_5487_ = v___x_5484_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_5488_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5488_, 0, v_a_5482_);
                    v___x_5487_ = v_reuseFailAlloc_5488_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_5487_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Action_solverAction___boxed(
    mut v_check_5490_: *mut crate::leanh::LeanObject,
    mut v_mkTac_5491_: *mut crate::leanh::LeanObject,
    mut v_goal_5492_: *mut crate::leanh::LeanObject,
    mut v_kna_5493_: *mut crate::leanh::LeanObject,
    mut v_kp_5494_: *mut crate::leanh::LeanObject,
    mut v_a_5495_: *mut crate::leanh::LeanObject,
    mut v_a_5496_: *mut crate::leanh::LeanObject,
    mut v_a_5497_: *mut crate::leanh::LeanObject,
    mut v_a_5498_: *mut crate::leanh::LeanObject,
    mut v_a_5499_: *mut crate::leanh::LeanObject,
    mut v_a_5500_: *mut crate::leanh::LeanObject,
    mut v_a_5501_: *mut crate::leanh::LeanObject,
    mut v_a_5502_: *mut crate::leanh::LeanObject,
    mut v_a_5503_: *mut crate::leanh::LeanObject,
    mut v_a_5504_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5505_ = l_Lean_Meta_Grind_Action_solverAction(
        v_check_5490_,
        v_mkTac_5491_,
        v_goal_5492_,
        v_kna_5493_,
        v_kp_5494_,
        v_a_5495_,
        v_a_5496_,
        v_a_5497_,
        v_a_5498_,
        v_a_5499_,
        v_a_5500_,
        v_a_5501_,
        v_a_5502_,
        v_a_5503_,
    );
    crate::leanh::lean_dec(v_a_5503_);
    crate::leanh::lean_dec_ref(v_a_5502_);
    crate::leanh::lean_dec(v_a_5501_);
    crate::leanh::lean_dec_ref(v_a_5500_);
    crate::leanh::lean_dec(v_a_5499_);
    crate::leanh::lean_dec_ref(v_a_5498_);
    crate::leanh::lean_dec(v_a_5497_);
    crate::leanh::lean_dec_ref(v_a_5496_);
    crate::leanh::lean_dec(v_a_5495_);
    return v_res_5505_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_mbtc___lam__0(
    mut v_goal_5506_: *mut crate::leanh::LeanObject,
    mut v___y_5507_: *mut crate::leanh::LeanObject,
    mut v___y_5508_: *mut crate::leanh::LeanObject,
    mut v___y_5509_: *mut crate::leanh::LeanObject,
    mut v___y_5510_: *mut crate::leanh::LeanObject,
    mut v___y_5511_: *mut crate::leanh::LeanObject,
    mut v___y_5512_: *mut crate::leanh::LeanObject,
    mut v___y_5513_: *mut crate::leanh::LeanObject,
    mut v___y_5514_: *mut crate::leanh::LeanObject,
    mut v___y_5515_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5522_: u8 = 0;
    let mut v___x_5523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5528_: u8 = 0;
    let mut v_a_5529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5532_: u8 = 0;
    let mut v___x_5534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5536_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5517_ = lean_st_mk_ref(v_goal_5506_);
                v___x_5518_ = l_Lean_Meta_Grind_Solvers_mbtc(
                    v___x_5517_,
                    v___y_5507_,
                    v___y_5508_,
                    v___y_5509_,
                    v___y_5510_,
                    v___y_5511_,
                    v___y_5512_,
                    v___y_5513_,
                    v___y_5514_,
                    v___y_5515_,
                );
                if crate::leanh::lean_obj_tag(v___x_5518_) == 0 {
                    v_a_5519_ = crate::leanh::lean_ctor_get(v___x_5518_, 0);
                    v_isSharedCheck_5528_ = (!crate::leanh::lean_is_exclusive(v___x_5518_)) as u8;
                    if v_isSharedCheck_5528_ == 0 {
                        v___x_5521_ = v___x_5518_;
                        v_isShared_5522_ = v_isSharedCheck_5528_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5519_);
                        crate::leanh::lean_dec(v___x_5518_);
                        v___x_5521_ = crate::leanh::lean_box(0);
                        v_isShared_5522_ = v_isSharedCheck_5528_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5517_);
                    v_a_5529_ = crate::leanh::lean_ctor_get(v___x_5518_, 0);
                    v_isSharedCheck_5536_ = (!crate::leanh::lean_is_exclusive(v___x_5518_)) as u8;
                    if v_isSharedCheck_5536_ == 0 {
                        v___x_5531_ = v___x_5518_;
                        v_isShared_5532_ = v_isSharedCheck_5536_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5529_);
                        crate::leanh::lean_dec(v___x_5518_);
                        v___x_5531_ = crate::leanh::lean_box(0);
                        v_isShared_5532_ = v_isSharedCheck_5536_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5523_ = lean_st_ref_get(v___x_5517_);
                crate::leanh::lean_dec(v___x_5517_);
                v___x_5524_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5524_, 0, v_a_5519_);
                crate::leanh::lean_ctor_set(v___x_5524_, 1, v___x_5523_);
                if v_isShared_5522_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5521_, 0, v___x_5524_);
                    v___x_5526_ = v___x_5521_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5527_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5527_, 0, v___x_5524_);
                    v___x_5526_ = v_reuseFailAlloc_5527_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5526_;
            }
            3 => {
                if v_isShared_5532_ == 0 {
                    v___x_5534_ = v___x_5531_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5535_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5535_, 0, v_a_5529_);
                    v___x_5534_ = v_reuseFailAlloc_5535_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5534_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Action_mbtc___lam__0___boxed(
    mut v_goal_5537_: *mut crate::leanh::LeanObject,
    mut v___y_5538_: *mut crate::leanh::LeanObject,
    mut v___y_5539_: *mut crate::leanh::LeanObject,
    mut v___y_5540_: *mut crate::leanh::LeanObject,
    mut v___y_5541_: *mut crate::leanh::LeanObject,
    mut v___y_5542_: *mut crate::leanh::LeanObject,
    mut v___y_5543_: *mut crate::leanh::LeanObject,
    mut v___y_5544_: *mut crate::leanh::LeanObject,
    mut v___y_5545_: *mut crate::leanh::LeanObject,
    mut v___y_5546_: *mut crate::leanh::LeanObject,
    mut v___y_5547_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5548_ = l_Lean_Meta_Grind_Action_mbtc___lam__0(
        v_goal_5537_,
        v___y_5538_,
        v___y_5539_,
        v___y_5540_,
        v___y_5541_,
        v___y_5542_,
        v___y_5543_,
        v___y_5544_,
        v___y_5545_,
        v___y_5546_,
    );
    crate::leanh::lean_dec(v___y_5546_);
    crate::leanh::lean_dec_ref(v___y_5545_);
    crate::leanh::lean_dec(v___y_5544_);
    crate::leanh::lean_dec_ref(v___y_5543_);
    crate::leanh::lean_dec(v___y_5542_);
    crate::leanh::lean_dec_ref(v___y_5541_);
    crate::leanh::lean_dec(v___y_5540_);
    crate::leanh::lean_dec_ref(v___y_5539_);
    crate::leanh::lean_dec(v___y_5538_);
    return v_res_5548_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_mbtc(
    mut v_goal_5556_: *mut crate::leanh::LeanObject,
    mut v_kna_5557_: *mut crate::leanh::LeanObject,
    mut v_kp_5558_: *mut crate::leanh::LeanObject,
    mut v_a_5559_: *mut crate::leanh::LeanObject,
    mut v_a_5560_: *mut crate::leanh::LeanObject,
    mut v_a_5561_: *mut crate::leanh::LeanObject,
    mut v_a_5562_: *mut crate::leanh::LeanObject,
    mut v_a_5563_: *mut crate::leanh::LeanObject,
    mut v_a_5564_: *mut crate::leanh::LeanObject,
    mut v_a_5565_: *mut crate::leanh::LeanObject,
    mut v_a_5566_: *mut crate::leanh::LeanObject,
    mut v_a_5567_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_5571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5576_: u8 = 0;
    let mut v_snd_5577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5582_: u8 = 0;
    let mut v___x_5583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trace_5585_: u8 = 0;
    let mut v___x_5586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_seq_5589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5594_: u8 = 0;
    let mut v___x_5595_: u8 = 0;
    let mut v___x_5597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5598_: u8 = 0;
    let mut v_ref_5599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5600_: u8 = 0;
    let mut v___x_5601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5615_: u8 = 0;
    let mut v_unused_5616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5620_: u8 = 0;
    let mut v_a_5621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5624_: u8 = 0;
    let mut v___x_5626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5628_: u8 = 0;
    let mut v_a_5629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5632_: u8 = 0;
    let mut v___x_5634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5636_: u8 = 0;
    let mut v_isSharedCheck_5637_: u8 = 0;
    let mut v_unused_5638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5642_: u8 = 0;
    let mut v___x_5644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5646_: u8 = 0;
    let mut v_a_5647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5650_: u8 = 0;
    let mut v___x_5652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5654_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5569_ = l_Lean_Meta_Grind_Action_saveStateIfTracing___redArg(
                    v_a_5560_, v_a_5561_, v_a_5565_, v_a_5567_,
                );
                if crate::leanh::lean_obj_tag(v___x_5569_) == 0 {
                    v_a_5570_ = crate::leanh::lean_ctor_get(v___x_5569_, 0);
                    crate::leanh::lean_inc(v_a_5570_);
                    crate::leanh::lean_dec_ref_known(v___x_5569_, 1);
                    v_mvarId_5571_ = crate::leanh::lean_ctor_get(v_goal_5556_, 1);
                    crate::leanh::lean_inc_ref(v_goal_5556_);
                    v___f_5572_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Meta_Grind_Action_mbtc___lam__0___boxed as *mut core::ffi::c_void,
                        11,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_5572_, 0, v_goal_5556_);
                    crate::leanh::lean_inc(v_mvarId_5571_);
                    v___x_5573_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg(v_mvarId_5571_, v___f_5572_, v_a_5559_, v_a_5560_, v_a_5561_, v_a_5562_, v_a_5563_, v_a_5564_, v_a_5565_, v_a_5566_, v_a_5567_);
                    if crate::leanh::lean_obj_tag(v___x_5573_) == 0 {
                        v_a_5574_ = crate::leanh::lean_ctor_get(v___x_5573_, 0);
                        crate::leanh::lean_inc(v_a_5574_);
                        crate::leanh::lean_dec_ref_known(v___x_5573_, 1);
                        v_fst_5575_ = crate::leanh::lean_ctor_get(v_a_5574_, 0);
                        v___x_5576_ = (crate::leanh::lean_unbox(v_fst_5575_) as u8);
                        if v___x_5576_ == 0 {
                            crate::leanh::lean_dec(v_a_5570_);
                            crate::leanh::lean_dec_ref(v_kp_5558_);
                            crate::leanh::lean_dec_ref(v_goal_5556_);
                            v_snd_5577_ = crate::leanh::lean_ctor_get(v_a_5574_, 1);
                            crate::leanh::lean_inc(v_snd_5577_);
                            crate::leanh::lean_dec(v_a_5574_);
                            crate::leanh::lean_inc(v_a_5567_);
                            crate::leanh::lean_inc_ref(v_a_5566_);
                            crate::leanh::lean_inc(v_a_5565_);
                            crate::leanh::lean_inc_ref(v_a_5564_);
                            crate::leanh::lean_inc(v_a_5563_);
                            crate::leanh::lean_inc_ref(v_a_5562_);
                            crate::leanh::lean_inc(v_a_5561_);
                            crate::leanh::lean_inc_ref(v_a_5560_);
                            crate::leanh::lean_inc(v_a_5559_);
                            v___x_5578_ = crate::leanh::lean_apply_11(
                                v_kna_5557_,
                                v_snd_5577_,
                                v_a_5559_,
                                v_a_5560_,
                                v_a_5561_,
                                v_a_5562_,
                                v_a_5563_,
                                v_a_5564_,
                                v_a_5565_,
                                v_a_5566_,
                                v_a_5567_,
                                crate::leanh::lean_box(0),
                            );
                            return v___x_5578_;
                        } else {
                            crate::leanh::lean_dec_ref(v_kna_5557_);
                            v_snd_5579_ = crate::leanh::lean_ctor_get(v_a_5574_, 1);
                            v_isSharedCheck_5637_ =
                                (!crate::leanh::lean_is_exclusive(v_a_5574_)) as u8;
                            if v_isSharedCheck_5637_ == 0 {
                                v_unused_5638_ = crate::leanh::lean_ctor_get(v_a_5574_, 0);
                                crate::leanh::lean_dec(v_unused_5638_);
                                v___x_5581_ = v_a_5574_;
                                v_isShared_5582_ = v_isSharedCheck_5637_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_snd_5579_);
                                crate::leanh::lean_dec(v_a_5574_);
                                v___x_5581_ = crate::leanh::lean_box(0);
                                v_isShared_5582_ = v_isSharedCheck_5637_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_5570_);
                        crate::leanh::lean_dec_ref(v_kp_5558_);
                        crate::leanh::lean_dec_ref(v_kna_5557_);
                        crate::leanh::lean_dec_ref(v_goal_5556_);
                        v_a_5639_ = crate::leanh::lean_ctor_get(v___x_5573_, 0);
                        v_isSharedCheck_5646_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5573_)) as u8;
                        if v_isSharedCheck_5646_ == 0 {
                            v___x_5641_ = v___x_5573_;
                            v_isShared_5642_ = v_isSharedCheck_5646_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5639_);
                            crate::leanh::lean_dec(v___x_5573_);
                            v___x_5641_ = crate::leanh::lean_box(0);
                            v_isShared_5642_ = v_isSharedCheck_5646_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_kp_5558_);
                    crate::leanh::lean_dec_ref(v_kna_5557_);
                    crate::leanh::lean_dec_ref(v_goal_5556_);
                    v_a_5647_ = crate::leanh::lean_ctor_get(v___x_5569_, 0);
                    v_isSharedCheck_5654_ = (!crate::leanh::lean_is_exclusive(v___x_5569_)) as u8;
                    if v_isSharedCheck_5654_ == 0 {
                        v___x_5649_ = v___x_5569_;
                        v_isShared_5650_ = v_isSharedCheck_5654_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5647_);
                        crate::leanh::lean_dec(v___x_5569_);
                        v___x_5649_ = crate::leanh::lean_box(0);
                        v_isShared_5650_ = v_isSharedCheck_5654_;
                        state = 14;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5583_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_5560_);
                if crate::leanh::lean_obj_tag(v___x_5583_) == 0 {
                    v_a_5584_ = crate::leanh::lean_ctor_get(v___x_5583_, 0);
                    crate::leanh::lean_inc(v_a_5584_);
                    crate::leanh::lean_dec_ref_known(v___x_5583_, 1);
                    v_trace_5585_ = crate::leanh::lean_ctor_get_uint8(
                        v_a_5584_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13) as u32,
                    );
                    crate::leanh::lean_dec(v_a_5584_);
                    if v_trace_5585_ == 0 {
                        crate::leanh::lean_del_object(v___x_5581_);
                        crate::leanh::lean_dec(v_a_5570_);
                        crate::leanh::lean_dec_ref(v_goal_5556_);
                        crate::leanh::lean_inc(v_a_5567_);
                        crate::leanh::lean_inc_ref(v_a_5566_);
                        crate::leanh::lean_inc(v_a_5565_);
                        crate::leanh::lean_inc_ref(v_a_5564_);
                        crate::leanh::lean_inc(v_a_5563_);
                        crate::leanh::lean_inc_ref(v_a_5562_);
                        crate::leanh::lean_inc(v_a_5561_);
                        crate::leanh::lean_inc_ref(v_a_5560_);
                        crate::leanh::lean_inc(v_a_5559_);
                        v___x_5586_ = crate::leanh::lean_apply_11(
                            v_kp_5558_,
                            v_snd_5579_,
                            v_a_5559_,
                            v_a_5560_,
                            v_a_5561_,
                            v_a_5562_,
                            v_a_5563_,
                            v_a_5564_,
                            v_a_5565_,
                            v_a_5566_,
                            v_a_5567_,
                            crate::leanh::lean_box(0),
                        );
                        return v___x_5586_;
                    } else {
                        crate::leanh::lean_inc(v_a_5567_);
                        crate::leanh::lean_inc_ref(v_a_5566_);
                        crate::leanh::lean_inc(v_a_5565_);
                        crate::leanh::lean_inc_ref(v_a_5564_);
                        crate::leanh::lean_inc(v_a_5563_);
                        crate::leanh::lean_inc_ref(v_a_5562_);
                        crate::leanh::lean_inc(v_a_5561_);
                        crate::leanh::lean_inc_ref(v_a_5560_);
                        crate::leanh::lean_inc(v_a_5559_);
                        v___x_5587_ = crate::leanh::lean_apply_11(
                            v_kp_5558_,
                            v_snd_5579_,
                            v_a_5559_,
                            v_a_5560_,
                            v_a_5561_,
                            v_a_5562_,
                            v_a_5563_,
                            v_a_5564_,
                            v_a_5565_,
                            v_a_5566_,
                            v_a_5567_,
                            crate::leanh::lean_box(0),
                        );
                        if crate::leanh::lean_obj_tag(v___x_5587_) == 0 {
                            v_a_5588_ = crate::leanh::lean_ctor_get(v___x_5587_, 0);
                            crate::leanh::lean_inc(v_a_5588_);
                            if crate::leanh::lean_obj_tag(v_a_5588_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_5587_, 1);
                                v_seq_5589_ = crate::leanh::lean_ctor_get(v_a_5588_, 0);
                                crate::leanh::lean_inc(v_seq_5589_);
                                v___x_5590_ = l_Lean_Meta_Grind_Action_checkSeqAt(
                                    v_a_5570_,
                                    v_goal_5556_,
                                    v_seq_5589_,
                                    v_a_5559_,
                                    v_a_5560_,
                                    v_a_5561_,
                                    v_a_5562_,
                                    v_a_5563_,
                                    v_a_5564_,
                                    v_a_5565_,
                                    v_a_5566_,
                                    v_a_5567_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_5590_) == 0 {
                                    v_a_5591_ = crate::leanh::lean_ctor_get(v___x_5590_, 0);
                                    v_isSharedCheck_5620_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_5590_)) as u8;
                                    if v_isSharedCheck_5620_ == 0 {
                                        v___x_5593_ = v___x_5590_;
                                        v_isShared_5594_ = v_isSharedCheck_5620_;
                                        state = 2;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_5591_);
                                        crate::leanh::lean_dec(v___x_5590_);
                                        v___x_5593_ = crate::leanh::lean_box(0);
                                        v_isShared_5594_ = v_isSharedCheck_5620_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref_known(v_a_5588_, 1);
                                    crate::leanh::lean_del_object(v___x_5581_);
                                    v_a_5621_ = crate::leanh::lean_ctor_get(v___x_5590_, 0);
                                    v_isSharedCheck_5628_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_5590_)) as u8;
                                    if v_isSharedCheck_5628_ == 0 {
                                        v___x_5623_ = v___x_5590_;
                                        v_isShared_5624_ = v_isSharedCheck_5628_;
                                        state = 8;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_5621_);
                                        crate::leanh::lean_dec(v___x_5590_);
                                        v___x_5623_ = crate::leanh::lean_box(0);
                                        v_isShared_5624_ = v_isSharedCheck_5628_;
                                        state = 8;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_5588_);
                                crate::leanh::lean_del_object(v___x_5581_);
                                crate::leanh::lean_dec(v_a_5570_);
                                crate::leanh::lean_dec_ref(v_goal_5556_);
                                return v___x_5587_;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_5581_);
                            crate::leanh::lean_dec(v_a_5570_);
                            crate::leanh::lean_dec_ref(v_goal_5556_);
                            return v___x_5587_;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5581_);
                    crate::leanh::lean_dec(v_snd_5579_);
                    crate::leanh::lean_dec(v_a_5570_);
                    crate::leanh::lean_dec_ref(v_kp_5558_);
                    crate::leanh::lean_dec_ref(v_goal_5556_);
                    v_a_5629_ = crate::leanh::lean_ctor_get(v___x_5583_, 0);
                    v_isSharedCheck_5636_ = (!crate::leanh::lean_is_exclusive(v___x_5583_)) as u8;
                    if v_isSharedCheck_5636_ == 0 {
                        v___x_5631_ = v___x_5583_;
                        v_isShared_5632_ = v_isSharedCheck_5636_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5629_);
                        crate::leanh::lean_dec(v___x_5583_);
                        v___x_5631_ = crate::leanh::lean_box(0);
                        v_isShared_5632_ = v_isSharedCheck_5636_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5595_ = (crate::leanh::lean_unbox(v_a_5591_) as u8);
                if v___x_5595_ == 0 {
                    crate::leanh::lean_inc(v_seq_5589_);
                    v_isSharedCheck_5615_ = (!crate::leanh::lean_is_exclusive(v_a_5588_)) as u8;
                    if v_isSharedCheck_5615_ == 0 {
                        v_unused_5616_ = crate::leanh::lean_ctor_get(v_a_5588_, 0);
                        crate::leanh::lean_dec(v_unused_5616_);
                        v___x_5597_ = v_a_5588_;
                        v_isShared_5598_ = v_isSharedCheck_5615_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_a_5588_);
                        v___x_5597_ = crate::leanh::lean_box(0);
                        v_isShared_5598_ = v_isSharedCheck_5615_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5591_);
                    crate::leanh::lean_del_object(v___x_5581_);
                    if v_isShared_5594_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5593_, 0, v_a_5588_);
                        v___x_5618_ = v___x_5593_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_5619_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5619_, 0, v_a_5588_);
                        v___x_5618_ = v_reuseFailAlloc_5619_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                v_ref_5599_ = crate::leanh::lean_ctor_get(v_a_5566_, 5);
                v___x_5600_ = (crate::leanh::lean_unbox(v_a_5591_) as u8);
                crate::leanh::lean_dec(v_a_5591_);
                v___x_5601_ = l_Lean_SourceInfo_fromRef(v_ref_5599_, v___x_5600_);
                v___x_5602_ = l_Lean_Meta_Grind_Action_mbtc___closed__0;
                v___x_5603_ = l_Lean_Meta_Grind_Action_mbtc___closed__1;
                crate::leanh::lean_inc(v___x_5601_);
                if v_isShared_5582_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5581_, 2);
                    crate::leanh::lean_ctor_set(v___x_5581_, 1, v___x_5602_);
                    crate::leanh::lean_ctor_set(v___x_5581_, 0, v___x_5601_);
                    v___x_5605_ = v___x_5581_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5614_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5614_, 0, v___x_5601_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5614_, 1, v___x_5602_);
                    v___x_5605_ = v_reuseFailAlloc_5614_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5606_ = l_Lean_Syntax_node1(v___x_5601_, v___x_5603_, v___x_5605_);
                v___x_5607_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5607_, 0, v___x_5606_);
                crate::leanh::lean_ctor_set(v___x_5607_, 1, v_seq_5589_);
                if v_isShared_5598_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5597_, 0, v___x_5607_);
                    v___x_5609_ = v___x_5597_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5613_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5613_, 0, v___x_5607_);
                    v___x_5609_ = v_reuseFailAlloc_5613_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_5594_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5593_, 0, v___x_5609_);
                    v___x_5611_ = v___x_5593_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5612_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5612_, 0, v___x_5609_);
                    v___x_5611_ = v_reuseFailAlloc_5612_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5611_;
            }
            7 => {
                return v___x_5618_;
            }
            8 => {
                if v_isShared_5624_ == 0 {
                    v___x_5626_ = v___x_5623_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5627_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5627_, 0, v_a_5621_);
                    v___x_5626_ = v_reuseFailAlloc_5627_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5626_;
            }
            10 => {
                if v_isShared_5632_ == 0 {
                    v___x_5634_ = v___x_5631_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5635_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5635_, 0, v_a_5629_);
                    v___x_5634_ = v_reuseFailAlloc_5635_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_5634_;
            }
            12 => {
                if v_isShared_5642_ == 0 {
                    v___x_5644_ = v___x_5641_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5645_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5645_, 0, v_a_5639_);
                    v___x_5644_ = v_reuseFailAlloc_5645_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_5644_;
            }
            14 => {
                if v_isShared_5650_ == 0 {
                    v___x_5652_ = v___x_5649_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_5653_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5653_, 0, v_a_5647_);
                    v___x_5652_ = v_reuseFailAlloc_5653_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_5652_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Action_mbtc___boxed(
    mut v_goal_5655_: *mut crate::leanh::LeanObject,
    mut v_kna_5656_: *mut crate::leanh::LeanObject,
    mut v_kp_5657_: *mut crate::leanh::LeanObject,
    mut v_a_5658_: *mut crate::leanh::LeanObject,
    mut v_a_5659_: *mut crate::leanh::LeanObject,
    mut v_a_5660_: *mut crate::leanh::LeanObject,
    mut v_a_5661_: *mut crate::leanh::LeanObject,
    mut v_a_5662_: *mut crate::leanh::LeanObject,
    mut v_a_5663_: *mut crate::leanh::LeanObject,
    mut v_a_5664_: *mut crate::leanh::LeanObject,
    mut v_a_5665_: *mut crate::leanh::LeanObject,
    mut v_a_5666_: *mut crate::leanh::LeanObject,
    mut v_a_5667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5668_ = l_Lean_Meta_Grind_Action_mbtc(
        v_goal_5655_,
        v_kna_5656_,
        v_kp_5657_,
        v_a_5658_,
        v_a_5659_,
        v_a_5660_,
        v_a_5661_,
        v_a_5662_,
        v_a_5663_,
        v_a_5664_,
        v_a_5665_,
        v_a_5666_,
    );
    crate::leanh::lean_dec(v_a_5666_);
    crate::leanh::lean_dec_ref(v_a_5665_);
    crate::leanh::lean_dec(v_a_5664_);
    crate::leanh::lean_dec_ref(v_a_5663_);
    crate::leanh::lean_dec(v_a_5662_);
    crate::leanh::lean_dec_ref(v_a_5661_);
    crate::leanh::lean_dec(v_a_5660_);
    crate::leanh::lean_dec_ref(v_a_5659_);
    crate::leanh::lean_dec(v_a_5658_);
    return v_res_5668_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_loop_match__1_splitter___redArg(
    mut v_n_5669_: *mut crate::leanh::LeanObject,
    mut v_h__1_5670_: *mut crate::leanh::LeanObject,
    mut v_h__2_5671_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_5672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_5673_: u8 = 0;
    v_zero_5672_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_5673_ = lean_nat_dec_eq(v_n_5669_, v_zero_5672_);
    if v_isZero_5673_ == 1 {
        let mut v___x_5674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_5671_);
        v___x_5674_ = crate::leanh::lean_box(0);
        v___x_5675_ = crate::leanh::lean_apply_1(v_h__1_5670_, v___x_5674_);
        return v___x_5675_;
    } else {
        let mut v_one_5676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_5677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_5670_);
        v_one_5676_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_5677_ = lean_nat_sub(v_n_5669_, v_one_5676_);
        v___x_5678_ = crate::leanh::lean_apply_1(v_h__2_5671_, v_n_5677_);
        return v___x_5678_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_loop_match__1_splitter___redArg___boxed(
    mut v_n_5679_: *mut crate::leanh::LeanObject,
    mut v_h__1_5680_: *mut crate::leanh::LeanObject,
    mut v_h__2_5681_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5682_ = l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_loop_match__1_splitter___redArg(v_n_5679_, v_h__1_5680_, v_h__2_5681_);
    crate::leanh::lean_dec(v_n_5679_);
    return v_res_5682_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_loop_match__1_splitter(
    mut v_motive_5683_: *mut crate::leanh::LeanObject,
    mut v_n_5684_: *mut crate::leanh::LeanObject,
    mut v_h__1_5685_: *mut crate::leanh::LeanObject,
    mut v_h__2_5686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_5687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_5688_: u8 = 0;
    v_zero_5687_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_5688_ = lean_nat_dec_eq(v_n_5684_, v_zero_5687_);
    if v_isZero_5688_ == 1 {
        let mut v___x_5689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_5686_);
        v___x_5689_ = crate::leanh::lean_box(0);
        v___x_5690_ = crate::leanh::lean_apply_1(v_h__1_5685_, v___x_5689_);
        return v___x_5690_;
    } else {
        let mut v_one_5691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_5692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_5685_);
        v_one_5691_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_5692_ = lean_nat_sub(v_n_5684_, v_one_5691_);
        v___x_5693_ = crate::leanh::lean_apply_1(v_h__2_5686_, v_n_5692_);
        return v___x_5693_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_loop_match__1_splitter___boxed(
    mut v_motive_5694_: *mut crate::leanh::LeanObject,
    mut v_n_5695_: *mut crate::leanh::LeanObject,
    mut v_h__1_5696_: *mut crate::leanh::LeanObject,
    mut v_h__2_5697_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5698_ =
        l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_loop_match__1_splitter(
            v_motive_5694_,
            v_n_5695_,
            v_h__1_5696_,
            v_h__2_5697_,
        );
    crate::leanh::lean_dec(v_n_5695_);
    return v_res_5698_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Action(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Action(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Action(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Action(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Action(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Action(builtin);
}
