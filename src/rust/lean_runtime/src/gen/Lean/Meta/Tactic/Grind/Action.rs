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
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr5, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg,
    l_Lean_Syntax_getArgs, l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f,
    l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull, l_Lean_Syntax_node1, l_Lean_Syntax_node2,
    l_Lean_Syntax_node3, l_Lean_replaceRef,
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
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_mk, lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity,
    lean_nat_dec_eq, lean_nat_sub, lean_string_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Meta::Tactic::Grind::Types::lean_grind_process_new_facts;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_10, lean_apply_11, lean_apply_13, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref,
    lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
pub static l_Lean_Meta_Grind_ActionResult_toMessageData___closed__0_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_ActionResult_toMessageData___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_ActionResult_toMessageData___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_ActionResult_toMessageData___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_ActionResult_toMessageData___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_ActionResult_toMessageData___closed__2_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_ActionResult_toMessageData___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_ActionResult_toMessageData___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_ActionResult_toMessageData___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_ActionResult_toMessageData___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_instToMessageDataActionResult___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Meta_Grind_ActionResult_toMessageData as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Grind_instToMessageDataActionResult___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instToMessageDataActionResult___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Meta_Grind_instToMessageDataActionResult: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instToMessageDataActionResult___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Action_done___redArg___closed__0_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lean_Meta_Grind_Action_done___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_done___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Action_instAndThen___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Meta_Grind_Action_instAndThen___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 15,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Grind_Action_instAndThen___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_instAndThen___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Meta_Grind_Action_instAndThen: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_instAndThen___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Action_instOrElse___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Meta_Grind_Action_instOrElse___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 15,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Grind_Action_instOrElse___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_instOrElse___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Meta_Grind_Action_instOrElse: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_instOrElse___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Action_run___lam__0___closed__0_value: LeanStringObject<5> =
    LeanStringObject {
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
static mut l_Lean_Meta_Grind_Action_run___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Action_run___lam__0___closed__1_value: LeanStringObject<7> =
    LeanStringObject {
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
static mut l_Lean_Meta_Grind_Action_run___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Action_run___lam__0___closed__2_value: LeanStringObject<7> =
    LeanStringObject {
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
static mut l_Lean_Meta_Grind_Action_run___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__2_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Action_run___lam__0___closed__3_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_Action_run___lam__0___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__3_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Action_run___lam__0___closed__4_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_Action_run___lam__0___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__4_value) as *mut LeanObject;
static l_Lean_Meta_Grind_Action_run___lam__0___closed__5_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Action_run___lam__0___closed__5_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__5_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Action_run___lam__0___closed__5_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__5_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Action_run___lam__0___closed__5_value_aux_3: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__5_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__3_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Action_run___lam__0___closed__5_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__5_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__4_value)
                as *mut LeanObject,
            12610174047474239361 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Action_run___lam__0___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__5_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Action_run___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Meta_Grind_Action_run___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 11,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Grind_Action_run___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Action_mkGrindStep___closed__0_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_Action_mkGrindStep___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindStep___closed__0_value) as *mut LeanObject;
static l_Lean_Meta_Grind_Action_mkGrindStep___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Action_mkGrindStep___closed__1_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindStep___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Action_mkGrindStep___closed__1_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindStep___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Action_mkGrindStep___closed__1_value_aux_3: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindStep___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__3_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Action_mkGrindStep___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindStep___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindStep___closed__0_value)
                as *mut LeanObject,
            6321866296242073541 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Action_mkGrindStep___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindStep___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Action_mkGrindStep___closed__2_value: LeanArrayObject<0> =
    LeanArrayObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Meta_Grind_Action_mkGrindStep___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindStep___closed__2_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Action_mkGrindStep___closed__3_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_Action_mkGrindStep___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindStep___closed__3_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Action_mkGrindStep___closed__4_value: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindStep___closed__3_value)
                as *mut LeanObject,
            9855511589286918680 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Action_mkGrindStep___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindStep___closed__4_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Action_mkGrindStep___closed__5_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 1,
        },
        m_objs: [
            (((2 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindStep___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindStep___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Action_mkGrindStep___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindStep___closed__5_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Action_mkGrindSeq___closed__0_value: LeanArrayObject<0> =
    LeanArrayObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Meta_Grind_Action_mkGrindSeq___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Action_mkGrindSeq___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 1,
        },
        m_objs: [
            (((2 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindStep___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Action_mkGrindSeq___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Action_mkGrindSeq___closed__2_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_Action_mkGrindSeq___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__2_value) as *mut LeanObject;
static l_Lean_Meta_Grind_Action_mkGrindSeq___closed__3_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Action_mkGrindSeq___closed__3_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__3_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Action_mkGrindSeq___closed__3_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__3_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Action_mkGrindSeq___closed__3_value_aux_3: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__3_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__3_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Action_mkGrindSeq___closed__3_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__3_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__2_value)
                as *mut LeanObject,
            12547805878916670878 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Action_mkGrindSeq___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__3_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Action_mkGrindSeq___closed__4_value: LeanStringObject<18> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_Action_mkGrindSeq___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__4_value) as *mut LeanObject;
static l_Lean_Meta_Grind_Action_mkGrindSeq___closed__5_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Action_mkGrindSeq___closed__5_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__5_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Action_mkGrindSeq___closed__5_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__5_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Action_mkGrindSeq___closed__5_value_aux_3: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__5_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__3_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Action_mkGrindSeq___closed__5_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__5_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__4_value)
                as *mut LeanObject,
            13326625262248817187 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Action_mkGrindSeq___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__5_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__0_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__0_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__1_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__1_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__1_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__1_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__1_value_aux_3: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__1_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__3_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__1_value_aux_3
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__0_value)
                as *mut LeanObject,
            12389819025714499611 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__2_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__3_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__3_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__4_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__4_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__4_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__4_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__4_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__4_value_aux_3: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__4_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__3_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__4_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__4_value_aux_3
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__3_value)
                as *mut LeanObject,
            4707943553582391371 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__4_value)
        as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [112, 97, 114, 101, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__0_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__3_value) as *mut LeanObject,3168557723425139092 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__0_value) as *mut LeanObject,6341562230758934095 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__3_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__4_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 107, 105, 112, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__4_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__5_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__5_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__5_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__5_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__5_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__3_value) as *mut LeanObject,3168557723425139092 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__5_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__4_value) as *mut LeanObject,3888978822640132046 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__5_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Action_ungroup___redArg___closed__0_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_Action_ungroup___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_ungroup___redArg___closed__0_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_Action_ungroup___redArg___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Action_ungroup___redArg___closed__1_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_ungroup___redArg___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Action_ungroup___redArg___closed__1_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_ungroup___redArg___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_Action_ungroup___redArg___closed__1_value_aux_3: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_ungroup___redArg___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__3_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Action_ungroup___redArg___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_ungroup___redArg___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Action_ungroup___redArg___closed__0_value)
                as *mut LeanObject,
            7819112639170036602 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Action_ungroup___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_ungroup___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__1_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__1_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__2_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__2_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__3_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__3_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__4_value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__4_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__5_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__5_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__6_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__6_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___closed__0_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__0_value: LeanStringObject<39> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 39,
        m_capacity: 39,
        m_length: 38,
        m_data: [
            103, 101, 110, 101, 114, 97, 116, 101, 100, 32, 116, 97, 99, 116, 105, 99, 32, 99, 97,
            110, 110, 111, 116, 32, 99, 108, 111, 115, 101, 32, 116, 104, 101, 32, 103, 111, 97,
            108, 0,
        ],
    };
static mut l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__2_value: LeanStringObject<15> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Action_mbtc___closed__0_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_Action_mbtc___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mbtc___closed__0_value) as *mut LeanObject;
static l_Lean_Meta_Grind_Action_mbtc___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Grind_Action_mbtc___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mbtc___closed__1_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__1_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Grind_Action_mbtc___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mbtc___closed__1_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__2_value)
            as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Grind_Action_mbtc___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mbtc___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_run___lam__0___closed__3_value)
            as *mut LeanObject,
        3168557723425139092 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Action_mbtc___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mbtc___closed__1_value_aux_3)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mbtc___closed__0_value) as *mut LeanObject,
        17215256822346630302 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Action_mbtc___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_mbtc___closed__1_value) as *mut LeanObject;
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Grind_ActionResult_toMessageData_spec__1(
    mut v_a_2850_: *mut LeanObject,
    mut v_a_2851_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2857_: u8 = 0;
    let mut v_mvarId_2858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2863_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_2850_) == 0 {
                    v___x_2852_ = l_List_reverse___redArg(v_a_2851_);
                    return v___x_2852_;
                } else {
                    v_head_2853_ = lean_ctor_get(v_a_2850_, 0);
                    v_tail_2854_ = lean_ctor_get(v_a_2850_, 1);
                    v_isSharedCheck_2863_ = (!lean_is_exclusive(v_a_2850_)) as u8;
                    if v_isSharedCheck_2863_ == 0 {
                        v___x_2856_ = v_a_2850_;
                        v_isShared_2857_ = v_isSharedCheck_2863_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2854_);
                        lean_inc(v_head_2853_);
                        lean_dec(v_a_2850_);
                        v___x_2856_ = lean_box(0);
                        v_isShared_2857_ = v_isSharedCheck_2863_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_mvarId_2858_ = lean_ctor_get(v_head_2853_, 1);
                lean_inc(v_mvarId_2858_);
                lean_dec(v_head_2853_);
                if v_isShared_2857_ == 0 {
                    lean_ctor_set(v___x_2856_, 1, v_a_2851_);
                    lean_ctor_set(v___x_2856_, 0, v_mvarId_2858_);
                    v___x_2860_ = v___x_2856_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2862_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2862_, 0, v_mvarId_2858_);
                    lean_ctor_set(v_reuseFailAlloc_2862_, 1, v_a_2851_);
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
    mut v_a_2864_: *mut LeanObject,
    mut v_a_2865_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2871_: u8 = 0;
    let mut v___x_2872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2877_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_2864_) == 0 {
                    v___x_2866_ = l_List_reverse___redArg(v_a_2865_);
                    return v___x_2866_;
                } else {
                    v_head_2867_ = lean_ctor_get(v_a_2864_, 0);
                    v_tail_2868_ = lean_ctor_get(v_a_2864_, 1);
                    v_isSharedCheck_2877_ = (!lean_is_exclusive(v_a_2864_)) as u8;
                    if v_isSharedCheck_2877_ == 0 {
                        v___x_2870_ = v_a_2864_;
                        v_isShared_2871_ = v_isSharedCheck_2877_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2868_);
                        lean_inc(v_head_2867_);
                        lean_dec(v_a_2864_);
                        v___x_2870_ = lean_box(0);
                        v_isShared_2871_ = v_isSharedCheck_2877_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2872_ = l_Lean_MessageData_ofSyntax(v_head_2867_);
                if v_isShared_2871_ == 0 {
                    lean_ctor_set(v___x_2870_, 1, v_a_2865_);
                    lean_ctor_set(v___x_2870_, 0, v___x_2872_);
                    v___x_2874_ = v___x_2870_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2876_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2876_, 0, v___x_2872_);
                    lean_ctor_set(v_reuseFailAlloc_2876_, 1, v_a_2865_);
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
    mut v_a_2878_: *mut LeanObject,
    mut v_a_2879_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2885_: u8 = 0;
    let mut v___x_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2891_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_2878_) == 0 {
                    v___x_2880_ = l_List_reverse___redArg(v_a_2879_);
                    return v___x_2880_;
                } else {
                    v_head_2881_ = lean_ctor_get(v_a_2878_, 0);
                    v_tail_2882_ = lean_ctor_get(v_a_2878_, 1);
                    v_isSharedCheck_2891_ = (!lean_is_exclusive(v_a_2878_)) as u8;
                    if v_isSharedCheck_2891_ == 0 {
                        v___x_2884_ = v_a_2878_;
                        v_isShared_2885_ = v_isSharedCheck_2891_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2882_);
                        lean_inc(v_head_2881_);
                        lean_dec(v_a_2878_);
                        v___x_2884_ = lean_box(0);
                        v_isShared_2885_ = v_isSharedCheck_2891_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2886_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2886_, 0, v_head_2881_);
                if v_isShared_2885_ == 0 {
                    lean_ctor_set(v___x_2884_, 1, v_a_2879_);
                    lean_ctor_set(v___x_2884_, 0, v___x_2886_);
                    v___x_2888_ = v___x_2884_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2890_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2890_, 0, v___x_2886_);
                    lean_ctor_set(v_reuseFailAlloc_2890_, 1, v_a_2879_);
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
pub unsafe fn _init_l_Lean_Meta_Grind_ActionResult_toMessageData___closed__1() -> *mut LeanObject {
    let mut v___x_2893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut LeanObject = core::ptr::null_mut();
    v___x_2893_ = l_Lean_Meta_Grind_ActionResult_toMessageData___closed__0;
    v___x_2894_ = l_Lean_stringToMessageData(v___x_2893_);
    return v___x_2894_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_ActionResult_toMessageData___closed__3() -> *mut LeanObject {
    let mut v___x_2896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: *mut LeanObject = core::ptr::null_mut();
    v___x_2896_ = l_Lean_Meta_Grind_ActionResult_toMessageData___closed__2;
    v___x_2897_ = l_Lean_stringToMessageData(v___x_2896_);
    return v___x_2897_;
}
pub unsafe fn l_Lean_Meta_Grind_ActionResult_toMessageData(
    mut v_x_2898_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2898_) == 0 {
        let mut v_seq_2899_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2900_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2901_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2902_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2903_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2904_: *mut LeanObject = core::ptr::null_mut();
        v_seq_2899_ = lean_ctor_get(v_x_2898_, 0);
        lean_inc(v_seq_2899_);
        lean_dec_ref_known(v_x_2898_, 1);
        v___x_2900_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_ActionResult_toMessageData___closed__1),
            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_ActionResult_toMessageData___closed__1_once),
            _init_l_Lean_Meta_Grind_ActionResult_toMessageData___closed__1,
        );
        v___x_2901_ = lean_box(0);
        v___x_2902_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_ActionResult_toMessageData_spec__0(
            v_seq_2899_,
            v___x_2901_,
        );
        v___x_2903_ = l_Lean_MessageData_ofList(v___x_2902_);
        v___x_2904_ = lean_alloc_ctor(7, 2, (0) as u32);
        lean_ctor_set(v___x_2904_, 0, v___x_2900_);
        lean_ctor_set(v___x_2904_, 1, v___x_2903_);
        return v___x_2904_;
    } else {
        let mut v_gs_2905_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2906_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2907_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2908_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2909_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2910_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2911_: *mut LeanObject = core::ptr::null_mut();
        v_gs_2905_ = lean_ctor_get(v_x_2898_, 0);
        lean_inc(v_gs_2905_);
        lean_dec_ref_known(v_x_2898_, 1);
        v___x_2906_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_ActionResult_toMessageData___closed__3),
            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_ActionResult_toMessageData___closed__3_once),
            _init_l_Lean_Meta_Grind_ActionResult_toMessageData___closed__3,
        );
        v___x_2907_ = lean_box(0);
        v___x_2908_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_ActionResult_toMessageData_spec__1(
            v_gs_2905_,
            v___x_2907_,
        );
        v___x_2909_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_ActionResult_toMessageData_spec__2(
            v___x_2908_,
            v___x_2907_,
        );
        v___x_2910_ = l_Lean_MessageData_ofList(v___x_2909_);
        v___x_2911_ = lean_alloc_ctor(7, 2, (0) as u32);
        lean_ctor_set(v___x_2911_, 0, v___x_2906_);
        lean_ctor_set(v___x_2911_, 1, v___x_2910_);
        return v___x_2911_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Action_skip___redArg(
    mut v_goal_2914_: *mut LeanObject,
    mut v_kp_2915_: *mut LeanObject,
    mut v_a_2916_: *mut LeanObject,
    mut v_a_2917_: *mut LeanObject,
    mut v_a_2918_: *mut LeanObject,
    mut v_a_2919_: *mut LeanObject,
    mut v_a_2920_: *mut LeanObject,
    mut v_a_2921_: *mut LeanObject,
    mut v_a_2922_: *mut LeanObject,
    mut v_a_2923_: *mut LeanObject,
    mut v_a_2924_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2926_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_2924_);
    lean_inc_ref(v_a_2923_);
    lean_inc(v_a_2922_);
    lean_inc_ref(v_a_2921_);
    lean_inc(v_a_2920_);
    lean_inc_ref(v_a_2919_);
    lean_inc(v_a_2918_);
    lean_inc_ref(v_a_2917_);
    lean_inc(v_a_2916_);
    v___x_2926_ = lean_apply_11(
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
        lean_box(0),
    );
    return v___x_2926_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_skip___redArg___boxed(
    mut v_goal_2927_: *mut LeanObject,
    mut v_kp_2928_: *mut LeanObject,
    mut v_a_2929_: *mut LeanObject,
    mut v_a_2930_: *mut LeanObject,
    mut v_a_2931_: *mut LeanObject,
    mut v_a_2932_: *mut LeanObject,
    mut v_a_2933_: *mut LeanObject,
    mut v_a_2934_: *mut LeanObject,
    mut v_a_2935_: *mut LeanObject,
    mut v_a_2936_: *mut LeanObject,
    mut v_a_2937_: *mut LeanObject,
    mut v_a_2938_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2939_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_2937_);
    lean_dec_ref(v_a_2936_);
    lean_dec(v_a_2935_);
    lean_dec_ref(v_a_2934_);
    lean_dec(v_a_2933_);
    lean_dec_ref(v_a_2932_);
    lean_dec(v_a_2931_);
    lean_dec_ref(v_a_2930_);
    lean_dec(v_a_2929_);
    return v_res_2939_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_skip(
    mut v_goal_2940_: *mut LeanObject,
    mut v_x_2941_: *mut LeanObject,
    mut v_kp_2942_: *mut LeanObject,
    mut v_a_2943_: *mut LeanObject,
    mut v_a_2944_: *mut LeanObject,
    mut v_a_2945_: *mut LeanObject,
    mut v_a_2946_: *mut LeanObject,
    mut v_a_2947_: *mut LeanObject,
    mut v_a_2948_: *mut LeanObject,
    mut v_a_2949_: *mut LeanObject,
    mut v_a_2950_: *mut LeanObject,
    mut v_a_2951_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2953_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_2951_);
    lean_inc_ref(v_a_2950_);
    lean_inc(v_a_2949_);
    lean_inc_ref(v_a_2948_);
    lean_inc(v_a_2947_);
    lean_inc_ref(v_a_2946_);
    lean_inc(v_a_2945_);
    lean_inc_ref(v_a_2944_);
    lean_inc(v_a_2943_);
    v___x_2953_ = lean_apply_11(
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
        lean_box(0),
    );
    return v___x_2953_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_skip___boxed(
    mut v_goal_2954_: *mut LeanObject,
    mut v_x_2955_: *mut LeanObject,
    mut v_kp_2956_: *mut LeanObject,
    mut v_a_2957_: *mut LeanObject,
    mut v_a_2958_: *mut LeanObject,
    mut v_a_2959_: *mut LeanObject,
    mut v_a_2960_: *mut LeanObject,
    mut v_a_2961_: *mut LeanObject,
    mut v_a_2962_: *mut LeanObject,
    mut v_a_2963_: *mut LeanObject,
    mut v_a_2964_: *mut LeanObject,
    mut v_a_2965_: *mut LeanObject,
    mut v_a_2966_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2967_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_2965_);
    lean_dec_ref(v_a_2964_);
    lean_dec(v_a_2963_);
    lean_dec_ref(v_a_2962_);
    lean_dec(v_a_2961_);
    lean_dec_ref(v_a_2960_);
    lean_dec(v_a_2959_);
    lean_dec_ref(v_a_2958_);
    lean_dec(v_a_2957_);
    lean_dec_ref(v_x_2955_);
    return v_res_2967_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_done___redArg(
    mut v_goal_2970_: *mut LeanObject,
    mut v_kna_2971_: *mut LeanObject,
    mut v_a_2972_: *mut LeanObject,
    mut v_a_2973_: *mut LeanObject,
    mut v_a_2974_: *mut LeanObject,
    mut v_a_2975_: *mut LeanObject,
    mut v_a_2976_: *mut LeanObject,
    mut v_a_2977_: *mut LeanObject,
    mut v_a_2978_: *mut LeanObject,
    mut v_a_2979_: *mut LeanObject,
    mut v_a_2980_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toGoalState_2982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inconsistent_2983_: u8 = 0;
    v_toGoalState_2982_ = lean_ctor_get(v_goal_2970_, 0);
    v_inconsistent_2983_ = lean_ctor_get_uint8(
        v_toGoalState_2982_,
        (core::mem::size_of::<*mut LeanObject>() * 17) as u32,
    );
    if v_inconsistent_2983_ == 0 {
        let mut v___x_2984_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v_a_2980_);
        lean_inc_ref(v_a_2979_);
        lean_inc(v_a_2978_);
        lean_inc_ref(v_a_2977_);
        lean_inc(v_a_2976_);
        lean_inc_ref(v_a_2975_);
        lean_inc(v_a_2974_);
        lean_inc_ref(v_a_2973_);
        lean_inc(v_a_2972_);
        v___x_2984_ = lean_apply_11(
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
            lean_box(0),
        );
        return v___x_2984_;
    } else {
        let mut v___x_2985_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2986_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_kna_2971_);
        lean_dec_ref(v_goal_2970_);
        v___x_2985_ = l_Lean_Meta_Grind_Action_done___redArg___closed__0;
        v___x_2986_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_2986_, 0, v___x_2985_);
        return v___x_2986_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Action_done___redArg___boxed(
    mut v_goal_2987_: *mut LeanObject,
    mut v_kna_2988_: *mut LeanObject,
    mut v_a_2989_: *mut LeanObject,
    mut v_a_2990_: *mut LeanObject,
    mut v_a_2991_: *mut LeanObject,
    mut v_a_2992_: *mut LeanObject,
    mut v_a_2993_: *mut LeanObject,
    mut v_a_2994_: *mut LeanObject,
    mut v_a_2995_: *mut LeanObject,
    mut v_a_2996_: *mut LeanObject,
    mut v_a_2997_: *mut LeanObject,
    mut v_a_2998_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2999_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_2997_);
    lean_dec_ref(v_a_2996_);
    lean_dec(v_a_2995_);
    lean_dec_ref(v_a_2994_);
    lean_dec(v_a_2993_);
    lean_dec_ref(v_a_2992_);
    lean_dec(v_a_2991_);
    lean_dec_ref(v_a_2990_);
    lean_dec(v_a_2989_);
    return v_res_2999_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_done(
    mut v_goal_3000_: *mut LeanObject,
    mut v_kna_3001_: *mut LeanObject,
    mut v_x_3002_: *mut LeanObject,
    mut v_a_3003_: *mut LeanObject,
    mut v_a_3004_: *mut LeanObject,
    mut v_a_3005_: *mut LeanObject,
    mut v_a_3006_: *mut LeanObject,
    mut v_a_3007_: *mut LeanObject,
    mut v_a_3008_: *mut LeanObject,
    mut v_a_3009_: *mut LeanObject,
    mut v_a_3010_: *mut LeanObject,
    mut v_a_3011_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3013_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_goal_3014_: *mut LeanObject,
    mut v_kna_3015_: *mut LeanObject,
    mut v_x_3016_: *mut LeanObject,
    mut v_a_3017_: *mut LeanObject,
    mut v_a_3018_: *mut LeanObject,
    mut v_a_3019_: *mut LeanObject,
    mut v_a_3020_: *mut LeanObject,
    mut v_a_3021_: *mut LeanObject,
    mut v_a_3022_: *mut LeanObject,
    mut v_a_3023_: *mut LeanObject,
    mut v_a_3024_: *mut LeanObject,
    mut v_a_3025_: *mut LeanObject,
    mut v_a_3026_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3027_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_3025_);
    lean_dec_ref(v_a_3024_);
    lean_dec(v_a_3023_);
    lean_dec_ref(v_a_3022_);
    lean_dec(v_a_3021_);
    lean_dec_ref(v_a_3020_);
    lean_dec(v_a_3019_);
    lean_dec_ref(v_a_3018_);
    lean_dec(v_a_3017_);
    lean_dec_ref(v_x_3016_);
    return v_res_3027_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_andThen___lam__0(
    mut v_y_3028_: *mut LeanObject,
    mut v_kp_3029_: *mut LeanObject,
    mut v_goal_x27_3030_: *mut LeanObject,
    mut v___y_3031_: *mut LeanObject,
    mut v___y_3032_: *mut LeanObject,
    mut v___y_3033_: *mut LeanObject,
    mut v___y_3034_: *mut LeanObject,
    mut v___y_3035_: *mut LeanObject,
    mut v___y_3036_: *mut LeanObject,
    mut v___y_3037_: *mut LeanObject,
    mut v___y_3038_: *mut LeanObject,
    mut v___y_3039_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3041_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_3039_);
    lean_inc_ref(v___y_3038_);
    lean_inc(v___y_3037_);
    lean_inc_ref(v___y_3036_);
    lean_inc(v___y_3035_);
    lean_inc_ref(v___y_3034_);
    lean_inc(v___y_3033_);
    lean_inc_ref(v___y_3032_);
    lean_inc(v___y_3031_);
    lean_inc_ref(v_kp_3029_);
    v___x_3041_ = lean_apply_13(
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
        lean_box(0),
    );
    return v___x_3041_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_andThen___lam__0___boxed(
    mut v_y_3042_: *mut LeanObject,
    mut v_kp_3043_: *mut LeanObject,
    mut v_goal_x27_3044_: *mut LeanObject,
    mut v___y_3045_: *mut LeanObject,
    mut v___y_3046_: *mut LeanObject,
    mut v___y_3047_: *mut LeanObject,
    mut v___y_3048_: *mut LeanObject,
    mut v___y_3049_: *mut LeanObject,
    mut v___y_3050_: *mut LeanObject,
    mut v___y_3051_: *mut LeanObject,
    mut v___y_3052_: *mut LeanObject,
    mut v___y_3053_: *mut LeanObject,
    mut v___y_3054_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3055_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_3053_);
    lean_dec_ref(v___y_3052_);
    lean_dec(v___y_3051_);
    lean_dec_ref(v___y_3050_);
    lean_dec(v___y_3049_);
    lean_dec_ref(v___y_3048_);
    lean_dec(v___y_3047_);
    lean_dec_ref(v___y_3046_);
    lean_dec(v___y_3045_);
    return v_res_3055_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_andThen(
    mut v_x_3056_: *mut LeanObject,
    mut v_y_3057_: *mut LeanObject,
    mut v_goal_3058_: *mut LeanObject,
    mut v_kna_3059_: *mut LeanObject,
    mut v_kp_3060_: *mut LeanObject,
    mut v_a_3061_: *mut LeanObject,
    mut v_a_3062_: *mut LeanObject,
    mut v_a_3063_: *mut LeanObject,
    mut v_a_3064_: *mut LeanObject,
    mut v_a_3065_: *mut LeanObject,
    mut v_a_3066_: *mut LeanObject,
    mut v_a_3067_: *mut LeanObject,
    mut v_a_3068_: *mut LeanObject,
    mut v_a_3069_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: *mut LeanObject = core::ptr::null_mut();
    v___f_3071_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Action_andThen___lam__0___boxed as *mut core::ffi::c_void,
        13,
        2,
    );
    lean_closure_set(v___f_3071_, 0, v_y_3057_);
    lean_closure_set(v___f_3071_, 1, v_kp_3060_);
    lean_inc(v_a_3069_);
    lean_inc_ref(v_a_3068_);
    lean_inc(v_a_3067_);
    lean_inc_ref(v_a_3066_);
    lean_inc(v_a_3065_);
    lean_inc_ref(v_a_3064_);
    lean_inc(v_a_3063_);
    lean_inc_ref(v_a_3062_);
    lean_inc(v_a_3061_);
    v___x_3072_ = lean_apply_13(
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
        lean_box(0),
    );
    return v___x_3072_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_andThen___boxed(
    mut v_x_3073_: *mut LeanObject,
    mut v_y_3074_: *mut LeanObject,
    mut v_goal_3075_: *mut LeanObject,
    mut v_kna_3076_: *mut LeanObject,
    mut v_kp_3077_: *mut LeanObject,
    mut v_a_3078_: *mut LeanObject,
    mut v_a_3079_: *mut LeanObject,
    mut v_a_3080_: *mut LeanObject,
    mut v_a_3081_: *mut LeanObject,
    mut v_a_3082_: *mut LeanObject,
    mut v_a_3083_: *mut LeanObject,
    mut v_a_3084_: *mut LeanObject,
    mut v_a_3085_: *mut LeanObject,
    mut v_a_3086_: *mut LeanObject,
    mut v_a_3087_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3088_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_3086_);
    lean_dec_ref(v_a_3085_);
    lean_dec(v_a_3084_);
    lean_dec_ref(v_a_3083_);
    lean_dec(v_a_3082_);
    lean_dec_ref(v_a_3081_);
    lean_dec(v_a_3080_);
    lean_dec_ref(v_a_3079_);
    lean_dec(v_a_3078_);
    return v_res_3088_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_instAndThen___lam__0(
    mut v_x_3089_: *mut LeanObject,
    mut v_y_3090_: *mut LeanObject,
    mut v___y_3091_: *mut LeanObject,
    mut v___y_3092_: *mut LeanObject,
    mut v___y_3093_: *mut LeanObject,
    mut v___y_3094_: *mut LeanObject,
    mut v___y_3095_: *mut LeanObject,
    mut v___y_3096_: *mut LeanObject,
    mut v___y_3097_: *mut LeanObject,
    mut v___y_3098_: *mut LeanObject,
    mut v___y_3099_: *mut LeanObject,
    mut v___y_3100_: *mut LeanObject,
    mut v___y_3101_: *mut LeanObject,
    mut v___y_3102_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut LeanObject = core::ptr::null_mut();
    v___x_3104_ = lean_box(0);
    v___x_3105_ = lean_apply_1(v_y_3090_, v___x_3104_);
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
    mut v_x_3107_: *mut LeanObject,
    mut v_y_3108_: *mut LeanObject,
    mut v___y_3109_: *mut LeanObject,
    mut v___y_3110_: *mut LeanObject,
    mut v___y_3111_: *mut LeanObject,
    mut v___y_3112_: *mut LeanObject,
    mut v___y_3113_: *mut LeanObject,
    mut v___y_3114_: *mut LeanObject,
    mut v___y_3115_: *mut LeanObject,
    mut v___y_3116_: *mut LeanObject,
    mut v___y_3117_: *mut LeanObject,
    mut v___y_3118_: *mut LeanObject,
    mut v___y_3119_: *mut LeanObject,
    mut v___y_3120_: *mut LeanObject,
    mut v___y_3121_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3122_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_3120_);
    lean_dec_ref(v___y_3119_);
    lean_dec(v___y_3118_);
    lean_dec_ref(v___y_3117_);
    lean_dec(v___y_3116_);
    lean_dec_ref(v___y_3115_);
    lean_dec(v___y_3114_);
    lean_dec_ref(v___y_3113_);
    lean_dec(v___y_3112_);
    return v_res_3122_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_orElse___lam__0(
    mut v_y_3125_: *mut LeanObject,
    mut v_kna_3126_: *mut LeanObject,
    mut v_kp_3127_: *mut LeanObject,
    mut v_goal_3128_: *mut LeanObject,
    mut v___y_3129_: *mut LeanObject,
    mut v___y_3130_: *mut LeanObject,
    mut v___y_3131_: *mut LeanObject,
    mut v___y_3132_: *mut LeanObject,
    mut v___y_3133_: *mut LeanObject,
    mut v___y_3134_: *mut LeanObject,
    mut v___y_3135_: *mut LeanObject,
    mut v___y_3136_: *mut LeanObject,
    mut v___y_3137_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3139_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_3137_);
    lean_inc_ref(v___y_3136_);
    lean_inc(v___y_3135_);
    lean_inc_ref(v___y_3134_);
    lean_inc(v___y_3133_);
    lean_inc_ref(v___y_3132_);
    lean_inc(v___y_3131_);
    lean_inc_ref(v___y_3130_);
    lean_inc(v___y_3129_);
    v___x_3139_ = lean_apply_13(
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
        lean_box(0),
    );
    return v___x_3139_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_orElse___lam__0___boxed(
    mut v_y_3140_: *mut LeanObject,
    mut v_kna_3141_: *mut LeanObject,
    mut v_kp_3142_: *mut LeanObject,
    mut v_goal_3143_: *mut LeanObject,
    mut v___y_3144_: *mut LeanObject,
    mut v___y_3145_: *mut LeanObject,
    mut v___y_3146_: *mut LeanObject,
    mut v___y_3147_: *mut LeanObject,
    mut v___y_3148_: *mut LeanObject,
    mut v___y_3149_: *mut LeanObject,
    mut v___y_3150_: *mut LeanObject,
    mut v___y_3151_: *mut LeanObject,
    mut v___y_3152_: *mut LeanObject,
    mut v___y_3153_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3154_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_3152_);
    lean_dec_ref(v___y_3151_);
    lean_dec(v___y_3150_);
    lean_dec_ref(v___y_3149_);
    lean_dec(v___y_3148_);
    lean_dec_ref(v___y_3147_);
    lean_dec(v___y_3146_);
    lean_dec_ref(v___y_3145_);
    lean_dec(v___y_3144_);
    return v_res_3154_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_orElse(
    mut v_x_3155_: *mut LeanObject,
    mut v_y_3156_: *mut LeanObject,
    mut v_goal_3157_: *mut LeanObject,
    mut v_kna_3158_: *mut LeanObject,
    mut v_kp_3159_: *mut LeanObject,
    mut v_a_3160_: *mut LeanObject,
    mut v_a_3161_: *mut LeanObject,
    mut v_a_3162_: *mut LeanObject,
    mut v_a_3163_: *mut LeanObject,
    mut v_a_3164_: *mut LeanObject,
    mut v_a_3165_: *mut LeanObject,
    mut v_a_3166_: *mut LeanObject,
    mut v_a_3167_: *mut LeanObject,
    mut v_a_3168_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_kp_3159_);
    v___f_3170_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Action_orElse___lam__0___boxed as *mut core::ffi::c_void,
        14,
        3,
    );
    lean_closure_set(v___f_3170_, 0, v_y_3156_);
    lean_closure_set(v___f_3170_, 1, v_kna_3158_);
    lean_closure_set(v___f_3170_, 2, v_kp_3159_);
    lean_inc(v_a_3168_);
    lean_inc_ref(v_a_3167_);
    lean_inc(v_a_3166_);
    lean_inc_ref(v_a_3165_);
    lean_inc(v_a_3164_);
    lean_inc_ref(v_a_3163_);
    lean_inc(v_a_3162_);
    lean_inc_ref(v_a_3161_);
    lean_inc(v_a_3160_);
    v___x_3171_ = lean_apply_13(
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
        lean_box(0),
    );
    return v___x_3171_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_orElse___boxed(
    mut v_x_3172_: *mut LeanObject,
    mut v_y_3173_: *mut LeanObject,
    mut v_goal_3174_: *mut LeanObject,
    mut v_kna_3175_: *mut LeanObject,
    mut v_kp_3176_: *mut LeanObject,
    mut v_a_3177_: *mut LeanObject,
    mut v_a_3178_: *mut LeanObject,
    mut v_a_3179_: *mut LeanObject,
    mut v_a_3180_: *mut LeanObject,
    mut v_a_3181_: *mut LeanObject,
    mut v_a_3182_: *mut LeanObject,
    mut v_a_3183_: *mut LeanObject,
    mut v_a_3184_: *mut LeanObject,
    mut v_a_3185_: *mut LeanObject,
    mut v_a_3186_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3187_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_3185_);
    lean_dec_ref(v_a_3184_);
    lean_dec(v_a_3183_);
    lean_dec_ref(v_a_3182_);
    lean_dec(v_a_3181_);
    lean_dec_ref(v_a_3180_);
    lean_dec(v_a_3179_);
    lean_dec_ref(v_a_3178_);
    lean_dec(v_a_3177_);
    return v_res_3187_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_instOrElse___lam__0(
    mut v_x_3188_: *mut LeanObject,
    mut v_y_3189_: *mut LeanObject,
    mut v___y_3190_: *mut LeanObject,
    mut v___y_3191_: *mut LeanObject,
    mut v___y_3192_: *mut LeanObject,
    mut v___y_3193_: *mut LeanObject,
    mut v___y_3194_: *mut LeanObject,
    mut v___y_3195_: *mut LeanObject,
    mut v___y_3196_: *mut LeanObject,
    mut v___y_3197_: *mut LeanObject,
    mut v___y_3198_: *mut LeanObject,
    mut v___y_3199_: *mut LeanObject,
    mut v___y_3200_: *mut LeanObject,
    mut v___y_3201_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut LeanObject = core::ptr::null_mut();
    v___x_3203_ = lean_box(0);
    v___x_3204_ = lean_apply_1(v_y_3189_, v___x_3203_);
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
    mut v_x_3206_: *mut LeanObject,
    mut v_y_3207_: *mut LeanObject,
    mut v___y_3208_: *mut LeanObject,
    mut v___y_3209_: *mut LeanObject,
    mut v___y_3210_: *mut LeanObject,
    mut v___y_3211_: *mut LeanObject,
    mut v___y_3212_: *mut LeanObject,
    mut v___y_3213_: *mut LeanObject,
    mut v___y_3214_: *mut LeanObject,
    mut v___y_3215_: *mut LeanObject,
    mut v___y_3216_: *mut LeanObject,
    mut v___y_3217_: *mut LeanObject,
    mut v___y_3218_: *mut LeanObject,
    mut v___y_3219_: *mut LeanObject,
    mut v___y_3220_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3221_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_3219_);
    lean_dec_ref(v___y_3218_);
    lean_dec(v___y_3217_);
    lean_dec_ref(v___y_3216_);
    lean_dec(v___y_3215_);
    lean_dec_ref(v___y_3214_);
    lean_dec(v___y_3213_);
    lean_dec_ref(v___y_3212_);
    lean_dec(v___y_3211_);
    return v_res_3221_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_loop___redArg___lam__0___boxed(
    mut v_n_3224_: *mut LeanObject,
    mut v_x_3225_: *mut LeanObject,
    mut v_kp_3226_: *mut LeanObject,
    mut v_goal_x27_3227_: *mut LeanObject,
    mut v___y_3228_: *mut LeanObject,
    mut v___y_3229_: *mut LeanObject,
    mut v___y_3230_: *mut LeanObject,
    mut v___y_3231_: *mut LeanObject,
    mut v___y_3232_: *mut LeanObject,
    mut v___y_3233_: *mut LeanObject,
    mut v___y_3234_: *mut LeanObject,
    mut v___y_3235_: *mut LeanObject,
    mut v___y_3236_: *mut LeanObject,
    mut v___y_3237_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3238_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_3236_);
    lean_dec_ref(v___y_3235_);
    lean_dec(v___y_3234_);
    lean_dec_ref(v___y_3233_);
    lean_dec(v___y_3232_);
    lean_dec_ref(v___y_3231_);
    lean_dec(v___y_3230_);
    lean_dec_ref(v___y_3229_);
    lean_dec(v___y_3228_);
    lean_dec(v_n_3224_);
    return v_res_3238_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_loop___redArg(
    mut v_n_3239_: *mut LeanObject,
    mut v_x_3240_: *mut LeanObject,
    mut v_goal_3241_: *mut LeanObject,
    mut v_kp_3242_: *mut LeanObject,
    mut v_a_3243_: *mut LeanObject,
    mut v_a_3244_: *mut LeanObject,
    mut v_a_3245_: *mut LeanObject,
    mut v_a_3246_: *mut LeanObject,
    mut v_a_3247_: *mut LeanObject,
    mut v_a_3248_: *mut LeanObject,
    mut v_a_3249_: *mut LeanObject,
    mut v_a_3250_: *mut LeanObject,
    mut v_a_3251_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3261_: u8 = 0;
    let mut v___x_3262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: u8 = 0;
    let mut v___x_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3270_: u8 = 0;
    let mut v___x_3272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3274_: u8 = 0;
    let mut v_a_3275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3278_: u8 = 0;
    let mut v___x_3280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3282_: u8 = 0;
    let mut v___y_3284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: u8 = 0;
    let mut v___x_3287_: u8 = 0;
    let mut v___x_3288_: u8 = 0;
    let mut v_zero_3289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_3290_: u8 = 0;
    let mut v___x_3291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_3292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_3293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_3289_ = lean_unsigned_to_nat(0);
                v_isZero_3290_ = lean_nat_dec_eq(v_n_3239_, v_zero_3289_);
                if v_isZero_3290_ == 1 {
                    lean_dec_ref(v_x_3240_);
                    lean_inc(v_a_3251_);
                    lean_inc_ref(v_a_3250_);
                    lean_inc(v_a_3249_);
                    lean_inc_ref(v_a_3248_);
                    lean_inc(v_a_3247_);
                    lean_inc_ref(v_a_3246_);
                    lean_inc(v_a_3245_);
                    lean_inc_ref(v_a_3244_);
                    lean_inc(v_a_3243_);
                    lean_inc_ref(v_goal_3241_);
                    v___x_3291_ = lean_apply_11(
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
                        lean_box(0),
                    );
                    v___y_3284_ = v___x_3291_;
                    state = 7;
                    continue;
                } else {
                    v_one_3292_ = lean_unsigned_to_nat(1);
                    v_n_3293_ = lean_nat_sub(v_n_3239_, v_one_3292_);
                    lean_inc_ref(v_kp_3242_);
                    lean_inc_ref(v_x_3240_);
                    v___f_3294_ = lean_alloc_closure(
                        l_Lean_Meta_Grind_Action_loop___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        14,
                        3,
                    );
                    lean_closure_set(v___f_3294_, 0, v_n_3293_);
                    lean_closure_set(v___f_3294_, 1, v_x_3240_);
                    lean_closure_set(v___f_3294_, 2, v_kp_3242_);
                    lean_inc(v_a_3251_);
                    lean_inc_ref(v_a_3250_);
                    lean_inc(v_a_3249_);
                    lean_inc_ref(v_a_3248_);
                    lean_inc(v_a_3247_);
                    lean_inc_ref(v_a_3246_);
                    lean_inc(v_a_3245_);
                    lean_inc_ref(v_a_3244_);
                    lean_inc(v_a_3243_);
                    lean_inc_ref(v_goal_3241_);
                    v___x_3295_ = lean_apply_13(
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
                        lean_box(0),
                    );
                    v___y_3284_ = v___x_3295_;
                    state = 7;
                    continue;
                }
            }
            1 => {
                v___x_3254_ = lean_box(0);
                v___x_3255_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3255_, 0, v_goal_3241_);
                lean_ctor_set(v___x_3255_, 1, v___x_3254_);
                v___x_3256_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3256_, 0, v___x_3255_);
                v___x_3257_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3257_, 0, v___x_3256_);
                return v___x_3257_;
            }
            2 => {
                if v___y_3261_ == 0 {
                    lean_dec_ref(v___y_3260_);
                    lean_dec_ref(v_goal_3241_);
                    return v___y_3259_;
                } else {
                    lean_dec_ref(v___y_3259_);
                    v___x_3262_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_3246_);
                    if lean_obj_tag(v___x_3262_) == 0 {
                        v_a_3263_ = lean_ctor_get(v___x_3262_, 0);
                        lean_inc(v_a_3263_);
                        lean_dec_ref_known(v___x_3262_, 1);
                        v___x_3264_ = (lean_unbox(v_a_3263_) as u8);
                        lean_dec(v_a_3263_);
                        if v___x_3264_ == 0 {
                            lean_dec_ref(v___y_3260_);
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
                            if lean_obj_tag(v___x_3266_) == 0 {
                                lean_dec_ref_known(v___x_3266_, 1);
                                state = 1;
                                continue;
                            } else {
                                lean_dec_ref(v_goal_3241_);
                                v_a_3267_ = lean_ctor_get(v___x_3266_, 0);
                                v_isSharedCheck_3274_ = (!lean_is_exclusive(v___x_3266_)) as u8;
                                if v_isSharedCheck_3274_ == 0 {
                                    v___x_3269_ = v___x_3266_;
                                    v_isShared_3270_ = v_isSharedCheck_3274_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_inc(v_a_3267_);
                                    lean_dec(v___x_3266_);
                                    v___x_3269_ = lean_box(0);
                                    v_isShared_3270_ = v_isSharedCheck_3274_;
                                    state = 3;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec_ref(v___y_3260_);
                        lean_dec_ref(v_goal_3241_);
                        v_a_3275_ = lean_ctor_get(v___x_3262_, 0);
                        v_isSharedCheck_3282_ = (!lean_is_exclusive(v___x_3262_)) as u8;
                        if v_isSharedCheck_3282_ == 0 {
                            v___x_3277_ = v___x_3262_;
                            v_isShared_3278_ = v_isSharedCheck_3282_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_3275_);
                            lean_dec(v___x_3262_);
                            v___x_3277_ = lean_box(0);
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
                    v_reuseFailAlloc_3273_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3273_, 0, v_a_3267_);
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
                    v_reuseFailAlloc_3281_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3281_, 0, v_a_3275_);
                    v___x_3280_ = v_reuseFailAlloc_3281_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3280_;
            }
            7 => {
                if lean_obj_tag(v___y_3284_) == 0 {
                    lean_dec_ref(v_goal_3241_);
                    return v___y_3284_;
                } else {
                    v_a_3285_ = lean_ctor_get(v___y_3284_, 0);
                    v___x_3286_ = l_Lean_Exception_isInterrupt(v_a_3285_);
                    if v___x_3286_ == 0 {
                        lean_inc_n(v_a_3285_, 2);
                        v___x_3287_ = l_Lean_Exception_isMaxHeartbeat(v_a_3285_);
                        if v___x_3287_ == 0 {
                            lean_inc(v_a_3285_);
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
                        lean_dec_ref(v_goal_3241_);
                        return v___y_3284_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Action_loop___redArg___lam__0(
    mut v_n_3296_: *mut LeanObject,
    mut v_x_3297_: *mut LeanObject,
    mut v_kp_3298_: *mut LeanObject,
    mut v_goal_x27_3299_: *mut LeanObject,
    mut v___y_3300_: *mut LeanObject,
    mut v___y_3301_: *mut LeanObject,
    mut v___y_3302_: *mut LeanObject,
    mut v___y_3303_: *mut LeanObject,
    mut v___y_3304_: *mut LeanObject,
    mut v___y_3305_: *mut LeanObject,
    mut v___y_3306_: *mut LeanObject,
    mut v___y_3307_: *mut LeanObject,
    mut v___y_3308_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3310_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_n_3311_: *mut LeanObject,
    mut v_x_3312_: *mut LeanObject,
    mut v_goal_3313_: *mut LeanObject,
    mut v_kp_3314_: *mut LeanObject,
    mut v_a_3315_: *mut LeanObject,
    mut v_a_3316_: *mut LeanObject,
    mut v_a_3317_: *mut LeanObject,
    mut v_a_3318_: *mut LeanObject,
    mut v_a_3319_: *mut LeanObject,
    mut v_a_3320_: *mut LeanObject,
    mut v_a_3321_: *mut LeanObject,
    mut v_a_3322_: *mut LeanObject,
    mut v_a_3323_: *mut LeanObject,
    mut v_a_3324_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3325_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_3323_);
    lean_dec_ref(v_a_3322_);
    lean_dec(v_a_3321_);
    lean_dec_ref(v_a_3320_);
    lean_dec(v_a_3319_);
    lean_dec_ref(v_a_3318_);
    lean_dec(v_a_3317_);
    lean_dec_ref(v_a_3316_);
    lean_dec(v_a_3315_);
    lean_dec(v_n_3311_);
    return v_res_3325_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_loop(
    mut v_n_3326_: *mut LeanObject,
    mut v_x_3327_: *mut LeanObject,
    mut v_goal_3328_: *mut LeanObject,
    mut v_x_3329_: *mut LeanObject,
    mut v_kp_3330_: *mut LeanObject,
    mut v_a_3331_: *mut LeanObject,
    mut v_a_3332_: *mut LeanObject,
    mut v_a_3333_: *mut LeanObject,
    mut v_a_3334_: *mut LeanObject,
    mut v_a_3335_: *mut LeanObject,
    mut v_a_3336_: *mut LeanObject,
    mut v_a_3337_: *mut LeanObject,
    mut v_a_3338_: *mut LeanObject,
    mut v_a_3339_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3341_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_n_3342_: *mut LeanObject,
    mut v_x_3343_: *mut LeanObject,
    mut v_goal_3344_: *mut LeanObject,
    mut v_x_3345_: *mut LeanObject,
    mut v_kp_3346_: *mut LeanObject,
    mut v_a_3347_: *mut LeanObject,
    mut v_a_3348_: *mut LeanObject,
    mut v_a_3349_: *mut LeanObject,
    mut v_a_3350_: *mut LeanObject,
    mut v_a_3351_: *mut LeanObject,
    mut v_a_3352_: *mut LeanObject,
    mut v_a_3353_: *mut LeanObject,
    mut v_a_3354_: *mut LeanObject,
    mut v_a_3355_: *mut LeanObject,
    mut v_a_3356_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3357_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_3355_);
    lean_dec_ref(v_a_3354_);
    lean_dec(v_a_3353_);
    lean_dec_ref(v_a_3352_);
    lean_dec(v_a_3351_);
    lean_dec_ref(v_a_3350_);
    lean_dec(v_a_3349_);
    lean_dec_ref(v_a_3348_);
    lean_dec(v_a_3347_);
    lean_dec_ref(v_x_3345_);
    lean_dec(v_n_3342_);
    return v_res_3357_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_loopRef___redArg___lam__0___boxed(
    mut v_n_3358_: *mut LeanObject,
    mut v_x_3359_: *mut LeanObject,
    mut v_kp_3360_: *mut LeanObject,
    mut v_goal_x27_3361_: *mut LeanObject,
    mut v___y_3362_: *mut LeanObject,
    mut v___y_3363_: *mut LeanObject,
    mut v___y_3364_: *mut LeanObject,
    mut v___y_3365_: *mut LeanObject,
    mut v___y_3366_: *mut LeanObject,
    mut v___y_3367_: *mut LeanObject,
    mut v___y_3368_: *mut LeanObject,
    mut v___y_3369_: *mut LeanObject,
    mut v___y_3370_: *mut LeanObject,
    mut v___y_3371_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3372_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_3370_);
    lean_dec_ref(v___y_3369_);
    lean_dec(v___y_3368_);
    lean_dec_ref(v___y_3367_);
    lean_dec(v___y_3366_);
    lean_dec_ref(v___y_3365_);
    lean_dec(v___y_3364_);
    lean_dec_ref(v___y_3363_);
    lean_dec(v___y_3362_);
    lean_dec(v_n_3358_);
    return v_res_3372_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_loopRef___redArg(
    mut v_n_3373_: *mut LeanObject,
    mut v_x_3374_: *mut LeanObject,
    mut v_goal_3375_: *mut LeanObject,
    mut v_kp_3376_: *mut LeanObject,
    mut v_a_3377_: *mut LeanObject,
    mut v_a_3378_: *mut LeanObject,
    mut v_a_3379_: *mut LeanObject,
    mut v_a_3380_: *mut LeanObject,
    mut v_a_3381_: *mut LeanObject,
    mut v_a_3382_: *mut LeanObject,
    mut v_a_3383_: *mut LeanObject,
    mut v_a_3384_: *mut LeanObject,
    mut v_a_3385_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_3387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_3388_: u8 = 0;
    v_zero_3387_ = lean_unsigned_to_nat(0);
    v_isZero_3388_ = lean_nat_dec_eq(v_n_3373_, v_zero_3387_);
    if v_isZero_3388_ == 1 {
        let mut v___x_3389_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_x_3374_);
        lean_inc(v_a_3385_);
        lean_inc_ref(v_a_3384_);
        lean_inc(v_a_3383_);
        lean_inc_ref(v_a_3382_);
        lean_inc(v_a_3381_);
        lean_inc_ref(v_a_3380_);
        lean_inc(v_a_3379_);
        lean_inc_ref(v_a_3378_);
        lean_inc(v_a_3377_);
        v___x_3389_ = lean_apply_11(
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
            lean_box(0),
        );
        return v___x_3389_;
    } else {
        let mut v_one_3390_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_3391_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_3392_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3393_: *mut LeanObject = core::ptr::null_mut();
        v_one_3390_ = lean_unsigned_to_nat(1);
        v_n_3391_ = lean_nat_sub(v_n_3373_, v_one_3390_);
        lean_inc_ref(v_kp_3376_);
        lean_inc_ref(v_x_3374_);
        v___f_3392_ = lean_alloc_closure(
            l_Lean_Meta_Grind_Action_loopRef___redArg___lam__0___boxed as *mut core::ffi::c_void,
            14,
            3,
        );
        lean_closure_set(v___f_3392_, 0, v_n_3391_);
        lean_closure_set(v___f_3392_, 1, v_x_3374_);
        lean_closure_set(v___f_3392_, 2, v_kp_3376_);
        lean_inc(v_a_3385_);
        lean_inc_ref(v_a_3384_);
        lean_inc(v_a_3383_);
        lean_inc_ref(v_a_3382_);
        lean_inc(v_a_3381_);
        lean_inc_ref(v_a_3380_);
        lean_inc(v_a_3379_);
        lean_inc_ref(v_a_3378_);
        lean_inc(v_a_3377_);
        v___x_3393_ = lean_apply_13(
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
            lean_box(0),
        );
        return v___x_3393_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Action_loopRef___redArg___lam__0(
    mut v_n_3394_: *mut LeanObject,
    mut v_x_3395_: *mut LeanObject,
    mut v_kp_3396_: *mut LeanObject,
    mut v_goal_x27_3397_: *mut LeanObject,
    mut v___y_3398_: *mut LeanObject,
    mut v___y_3399_: *mut LeanObject,
    mut v___y_3400_: *mut LeanObject,
    mut v___y_3401_: *mut LeanObject,
    mut v___y_3402_: *mut LeanObject,
    mut v___y_3403_: *mut LeanObject,
    mut v___y_3404_: *mut LeanObject,
    mut v___y_3405_: *mut LeanObject,
    mut v___y_3406_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3408_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_n_3409_: *mut LeanObject,
    mut v_x_3410_: *mut LeanObject,
    mut v_goal_3411_: *mut LeanObject,
    mut v_kp_3412_: *mut LeanObject,
    mut v_a_3413_: *mut LeanObject,
    mut v_a_3414_: *mut LeanObject,
    mut v_a_3415_: *mut LeanObject,
    mut v_a_3416_: *mut LeanObject,
    mut v_a_3417_: *mut LeanObject,
    mut v_a_3418_: *mut LeanObject,
    mut v_a_3419_: *mut LeanObject,
    mut v_a_3420_: *mut LeanObject,
    mut v_a_3421_: *mut LeanObject,
    mut v_a_3422_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3423_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_3421_);
    lean_dec_ref(v_a_3420_);
    lean_dec(v_a_3419_);
    lean_dec_ref(v_a_3418_);
    lean_dec(v_a_3417_);
    lean_dec_ref(v_a_3416_);
    lean_dec(v_a_3415_);
    lean_dec_ref(v_a_3414_);
    lean_dec(v_a_3413_);
    lean_dec(v_n_3409_);
    return v_res_3423_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_loopRef(
    mut v_n_3424_: *mut LeanObject,
    mut v_x_3425_: *mut LeanObject,
    mut v_goal_3426_: *mut LeanObject,
    mut v_x_3427_: *mut LeanObject,
    mut v_kp_3428_: *mut LeanObject,
    mut v_a_3429_: *mut LeanObject,
    mut v_a_3430_: *mut LeanObject,
    mut v_a_3431_: *mut LeanObject,
    mut v_a_3432_: *mut LeanObject,
    mut v_a_3433_: *mut LeanObject,
    mut v_a_3434_: *mut LeanObject,
    mut v_a_3435_: *mut LeanObject,
    mut v_a_3436_: *mut LeanObject,
    mut v_a_3437_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3439_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_n_3440_: *mut LeanObject,
    mut v_x_3441_: *mut LeanObject,
    mut v_goal_3442_: *mut LeanObject,
    mut v_x_3443_: *mut LeanObject,
    mut v_kp_3444_: *mut LeanObject,
    mut v_a_3445_: *mut LeanObject,
    mut v_a_3446_: *mut LeanObject,
    mut v_a_3447_: *mut LeanObject,
    mut v_a_3448_: *mut LeanObject,
    mut v_a_3449_: *mut LeanObject,
    mut v_a_3450_: *mut LeanObject,
    mut v_a_3451_: *mut LeanObject,
    mut v_a_3452_: *mut LeanObject,
    mut v_a_3453_: *mut LeanObject,
    mut v_a_3454_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3455_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_3453_);
    lean_dec_ref(v_a_3452_);
    lean_dec(v_a_3451_);
    lean_dec_ref(v_a_3450_);
    lean_dec(v_a_3449_);
    lean_dec_ref(v_a_3448_);
    lean_dec(v_a_3447_);
    lean_dec_ref(v_a_3446_);
    lean_dec(v_a_3445_);
    lean_dec_ref(v_x_3443_);
    lean_dec(v_n_3440_);
    return v_res_3455_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_run___lam__0(
    mut v_goal_3467_: *mut LeanObject,
    mut v___y_3468_: *mut LeanObject,
    mut v___y_3469_: *mut LeanObject,
    mut v___y_3470_: *mut LeanObject,
    mut v___y_3471_: *mut LeanObject,
    mut v___y_3472_: *mut LeanObject,
    mut v___y_3473_: *mut LeanObject,
    mut v___y_3474_: *mut LeanObject,
    mut v___y_3475_: *mut LeanObject,
    mut v___y_3476_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toGoalState_3478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inconsistent_3479_: u8 = 0;
    let mut v_mvarId_3480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3487_: u8 = 0;
    let mut v___x_3489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trace_3495_: u8 = 0;
    let mut v_useSorry_3496_: u8 = 0;
    let mut v___x_3498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3499_: u8 = 0;
    let mut v___x_3500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3503_: u8 = 0;
    let mut v_ref_3504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3518_: u8 = 0;
    let mut v_unused_3519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3523_: u8 = 0;
    let mut v___x_3525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3527_: u8 = 0;
    let mut v_isSharedCheck_3528_: u8 = 0;
    let mut v_unused_3529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3531_: u8 = 0;
    let mut v_a_3532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3535_: u8 = 0;
    let mut v___x_3537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3539_: u8 = 0;
    let mut v_a_3540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3543_: u8 = 0;
    let mut v___x_3545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3547_: u8 = 0;
    let mut v___x_3548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toGoalState_3478_ = lean_ctor_get(v_goal_3467_, 0);
                v_inconsistent_3479_ = lean_ctor_get_uint8(
                    v_toGoalState_3478_,
                    (core::mem::size_of::<*mut LeanObject>() * 17) as u32,
                );
                if v_inconsistent_3479_ == 0 {
                    v_mvarId_3480_ = lean_ctor_get(v_goal_3467_, 1);
                    v___x_3481_ = l_Lean_Meta_Grind_getConfig___redArg(v___y_3469_);
                    if lean_obj_tag(v___x_3481_) == 0 {
                        v_a_3482_ = lean_ctor_get(v___x_3481_, 0);
                        lean_inc(v_a_3482_);
                        lean_dec_ref_known(v___x_3481_, 1);
                        v___x_3483_ = l_Lean_Meta_Grind_getConfig___redArg(v___y_3469_);
                        if lean_obj_tag(v___x_3483_) == 0 {
                            v_a_3484_ = lean_ctor_get(v___x_3483_, 0);
                            v_isSharedCheck_3531_ = (!lean_is_exclusive(v___x_3483_)) as u8;
                            if v_isSharedCheck_3531_ == 0 {
                                v___x_3486_ = v___x_3483_;
                                v_isShared_3487_ = v_isSharedCheck_3531_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_3484_);
                                lean_dec(v___x_3483_);
                                v___x_3486_ = lean_box(0);
                                v_isShared_3487_ = v_isSharedCheck_3531_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_3482_);
                            lean_dec_ref(v_goal_3467_);
                            v_a_3532_ = lean_ctor_get(v___x_3483_, 0);
                            v_isSharedCheck_3539_ = (!lean_is_exclusive(v___x_3483_)) as u8;
                            if v_isSharedCheck_3539_ == 0 {
                                v___x_3534_ = v___x_3483_;
                                v_isShared_3535_ = v_isSharedCheck_3539_;
                                state = 10;
                                continue;
                            } else {
                                lean_inc(v_a_3532_);
                                lean_dec(v___x_3483_);
                                v___x_3534_ = lean_box(0);
                                v_isShared_3535_ = v_isSharedCheck_3539_;
                                state = 10;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_goal_3467_);
                        v_a_3540_ = lean_ctor_get(v___x_3481_, 0);
                        v_isSharedCheck_3547_ = (!lean_is_exclusive(v___x_3481_)) as u8;
                        if v_isSharedCheck_3547_ == 0 {
                            v___x_3542_ = v___x_3481_;
                            v_isShared_3543_ = v_isSharedCheck_3547_;
                            state = 12;
                            continue;
                        } else {
                            lean_inc(v_a_3540_);
                            lean_dec(v___x_3481_);
                            v___x_3542_ = lean_box(0);
                            v_isShared_3543_ = v_isSharedCheck_3547_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_goal_3467_);
                    v___x_3548_ = l_Lean_Meta_Grind_Action_done___redArg___closed__0;
                    v___x_3549_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3549_, 0, v___x_3548_);
                    return v___x_3549_;
                }
            }
            1 => {
                v_trace_3495_ = lean_ctor_get_uint8(
                    v_a_3482_,
                    (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                );
                lean_dec(v_a_3482_);
                if v_trace_3495_ == 0 {
                    lean_dec(v_a_3484_);
                    state = 2;
                    continue;
                } else {
                    v_useSorry_3496_ = lean_ctor_get_uint8(
                        v_a_3484_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 28) as u32,
                    );
                    lean_dec(v_a_3484_);
                    if v_useSorry_3496_ == 0 {
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_mvarId_3480_);
                        lean_del_object(v___x_3486_);
                        v_isSharedCheck_3528_ = (!lean_is_exclusive(v_goal_3467_)) as u8;
                        if v_isSharedCheck_3528_ == 0 {
                            v_unused_3529_ = lean_ctor_get(v_goal_3467_, 1);
                            lean_dec(v_unused_3529_);
                            v_unused_3530_ = lean_ctor_get(v_goal_3467_, 0);
                            lean_dec(v_unused_3530_);
                            v___x_3498_ = v_goal_3467_;
                            v_isShared_3499_ = v_isSharedCheck_3528_;
                            state = 4;
                            continue;
                        } else {
                            lean_dec(v_goal_3467_);
                            v___x_3498_ = lean_box(0);
                            v_isShared_3499_ = v_isSharedCheck_3528_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v___x_3489_ = lean_box(0);
                v___x_3490_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3490_, 0, v_goal_3467_);
                lean_ctor_set(v___x_3490_, 1, v___x_3489_);
                v___x_3491_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3491_, 0, v___x_3490_);
                if v_isShared_3487_ == 0 {
                    lean_ctor_set(v___x_3486_, 0, v___x_3491_);
                    v___x_3493_ = v___x_3486_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3494_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3494_, 0, v___x_3491_);
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
                if lean_obj_tag(v___x_3500_) == 0 {
                    v_isSharedCheck_3518_ = (!lean_is_exclusive(v___x_3500_)) as u8;
                    if v_isSharedCheck_3518_ == 0 {
                        v_unused_3519_ = lean_ctor_get(v___x_3500_, 0);
                        lean_dec(v_unused_3519_);
                        v___x_3502_ = v___x_3500_;
                        v_isShared_3503_ = v_isSharedCheck_3518_;
                        state = 5;
                        continue;
                    } else {
                        lean_dec(v___x_3500_);
                        v___x_3502_ = lean_box(0);
                        v_isShared_3503_ = v_isSharedCheck_3518_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3498_);
                    v_a_3520_ = lean_ctor_get(v___x_3500_, 0);
                    v_isSharedCheck_3527_ = (!lean_is_exclusive(v___x_3500_)) as u8;
                    if v_isSharedCheck_3527_ == 0 {
                        v___x_3522_ = v___x_3500_;
                        v_isShared_3523_ = v_isSharedCheck_3527_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_3520_);
                        lean_dec(v___x_3500_);
                        v___x_3522_ = lean_box(0);
                        v_isShared_3523_ = v_isSharedCheck_3527_;
                        state = 8;
                        continue;
                    }
                }
            }
            5 => {
                v_ref_3504_ = lean_ctor_get(v___y_3475_, 5);
                v___x_3505_ = l_Lean_SourceInfo_fromRef(v_ref_3504_, v_inconsistent_3479_);
                v___x_3506_ = l_Lean_Meta_Grind_Action_run___lam__0___closed__4;
                v___x_3507_ = l_Lean_Meta_Grind_Action_run___lam__0___closed__5;
                lean_inc(v___x_3505_);
                if v_isShared_3499_ == 0 {
                    lean_ctor_set_tag(v___x_3498_, 2);
                    lean_ctor_set(v___x_3498_, 1, v___x_3506_);
                    lean_ctor_set(v___x_3498_, 0, v___x_3505_);
                    v___x_3509_ = v___x_3498_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3517_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3517_, 0, v___x_3505_);
                    lean_ctor_set(v_reuseFailAlloc_3517_, 1, v___x_3506_);
                    v___x_3509_ = v_reuseFailAlloc_3517_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_3510_ = l_Lean_Syntax_node1(v___x_3505_, v___x_3507_, v___x_3509_);
                v___x_3511_ = lean_box(0);
                v___x_3512_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3512_, 0, v___x_3510_);
                lean_ctor_set(v___x_3512_, 1, v___x_3511_);
                v___x_3513_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3513_, 0, v___x_3512_);
                if v_isShared_3503_ == 0 {
                    lean_ctor_set(v___x_3502_, 0, v___x_3513_);
                    v___x_3515_ = v___x_3502_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3516_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3516_, 0, v___x_3513_);
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
                    v_reuseFailAlloc_3526_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3526_, 0, v_a_3520_);
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
                    v_reuseFailAlloc_3538_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3538_, 0, v_a_3532_);
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
                    v_reuseFailAlloc_3546_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3546_, 0, v_a_3540_);
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
    mut v_goal_3550_: *mut LeanObject,
    mut v___y_3551_: *mut LeanObject,
    mut v___y_3552_: *mut LeanObject,
    mut v___y_3553_: *mut LeanObject,
    mut v___y_3554_: *mut LeanObject,
    mut v___y_3555_: *mut LeanObject,
    mut v___y_3556_: *mut LeanObject,
    mut v___y_3557_: *mut LeanObject,
    mut v___y_3558_: *mut LeanObject,
    mut v___y_3559_: *mut LeanObject,
    mut v___y_3560_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3561_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_3559_);
    lean_dec_ref(v___y_3558_);
    lean_dec(v___y_3557_);
    lean_dec_ref(v___y_3556_);
    lean_dec(v___y_3555_);
    lean_dec_ref(v___y_3554_);
    lean_dec(v___y_3553_);
    lean_dec_ref(v___y_3552_);
    lean_dec(v___y_3551_);
    return v_res_3561_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_run(
    mut v_goal_3563_: *mut LeanObject,
    mut v_a_3564_: *mut LeanObject,
    mut v_a_3565_: *mut LeanObject,
    mut v_a_3566_: *mut LeanObject,
    mut v_a_3567_: *mut LeanObject,
    mut v_a_3568_: *mut LeanObject,
    mut v_a_3569_: *mut LeanObject,
    mut v_a_3570_: *mut LeanObject,
    mut v_a_3571_: *mut LeanObject,
    mut v_a_3572_: *mut LeanObject,
    mut v_a_3573_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_3575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut LeanObject = core::ptr::null_mut();
    v_k_3575_ = l_Lean_Meta_Grind_Action_run___closed__0;
    lean_inc(v_a_3573_);
    lean_inc_ref(v_a_3572_);
    lean_inc(v_a_3571_);
    lean_inc_ref(v_a_3570_);
    lean_inc(v_a_3569_);
    lean_inc_ref(v_a_3568_);
    lean_inc(v_a_3567_);
    lean_inc_ref(v_a_3566_);
    lean_inc(v_a_3565_);
    v___x_3576_ = lean_apply_13(
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
        lean_box(0),
    );
    return v___x_3576_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_run___boxed(
    mut v_goal_3577_: *mut LeanObject,
    mut v_a_3578_: *mut LeanObject,
    mut v_a_3579_: *mut LeanObject,
    mut v_a_3580_: *mut LeanObject,
    mut v_a_3581_: *mut LeanObject,
    mut v_a_3582_: *mut LeanObject,
    mut v_a_3583_: *mut LeanObject,
    mut v_a_3584_: *mut LeanObject,
    mut v_a_3585_: *mut LeanObject,
    mut v_a_3586_: *mut LeanObject,
    mut v_a_3587_: *mut LeanObject,
    mut v_a_3588_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3589_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_3587_);
    lean_dec_ref(v_a_3586_);
    lean_dec(v_a_3585_);
    lean_dec_ref(v_a_3584_);
    lean_dec(v_a_3583_);
    lean_dec_ref(v_a_3582_);
    lean_dec(v_a_3581_);
    lean_dec_ref(v_a_3580_);
    lean_dec(v_a_3579_);
    return v_res_3589_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_skipIfNA___redArg(
    mut v_x_3590_: *mut LeanObject,
    mut v_goal_3591_: *mut LeanObject,
    mut v_kp_3592_: *mut LeanObject,
    mut v_a_3593_: *mut LeanObject,
    mut v_a_3594_: *mut LeanObject,
    mut v_a_3595_: *mut LeanObject,
    mut v_a_3596_: *mut LeanObject,
    mut v_a_3597_: *mut LeanObject,
    mut v_a_3598_: *mut LeanObject,
    mut v_a_3599_: *mut LeanObject,
    mut v_a_3600_: *mut LeanObject,
    mut v_a_3601_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3603_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_3601_);
    lean_inc_ref(v_a_3600_);
    lean_inc(v_a_3599_);
    lean_inc_ref(v_a_3598_);
    lean_inc(v_a_3597_);
    lean_inc_ref(v_a_3596_);
    lean_inc(v_a_3595_);
    lean_inc_ref(v_a_3594_);
    lean_inc(v_a_3593_);
    lean_inc_ref(v_kp_3592_);
    v___x_3603_ = lean_apply_13(
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
        lean_box(0),
    );
    return v___x_3603_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_skipIfNA___redArg___boxed(
    mut v_x_3604_: *mut LeanObject,
    mut v_goal_3605_: *mut LeanObject,
    mut v_kp_3606_: *mut LeanObject,
    mut v_a_3607_: *mut LeanObject,
    mut v_a_3608_: *mut LeanObject,
    mut v_a_3609_: *mut LeanObject,
    mut v_a_3610_: *mut LeanObject,
    mut v_a_3611_: *mut LeanObject,
    mut v_a_3612_: *mut LeanObject,
    mut v_a_3613_: *mut LeanObject,
    mut v_a_3614_: *mut LeanObject,
    mut v_a_3615_: *mut LeanObject,
    mut v_a_3616_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3617_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_3615_);
    lean_dec_ref(v_a_3614_);
    lean_dec(v_a_3613_);
    lean_dec_ref(v_a_3612_);
    lean_dec(v_a_3611_);
    lean_dec_ref(v_a_3610_);
    lean_dec(v_a_3609_);
    lean_dec_ref(v_a_3608_);
    lean_dec(v_a_3607_);
    return v_res_3617_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_skipIfNA(
    mut v_x_3618_: *mut LeanObject,
    mut v_goal_3619_: *mut LeanObject,
    mut v_x_3620_: *mut LeanObject,
    mut v_kp_3621_: *mut LeanObject,
    mut v_a_3622_: *mut LeanObject,
    mut v_a_3623_: *mut LeanObject,
    mut v_a_3624_: *mut LeanObject,
    mut v_a_3625_: *mut LeanObject,
    mut v_a_3626_: *mut LeanObject,
    mut v_a_3627_: *mut LeanObject,
    mut v_a_3628_: *mut LeanObject,
    mut v_a_3629_: *mut LeanObject,
    mut v_a_3630_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3632_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_3630_);
    lean_inc_ref(v_a_3629_);
    lean_inc(v_a_3628_);
    lean_inc_ref(v_a_3627_);
    lean_inc(v_a_3626_);
    lean_inc_ref(v_a_3625_);
    lean_inc(v_a_3624_);
    lean_inc_ref(v_a_3623_);
    lean_inc(v_a_3622_);
    lean_inc_ref(v_kp_3621_);
    v___x_3632_ = lean_apply_13(
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
        lean_box(0),
    );
    return v___x_3632_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_skipIfNA___boxed(
    mut v_x_3633_: *mut LeanObject,
    mut v_goal_3634_: *mut LeanObject,
    mut v_x_3635_: *mut LeanObject,
    mut v_kp_3636_: *mut LeanObject,
    mut v_a_3637_: *mut LeanObject,
    mut v_a_3638_: *mut LeanObject,
    mut v_a_3639_: *mut LeanObject,
    mut v_a_3640_: *mut LeanObject,
    mut v_a_3641_: *mut LeanObject,
    mut v_a_3642_: *mut LeanObject,
    mut v_a_3643_: *mut LeanObject,
    mut v_a_3644_: *mut LeanObject,
    mut v_a_3645_: *mut LeanObject,
    mut v_a_3646_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3647_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_3645_);
    lean_dec_ref(v_a_3644_);
    lean_dec(v_a_3643_);
    lean_dec_ref(v_a_3642_);
    lean_dec(v_a_3641_);
    lean_dec_ref(v_a_3640_);
    lean_dec(v_a_3639_);
    lean_dec_ref(v_a_3638_);
    lean_dec(v_a_3637_);
    lean_dec_ref(v_x_3635_);
    return v_res_3647_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_mkGrindStep(
    mut v_t_3664_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut LeanObject = core::ptr::null_mut();
    v___x_3665_ = l_Lean_Meta_Grind_Action_mkGrindStep___closed__1;
    v___x_3666_ = lean_box(2);
    v___x_3667_ = l_Lean_Meta_Grind_Action_mkGrindStep___closed__5;
    v___x_3668_ = lean_unsigned_to_nat(2);
    v___x_3669_ = lean_mk_empty_array_with_capacity(v___x_3668_);
    v___x_3670_ = lean_array_push(v___x_3669_, v_t_3664_);
    v___x_3671_ = lean_array_push(v___x_3670_, v___x_3667_);
    v___x_3672_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_3672_, 0, v___x_3666_);
    lean_ctor_set(v___x_3672_, 1, v___x_3665_);
    lean_ctor_set(v___x_3672_, 2, v___x_3671_);
    return v___x_3672_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_TGrindStep_getTactic(
    mut v_x_3673_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: u8 = 0;
    v___x_3674_ = l_Lean_Meta_Grind_Action_mkGrindStep___closed__1;
    lean_inc(v_x_3673_);
    v___x_3675_ = l_Lean_Syntax_isOfKind(v_x_3673_, v___x_3674_);
    if v___x_3675_ == 0 {
        let mut v___x_3676_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_3673_);
        v___x_3676_ = l_Lean_Meta_Grind_Action_mkGrindStep___closed__5;
        return v___x_3676_;
    } else {
        let mut v___x_3677_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tac_3678_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3679_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3680_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3681_: u8 = 0;
        v___x_3677_ = lean_unsigned_to_nat(0);
        v_tac_3678_ = l_Lean_Syntax_getArg(v_x_3673_, v___x_3677_);
        v___x_3679_ = lean_unsigned_to_nat(1);
        v___x_3680_ = l_Lean_Syntax_getArg(v_x_3673_, v___x_3679_);
        lean_dec(v_x_3673_);
        v___x_3681_ = l_Lean_Syntax_isNone(v___x_3680_);
        if v___x_3681_ == 0 {
            let mut v___x_3682_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3683_: u8 = 0;
            v___x_3682_ = lean_unsigned_to_nat(2);
            lean_inc(v___x_3680_);
            v___x_3683_ = l_Lean_Syntax_matchesNull(v___x_3680_, v___x_3682_);
            if v___x_3683_ == 0 {
                let mut v___x_3684_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___x_3680_);
                lean_dec(v_tac_3678_);
                v___x_3684_ = l_Lean_Meta_Grind_Action_mkGrindStep___closed__5;
                return v___x_3684_;
            } else {
                let mut v___x_3685_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3686_: u8 = 0;
                v___x_3685_ = l_Lean_Syntax_getArg(v___x_3680_, v___x_3679_);
                lean_dec(v___x_3680_);
                v___x_3686_ = l_Lean_Syntax_matchesNull(v___x_3685_, v___x_3679_);
                if v___x_3686_ == 0 {
                    let mut v___x_3687_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec(v_tac_3678_);
                    v___x_3687_ = l_Lean_Meta_Grind_Action_mkGrindStep___closed__5;
                    return v___x_3687_;
                } else {
                    return v_tac_3678_;
                }
            }
        } else {
            lean_dec(v___x_3680_);
            return v_tac_3678_;
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Grind_Action_mkGrindSeq_spec__0(
    mut v_a_3688_: *mut LeanObject,
    mut v_a_3689_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3695_: u8 = 0;
    let mut v___x_3696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3701_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_3688_) == 0 {
                    v___x_3690_ = l_List_reverse___redArg(v_a_3689_);
                    return v___x_3690_;
                } else {
                    v_head_3691_ = lean_ctor_get(v_a_3688_, 0);
                    v_tail_3692_ = lean_ctor_get(v_a_3688_, 1);
                    v_isSharedCheck_3701_ = (!lean_is_exclusive(v_a_3688_)) as u8;
                    if v_isSharedCheck_3701_ == 0 {
                        v___x_3694_ = v_a_3688_;
                        v_isShared_3695_ = v_isSharedCheck_3701_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3692_);
                        lean_inc(v_head_3691_);
                        lean_dec(v_a_3688_);
                        v___x_3694_ = lean_box(0);
                        v_isShared_3695_ = v_isSharedCheck_3701_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3696_ = l_Lean_Meta_Grind_Action_mkGrindStep(v_head_3691_);
                if v_isShared_3695_ == 0 {
                    lean_ctor_set(v___x_3694_, 1, v_a_3689_);
                    lean_ctor_set(v___x_3694_, 0, v___x_3696_);
                    v___x_3698_ = v___x_3694_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3700_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3700_, 0, v___x_3696_);
                    lean_ctor_set(v_reuseFailAlloc_3700_, 1, v_a_3689_);
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
    mut v_s_3722_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_3724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_3728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: *mut LeanObject = core::ptr::null_mut();
    v___x_3723_ = lean_box(0);
    v_s_3724_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Action_mkGrindSeq_spec__0(
        v_s_3722_,
        v___x_3723_,
    );
    v___x_3725_ = l_Lean_Meta_Grind_Action_mkGrindStep___closed__4;
    v___x_3726_ = lean_box(2);
    v___x_3727_ = l_Lean_Meta_Grind_Action_mkGrindSeq___closed__1;
    v_s_3728_ = l_List_intersperseTR___redArg(v___x_3727_, v_s_3724_);
    v___x_3729_ = l_Lean_Meta_Grind_Action_mkGrindSeq___closed__3;
    v___x_3730_ = l_Lean_Meta_Grind_Action_mkGrindSeq___closed__5;
    v___x_3731_ = lean_array_mk(v_s_3728_);
    v___x_3732_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_3732_, 0, v___x_3726_);
    lean_ctor_set(v___x_3732_, 1, v___x_3725_);
    lean_ctor_set(v___x_3732_, 2, v___x_3731_);
    v___x_3733_ = lean_unsigned_to_nat(1);
    v___x_3734_ = lean_mk_empty_array_with_capacity(v___x_3733_);
    lean_inc_ref(v___x_3734_);
    v___x_3735_ = lean_array_push(v___x_3734_, v___x_3732_);
    v___x_3736_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_3736_, 0, v___x_3726_);
    lean_ctor_set(v___x_3736_, 1, v___x_3730_);
    lean_ctor_set(v___x_3736_, 2, v___x_3735_);
    v___x_3737_ = lean_array_push(v___x_3734_, v___x_3736_);
    v___x_3738_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_3738_, 0, v___x_3726_);
    lean_ctor_set(v___x_3738_, 1, v___x_3729_);
    lean_ctor_set(v___x_3738_, 2, v___x_3737_);
    return v___x_3738_;
}
pub unsafe fn l_List_beq___at___00Lean_Meta_Grind_Action_mkGrindNext_spec__0(
    mut v_x_3739_: *mut LeanObject,
    mut v_x_3740_: *mut LeanObject,
) -> u8 {
    let mut v___x_3741_: u8 = 0;
    let mut v___x_3742_: u8 = 0;
    let mut v___x_3743_: u8 = 0;
    let mut v_head_3744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3739_) == 0 {
                    if lean_obj_tag(v_x_3740_) == 0 {
                        v___x_3741_ = 1;
                        return v___x_3741_;
                    } else {
                        lean_dec_ref_known(v_x_3740_, 2);
                        v___x_3742_ = 0;
                        return v___x_3742_;
                    }
                } else {
                    if lean_obj_tag(v_x_3740_) == 0 {
                        lean_dec_ref_known(v_x_3739_, 2);
                        v___x_3743_ = 0;
                        return v___x_3743_;
                    } else {
                        v_head_3744_ = lean_ctor_get(v_x_3739_, 0);
                        lean_inc(v_head_3744_);
                        v_tail_3745_ = lean_ctor_get(v_x_3739_, 1);
                        lean_inc(v_tail_3745_);
                        lean_dec_ref_known(v_x_3739_, 2);
                        v_head_3746_ = lean_ctor_get(v_x_3740_, 0);
                        lean_inc(v_head_3746_);
                        v_tail_3747_ = lean_ctor_get(v_x_3740_, 1);
                        lean_inc(v_tail_3747_);
                        lean_dec_ref_known(v_x_3740_, 2);
                        v___x_3748_ = l_Lean_Syntax_structEq(v_head_3744_, v_head_3746_);
                        if v___x_3748_ == 0 {
                            lean_dec(v_tail_3747_);
                            lean_dec(v_tail_3745_);
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
    mut v_x_3750_: *mut LeanObject,
    mut v_x_3751_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3752_: u8 = 0;
    let mut v_r_3753_: *mut LeanObject = core::ptr::null_mut();
    v_res_3752_ =
        l_List_beq___at___00Lean_Meta_Grind_Action_mkGrindNext_spec__0(v_x_3750_, v_x_3751_);
    v_r_3753_ = lean_box((v_res_3752_) as usize);
    return v_r_3753_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_mkGrindNext___redArg(
    mut v_s_3769_: *mut LeanObject,
    mut v_a_3770_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_s_3773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_3775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3776_: u8 = 0;
    let mut v___x_3777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: u8 = 0;
    let mut v_ref_3785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: u8 = 0;
    let mut v___x_3788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3783_ = lean_box(0);
                lean_inc(v_s_3769_);
                v___x_3784_ = l_List_beq___at___00Lean_Meta_Grind_Action_mkGrindNext_spec__0(
                    v_s_3769_,
                    v___x_3783_,
                );
                if v___x_3784_ == 0 {
                    v_ref_3785_ = lean_ctor_get(v_a_3770_, 5);
                    v_s_3773_ = v_s_3769_;
                    v_ref_3774_ = v_ref_3785_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v_s_3769_);
                    v_ref_3786_ = lean_ctor_get(v_a_3770_, 5);
                    v___x_3787_ = 0;
                    v___x_3788_ = l_Lean_SourceInfo_fromRef(v_ref_3786_, v___x_3787_);
                    v___x_3789_ = l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__3;
                    v___x_3790_ = l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__4;
                    lean_inc(v___x_3788_);
                    v___x_3791_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_3791_, 0, v___x_3788_);
                    lean_ctor_set(v___x_3791_, 1, v___x_3789_);
                    v___x_3792_ = l_Lean_Syntax_node1(v___x_3788_, v___x_3790_, v___x_3791_);
                    v___x_3793_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_3793_, 0, v___x_3792_);
                    lean_ctor_set(v___x_3793_, 1, v___x_3783_);
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
                lean_inc(v___x_3777_);
                v___x_3780_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3780_, 0, v___x_3777_);
                lean_ctor_set(v___x_3780_, 1, v___x_3779_);
                v___x_3781_ = l_Lean_Syntax_node2(v___x_3777_, v___x_3778_, v___x_3780_, v_s_3775_);
                v___x_3782_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3782_, 0, v___x_3781_);
                return v___x_3782_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Action_mkGrindNext___redArg___boxed(
    mut v_s_3794_: *mut LeanObject,
    mut v_a_3795_: *mut LeanObject,
    mut v_a_3796_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3797_: *mut LeanObject = core::ptr::null_mut();
    v_res_3797_ = l_Lean_Meta_Grind_Action_mkGrindNext___redArg(v_s_3794_, v_a_3795_);
    lean_dec_ref(v_a_3795_);
    return v_res_3797_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_mkGrindNext(
    mut v_s_3798_: *mut LeanObject,
    mut v_a_3799_: *mut LeanObject,
    mut v_a_3800_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3802_: *mut LeanObject = core::ptr::null_mut();
    v___x_3802_ = l_Lean_Meta_Grind_Action_mkGrindNext___redArg(v_s_3798_, v_a_3799_);
    return v___x_3802_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_mkGrindNext___boxed(
    mut v_s_3803_: *mut LeanObject,
    mut v_a_3804_: *mut LeanObject,
    mut v_a_3805_: *mut LeanObject,
    mut v_a_3806_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3807_: *mut LeanObject = core::ptr::null_mut();
    v_res_3807_ = l_Lean_Meta_Grind_Action_mkGrindNext(v_s_3803_, v_a_3804_, v_a_3805_);
    lean_dec(v_a_3805_);
    lean_dec_ref(v_a_3804_);
    return v_res_3807_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg(
    mut v_s_3824_: *mut LeanObject,
    mut v_a_3825_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_s_3828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_3830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: u8 = 0;
    let mut v___x_3832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: u8 = 0;
    let mut v_ref_3842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: u8 = 0;
    let mut v___x_3845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3840_ = lean_box(0);
                lean_inc(v_s_3824_);
                v___x_3841_ = l_List_beq___at___00Lean_Meta_Grind_Action_mkGrindNext_spec__0(
                    v_s_3824_,
                    v___x_3840_,
                );
                if v___x_3841_ == 0 {
                    v_ref_3842_ = lean_ctor_get(v_a_3825_, 5);
                    v_s_3828_ = v_s_3824_;
                    v_ref_3829_ = v_ref_3842_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v_s_3824_);
                    v_ref_3843_ = lean_ctor_get(v_a_3825_, 5);
                    v___x_3844_ = 0;
                    v___x_3845_ = l_Lean_SourceInfo_fromRef(v_ref_3843_, v___x_3844_);
                    v___x_3846_ = l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__4;
                    v___x_3847_ = l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__5;
                    lean_inc(v___x_3845_);
                    v___x_3848_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_3848_, 0, v___x_3845_);
                    lean_ctor_set(v___x_3848_, 1, v___x_3846_);
                    v___x_3849_ = l_Lean_Syntax_node1(v___x_3845_, v___x_3847_, v___x_3848_);
                    v___x_3850_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_3850_, 0, v___x_3849_);
                    lean_ctor_set(v___x_3850_, 1, v___x_3840_);
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
                lean_inc_n(v___x_3832_, 2);
                v___x_3835_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3835_, 0, v___x_3832_);
                lean_ctor_set(v___x_3835_, 1, v___x_3834_);
                v___x_3836_ = l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__3;
                v___x_3837_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3837_, 0, v___x_3832_);
                lean_ctor_set(v___x_3837_, 1, v___x_3836_);
                v___x_3838_ = l_Lean_Syntax_node3(
                    v___x_3832_,
                    v___x_3833_,
                    v___x_3835_,
                    v_s_3830_,
                    v___x_3837_,
                );
                v___x_3839_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3839_, 0, v___x_3838_);
                return v___x_3839_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___boxed(
    mut v_s_3851_: *mut LeanObject,
    mut v_a_3852_: *mut LeanObject,
    mut v_a_3853_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3854_: *mut LeanObject = core::ptr::null_mut();
    v_res_3854_ =
        l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg(
            v_s_3851_, v_a_3852_,
        );
    lean_dec_ref(v_a_3852_);
    return v_res_3854_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen(
    mut v_s_3855_: *mut LeanObject,
    mut v_a_3856_: *mut LeanObject,
    mut v_a_3857_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3859_: *mut LeanObject = core::ptr::null_mut();
    v___x_3859_ =
        l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg(
            v_s_3855_, v_a_3856_,
        );
    return v___x_3859_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___boxed(
    mut v_s_3860_: *mut LeanObject,
    mut v_a_3861_: *mut LeanObject,
    mut v_a_3862_: *mut LeanObject,
    mut v_a_3863_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3864_: *mut LeanObject = core::ptr::null_mut();
    v_res_3864_ = l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen(
        v_s_3860_, v_a_3861_, v_a_3862_,
    );
    lean_dec(v_a_3862_);
    lean_dec_ref(v_a_3861_);
    return v_res_3864_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_group___redArg(
    mut v_goal_3865_: *mut LeanObject,
    mut v_kp_3866_: *mut LeanObject,
    mut v_a_3867_: *mut LeanObject,
    mut v_a_3868_: *mut LeanObject,
    mut v_a_3869_: *mut LeanObject,
    mut v_a_3870_: *mut LeanObject,
    mut v_a_3871_: *mut LeanObject,
    mut v_a_3872_: *mut LeanObject,
    mut v_a_3873_: *mut LeanObject,
    mut v_a_3874_: *mut LeanObject,
    mut v_a_3875_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3883_: u8 = 0;
    let mut v_trace_3884_: u8 = 0;
    let mut v___x_3886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_seq_3888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3891_: u8 = 0;
    let mut v___x_3892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3896_: u8 = 0;
    let mut v___x_3897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3905_: u8 = 0;
    let mut v_isSharedCheck_3906_: u8 = 0;
    let mut v___x_3908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3910_: u8 = 0;
    let mut v_a_3911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3914_: u8 = 0;
    let mut v___x_3916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3918_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_a_3875_);
                lean_inc_ref(v_a_3874_);
                lean_inc(v_a_3873_);
                lean_inc_ref(v_a_3872_);
                lean_inc(v_a_3871_);
                lean_inc_ref(v_a_3870_);
                lean_inc(v_a_3869_);
                lean_inc_ref(v_a_3868_);
                lean_inc(v_a_3867_);
                v___x_3877_ = lean_apply_11(
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
                    lean_box(0),
                );
                if lean_obj_tag(v___x_3877_) == 0 {
                    v_a_3878_ = lean_ctor_get(v___x_3877_, 0);
                    lean_inc(v_a_3878_);
                    lean_dec_ref_known(v___x_3877_, 1);
                    v___x_3879_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_3868_);
                    if lean_obj_tag(v___x_3879_) == 0 {
                        v_a_3880_ = lean_ctor_get(v___x_3879_, 0);
                        v_isSharedCheck_3910_ = (!lean_is_exclusive(v___x_3879_)) as u8;
                        if v_isSharedCheck_3910_ == 0 {
                            v___x_3882_ = v___x_3879_;
                            v_isShared_3883_ = v_isSharedCheck_3910_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3880_);
                            lean_dec(v___x_3879_);
                            v___x_3882_ = lean_box(0);
                            v_isShared_3883_ = v_isSharedCheck_3910_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_3878_);
                        v_a_3911_ = lean_ctor_get(v___x_3879_, 0);
                        v_isSharedCheck_3918_ = (!lean_is_exclusive(v___x_3879_)) as u8;
                        if v_isSharedCheck_3918_ == 0 {
                            v___x_3913_ = v___x_3879_;
                            v_isShared_3914_ = v_isSharedCheck_3918_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_3911_);
                            lean_dec(v___x_3879_);
                            v___x_3913_ = lean_box(0);
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
                v_trace_3884_ = lean_ctor_get_uint8(
                    v_a_3880_,
                    (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                );
                lean_dec(v_a_3880_);
                if v_trace_3884_ == 0 {
                    if v_isShared_3883_ == 0 {
                        lean_ctor_set(v___x_3882_, 0, v_a_3878_);
                        v___x_3886_ = v___x_3882_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3887_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3887_, 0, v_a_3878_);
                        v___x_3886_ = v_reuseFailAlloc_3887_;
                        state = 2;
                        continue;
                    }
                } else {
                    if lean_obj_tag(v_a_3878_) == 0 {
                        lean_del_object(v___x_3882_);
                        v_seq_3888_ = lean_ctor_get(v_a_3878_, 0);
                        v_isSharedCheck_3906_ = (!lean_is_exclusive(v_a_3878_)) as u8;
                        if v_isSharedCheck_3906_ == 0 {
                            v___x_3890_ = v_a_3878_;
                            v_isShared_3891_ = v_isSharedCheck_3906_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_seq_3888_);
                            lean_dec(v_a_3878_);
                            v___x_3890_ = lean_box(0);
                            v_isShared_3891_ = v_isSharedCheck_3906_;
                            state = 3;
                            continue;
                        }
                    } else {
                        if v_isShared_3883_ == 0 {
                            lean_ctor_set(v___x_3882_, 0, v_a_3878_);
                            v___x_3908_ = v___x_3882_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_3909_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3909_, 0, v_a_3878_);
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
                v_a_3893_ = lean_ctor_get(v___x_3892_, 0);
                v_isSharedCheck_3905_ = (!lean_is_exclusive(v___x_3892_)) as u8;
                if v_isSharedCheck_3905_ == 0 {
                    v___x_3895_ = v___x_3892_;
                    v_isShared_3896_ = v_isSharedCheck_3905_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_a_3893_);
                    lean_dec(v___x_3892_);
                    v___x_3895_ = lean_box(0);
                    v_isShared_3896_ = v_isSharedCheck_3905_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3897_ = lean_box(0);
                v___x_3898_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3898_, 0, v_a_3893_);
                lean_ctor_set(v___x_3898_, 1, v___x_3897_);
                if v_isShared_3891_ == 0 {
                    lean_ctor_set(v___x_3890_, 0, v___x_3898_);
                    v___x_3900_ = v___x_3890_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3904_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3904_, 0, v___x_3898_);
                    v___x_3900_ = v_reuseFailAlloc_3904_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_3896_ == 0 {
                    lean_ctor_set(v___x_3895_, 0, v___x_3900_);
                    v___x_3902_ = v___x_3895_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3903_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3903_, 0, v___x_3900_);
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
                    v_reuseFailAlloc_3917_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3917_, 0, v_a_3911_);
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
    mut v_goal_3919_: *mut LeanObject,
    mut v_kp_3920_: *mut LeanObject,
    mut v_a_3921_: *mut LeanObject,
    mut v_a_3922_: *mut LeanObject,
    mut v_a_3923_: *mut LeanObject,
    mut v_a_3924_: *mut LeanObject,
    mut v_a_3925_: *mut LeanObject,
    mut v_a_3926_: *mut LeanObject,
    mut v_a_3927_: *mut LeanObject,
    mut v_a_3928_: *mut LeanObject,
    mut v_a_3929_: *mut LeanObject,
    mut v_a_3930_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3931_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_3929_);
    lean_dec_ref(v_a_3928_);
    lean_dec(v_a_3927_);
    lean_dec_ref(v_a_3926_);
    lean_dec(v_a_3925_);
    lean_dec_ref(v_a_3924_);
    lean_dec(v_a_3923_);
    lean_dec_ref(v_a_3922_);
    lean_dec(v_a_3921_);
    return v_res_3931_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_group(
    mut v_goal_3932_: *mut LeanObject,
    mut v_x_3933_: *mut LeanObject,
    mut v_kp_3934_: *mut LeanObject,
    mut v_a_3935_: *mut LeanObject,
    mut v_a_3936_: *mut LeanObject,
    mut v_a_3937_: *mut LeanObject,
    mut v_a_3938_: *mut LeanObject,
    mut v_a_3939_: *mut LeanObject,
    mut v_a_3940_: *mut LeanObject,
    mut v_a_3941_: *mut LeanObject,
    mut v_a_3942_: *mut LeanObject,
    mut v_a_3943_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3945_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_goal_3946_: *mut LeanObject,
    mut v_x_3947_: *mut LeanObject,
    mut v_kp_3948_: *mut LeanObject,
    mut v_a_3949_: *mut LeanObject,
    mut v_a_3950_: *mut LeanObject,
    mut v_a_3951_: *mut LeanObject,
    mut v_a_3952_: *mut LeanObject,
    mut v_a_3953_: *mut LeanObject,
    mut v_a_3954_: *mut LeanObject,
    mut v_a_3955_: *mut LeanObject,
    mut v_a_3956_: *mut LeanObject,
    mut v_a_3957_: *mut LeanObject,
    mut v_a_3958_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3959_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_3957_);
    lean_dec_ref(v_a_3956_);
    lean_dec(v_a_3955_);
    lean_dec_ref(v_a_3954_);
    lean_dec(v_a_3953_);
    lean_dec_ref(v_a_3952_);
    lean_dec(v_a_3951_);
    lean_dec_ref(v_a_3950_);
    lean_dec(v_a_3949_);
    lean_dec_ref(v_x_3947_);
    return v_res_3959_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Grind_Action_ungroup_spec__0(
    mut v_a_3960_: *mut LeanObject,
    mut v_a_3961_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3967_: u8 = 0;
    let mut v___x_3968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3973_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_3960_) == 0 {
                    v___x_3962_ = l_List_reverse___redArg(v_a_3961_);
                    return v___x_3962_;
                } else {
                    v_head_3963_ = lean_ctor_get(v_a_3960_, 0);
                    v_tail_3964_ = lean_ctor_get(v_a_3960_, 1);
                    v_isSharedCheck_3973_ = (!lean_is_exclusive(v_a_3960_)) as u8;
                    if v_isSharedCheck_3973_ == 0 {
                        v___x_3966_ = v_a_3960_;
                        v_isShared_3967_ = v_isSharedCheck_3973_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3964_);
                        lean_inc(v_head_3963_);
                        lean_dec(v_a_3960_);
                        v___x_3966_ = lean_box(0);
                        v_isShared_3967_ = v_isSharedCheck_3973_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3968_ = l_Lean_Meta_Grind_Action_TGrindStep_getTactic(v_head_3963_);
                if v_isShared_3967_ == 0 {
                    lean_ctor_set(v___x_3966_, 1, v_a_3961_);
                    lean_ctor_set(v___x_3966_, 0, v___x_3968_);
                    v___x_3970_ = v___x_3966_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3972_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3972_, 0, v___x_3968_);
                    lean_ctor_set(v_reuseFailAlloc_3972_, 1, v_a_3961_);
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
    mut v_goal_3981_: *mut LeanObject,
    mut v_kp_3982_: *mut LeanObject,
    mut v_a_3983_: *mut LeanObject,
    mut v_a_3984_: *mut LeanObject,
    mut v_a_3985_: *mut LeanObject,
    mut v_a_3986_: *mut LeanObject,
    mut v_a_3987_: *mut LeanObject,
    mut v_a_3988_: *mut LeanObject,
    mut v_a_3989_: *mut LeanObject,
    mut v_a_3990_: *mut LeanObject,
    mut v_a_3991_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3999_: u8 = 0;
    let mut v_trace_4000_: u8 = 0;
    let mut v___x_4002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_seq_4004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4008_: u8 = 0;
    let mut v___x_4009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: u8 = 0;
    let mut v___x_4012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: u8 = 0;
    let mut v___x_4019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: u8 = 0;
    let mut v___x_4026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4030_: u8 = 0;
    let mut v___x_4031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4042_: u8 = 0;
    let mut v_unused_4043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: u8 = 0;
    let mut v___x_4049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4054_: u8 = 0;
    let mut v___x_4056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: u8 = 0;
    let mut v___x_4062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4066_: u8 = 0;
    let mut v___x_4067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4078_: u8 = 0;
    let mut v_unused_4079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4089_: u8 = 0;
    let mut v_a_4090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4093_: u8 = 0;
    let mut v___x_4095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4097_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_a_3991_);
                lean_inc_ref(v_a_3990_);
                lean_inc(v_a_3989_);
                lean_inc_ref(v_a_3988_);
                lean_inc(v_a_3987_);
                lean_inc_ref(v_a_3986_);
                lean_inc(v_a_3985_);
                lean_inc_ref(v_a_3984_);
                lean_inc(v_a_3983_);
                v___x_3993_ = lean_apply_11(
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
                    lean_box(0),
                );
                if lean_obj_tag(v___x_3993_) == 0 {
                    v_a_3994_ = lean_ctor_get(v___x_3993_, 0);
                    lean_inc(v_a_3994_);
                    lean_dec_ref_known(v___x_3993_, 1);
                    v___x_3995_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_3984_);
                    if lean_obj_tag(v___x_3995_) == 0 {
                        v_a_3996_ = lean_ctor_get(v___x_3995_, 0);
                        v_isSharedCheck_4089_ = (!lean_is_exclusive(v___x_3995_)) as u8;
                        if v_isSharedCheck_4089_ == 0 {
                            v___x_3998_ = v___x_3995_;
                            v_isShared_3999_ = v_isSharedCheck_4089_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3996_);
                            lean_dec(v___x_3995_);
                            v___x_3998_ = lean_box(0);
                            v_isShared_3999_ = v_isSharedCheck_4089_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_3994_);
                        v_a_4090_ = lean_ctor_get(v___x_3995_, 0);
                        v_isSharedCheck_4097_ = (!lean_is_exclusive(v___x_3995_)) as u8;
                        if v_isSharedCheck_4097_ == 0 {
                            v___x_4092_ = v___x_3995_;
                            v_isShared_4093_ = v_isSharedCheck_4097_;
                            state = 18;
                            continue;
                        } else {
                            lean_inc(v_a_4090_);
                            lean_dec(v___x_3995_);
                            v___x_4092_ = lean_box(0);
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
                v_trace_4000_ = lean_ctor_get_uint8(
                    v_a_3996_,
                    (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                );
                lean_dec(v_a_3996_);
                if v_trace_4000_ == 0 {
                    if v_isShared_3999_ == 0 {
                        lean_ctor_set(v___x_3998_, 0, v_a_3994_);
                        v___x_4002_ = v___x_3998_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4003_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4003_, 0, v_a_3994_);
                        v___x_4002_ = v_reuseFailAlloc_4003_;
                        state = 2;
                        continue;
                    }
                } else {
                    if lean_obj_tag(v_a_3994_) == 0 {
                        v_seq_4004_ = lean_ctor_get(v_a_3994_, 0);
                        if lean_obj_tag(v_seq_4004_) == 1 {
                            v_tail_4005_ = lean_ctor_get(v_seq_4004_, 1);
                            if lean_obj_tag(v_tail_4005_) == 0 {
                                v_head_4006_ = lean_ctor_get(v_seq_4004_, 0);
                                v___x_4007_ = l_Lean_Meta_Grind_Action_ungroup___redArg___closed__1;
                                lean_inc(v_head_4006_);
                                v___x_4008_ = l_Lean_Syntax_isOfKind(v_head_4006_, v___x_4007_);
                                if v___x_4008_ == 0 {
                                    v___x_4009_ =
                                        l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__1;
                                    lean_inc(v_head_4006_);
                                    v___x_4010_ = l_Lean_Syntax_isOfKind(v_head_4006_, v___x_4009_);
                                    if v___x_4010_ == 0 {
                                        if v_isShared_3999_ == 0 {
                                            lean_ctor_set(v___x_3998_, 0, v_a_3994_);
                                            v___x_4012_ = v___x_3998_;
                                            state = 3;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_4013_ =
                                                lean_alloc_ctor(0, 1, (0) as u32);
                                            lean_ctor_set(v_reuseFailAlloc_4013_, 0, v_a_3994_);
                                            v___x_4012_ = v_reuseFailAlloc_4013_;
                                            state = 3;
                                            continue;
                                        }
                                    } else {
                                        v___x_4014_ = lean_unsigned_to_nat(1);
                                        v___x_4015_ =
                                            l_Lean_Syntax_getArg(v_head_4006_, v___x_4014_);
                                        v___x_4016_ =
                                            l_Lean_Meta_Grind_Action_mkGrindSeq___closed__3;
                                        lean_inc(v___x_4015_);
                                        v___x_4017_ =
                                            l_Lean_Syntax_isOfKind(v___x_4015_, v___x_4016_);
                                        if v___x_4017_ == 0 {
                                            lean_dec(v___x_4015_);
                                            if v_isShared_3999_ == 0 {
                                                lean_ctor_set(v___x_3998_, 0, v_a_3994_);
                                                v___x_4019_ = v___x_3998_;
                                                state = 4;
                                                continue;
                                            } else {
                                                v_reuseFailAlloc_4020_ =
                                                    lean_alloc_ctor(0, 1, (0) as u32);
                                                lean_ctor_set(v_reuseFailAlloc_4020_, 0, v_a_3994_);
                                                v___x_4019_ = v_reuseFailAlloc_4020_;
                                                state = 4;
                                                continue;
                                            }
                                        } else {
                                            v___x_4021_ = lean_unsigned_to_nat(0);
                                            v___x_4022_ =
                                                l_Lean_Syntax_getArg(v___x_4015_, v___x_4021_);
                                            lean_dec(v___x_4015_);
                                            v___x_4023_ =
                                                l_Lean_Meta_Grind_Action_mkGrindSeq___closed__5;
                                            lean_inc(v___x_4022_);
                                            v___x_4024_ =
                                                l_Lean_Syntax_isOfKind(v___x_4022_, v___x_4023_);
                                            if v___x_4024_ == 0 {
                                                lean_dec(v___x_4022_);
                                                if v_isShared_3999_ == 0 {
                                                    lean_ctor_set(v___x_3998_, 0, v_a_3994_);
                                                    v___x_4026_ = v___x_3998_;
                                                    state = 5;
                                                    continue;
                                                } else {
                                                    v_reuseFailAlloc_4027_ =
                                                        lean_alloc_ctor(0, 1, (0) as u32);
                                                    lean_ctor_set(
                                                        v_reuseFailAlloc_4027_,
                                                        0,
                                                        v_a_3994_,
                                                    );
                                                    v___x_4026_ = v_reuseFailAlloc_4027_;
                                                    state = 5;
                                                    continue;
                                                }
                                            } else {
                                                lean_inc(v_tail_4005_);
                                                v_isSharedCheck_4042_ =
                                                    (!lean_is_exclusive(v_a_3994_)) as u8;
                                                if v_isSharedCheck_4042_ == 0 {
                                                    v_unused_4043_ = lean_ctor_get(v_a_3994_, 0);
                                                    lean_dec(v_unused_4043_);
                                                    v___x_4029_ = v_a_3994_;
                                                    v_isShared_4030_ = v_isSharedCheck_4042_;
                                                    state = 6;
                                                    continue;
                                                } else {
                                                    lean_dec(v_a_3994_);
                                                    v___x_4029_ = lean_box(0);
                                                    v_isShared_4030_ = v_isSharedCheck_4042_;
                                                    state = 6;
                                                    continue;
                                                }
                                            }
                                        }
                                    }
                                } else {
                                    v___x_4044_ = lean_unsigned_to_nat(0);
                                    v___x_4045_ = lean_unsigned_to_nat(1);
                                    v___x_4046_ = l_Lean_Syntax_getArg(v_head_4006_, v___x_4045_);
                                    v___x_4047_ =
                                        l_Lean_Syntax_matchesNull(v___x_4046_, v___x_4044_);
                                    if v___x_4047_ == 0 {
                                        if v_isShared_3999_ == 0 {
                                            lean_ctor_set(v___x_3998_, 0, v_a_3994_);
                                            v___x_4049_ = v___x_3998_;
                                            state = 9;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_4050_ =
                                                lean_alloc_ctor(0, 1, (0) as u32);
                                            lean_ctor_set(v_reuseFailAlloc_4050_, 0, v_a_3994_);
                                            v___x_4049_ = v_reuseFailAlloc_4050_;
                                            state = 9;
                                            continue;
                                        }
                                    } else {
                                        v___x_4051_ = lean_unsigned_to_nat(3);
                                        v___x_4052_ =
                                            l_Lean_Syntax_getArg(v_head_4006_, v___x_4051_);
                                        v___x_4053_ =
                                            l_Lean_Meta_Grind_Action_mkGrindSeq___closed__3;
                                        lean_inc(v___x_4052_);
                                        v___x_4054_ =
                                            l_Lean_Syntax_isOfKind(v___x_4052_, v___x_4053_);
                                        if v___x_4054_ == 0 {
                                            lean_dec(v___x_4052_);
                                            if v_isShared_3999_ == 0 {
                                                lean_ctor_set(v___x_3998_, 0, v_a_3994_);
                                                v___x_4056_ = v___x_3998_;
                                                state = 10;
                                                continue;
                                            } else {
                                                v_reuseFailAlloc_4057_ =
                                                    lean_alloc_ctor(0, 1, (0) as u32);
                                                lean_ctor_set(v_reuseFailAlloc_4057_, 0, v_a_3994_);
                                                v___x_4056_ = v_reuseFailAlloc_4057_;
                                                state = 10;
                                                continue;
                                            }
                                        } else {
                                            v___x_4058_ =
                                                l_Lean_Syntax_getArg(v___x_4052_, v___x_4044_);
                                            lean_dec(v___x_4052_);
                                            v___x_4059_ =
                                                l_Lean_Meta_Grind_Action_mkGrindSeq___closed__5;
                                            lean_inc(v___x_4058_);
                                            v___x_4060_ =
                                                l_Lean_Syntax_isOfKind(v___x_4058_, v___x_4059_);
                                            if v___x_4060_ == 0 {
                                                lean_dec(v___x_4058_);
                                                if v_isShared_3999_ == 0 {
                                                    lean_ctor_set(v___x_3998_, 0, v_a_3994_);
                                                    v___x_4062_ = v___x_3998_;
                                                    state = 11;
                                                    continue;
                                                } else {
                                                    v_reuseFailAlloc_4063_ =
                                                        lean_alloc_ctor(0, 1, (0) as u32);
                                                    lean_ctor_set(
                                                        v_reuseFailAlloc_4063_,
                                                        0,
                                                        v_a_3994_,
                                                    );
                                                    v___x_4062_ = v_reuseFailAlloc_4063_;
                                                    state = 11;
                                                    continue;
                                                }
                                            } else {
                                                lean_inc(v_tail_4005_);
                                                v_isSharedCheck_4078_ =
                                                    (!lean_is_exclusive(v_a_3994_)) as u8;
                                                if v_isSharedCheck_4078_ == 0 {
                                                    v_unused_4079_ = lean_ctor_get(v_a_3994_, 0);
                                                    lean_dec(v_unused_4079_);
                                                    v___x_4065_ = v_a_3994_;
                                                    v_isShared_4066_ = v_isSharedCheck_4078_;
                                                    state = 12;
                                                    continue;
                                                } else {
                                                    lean_dec(v_a_3994_);
                                                    v___x_4065_ = lean_box(0);
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
                                    lean_ctor_set(v___x_3998_, 0, v_a_3994_);
                                    v___x_4081_ = v___x_3998_;
                                    state = 15;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_4082_ = lean_alloc_ctor(0, 1, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_4082_, 0, v_a_3994_);
                                    v___x_4081_ = v_reuseFailAlloc_4082_;
                                    state = 15;
                                    continue;
                                }
                            }
                        } else {
                            if v_isShared_3999_ == 0 {
                                lean_ctor_set(v___x_3998_, 0, v_a_3994_);
                                v___x_4084_ = v___x_3998_;
                                state = 16;
                                continue;
                            } else {
                                v_reuseFailAlloc_4085_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_4085_, 0, v_a_3994_);
                                v___x_4084_ = v_reuseFailAlloc_4085_;
                                state = 16;
                                continue;
                            }
                        }
                    } else {
                        if v_isShared_3999_ == 0 {
                            lean_ctor_set(v___x_3998_, 0, v_a_3994_);
                            v___x_4087_ = v___x_3998_;
                            state = 17;
                            continue;
                        } else {
                            v_reuseFailAlloc_4088_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4088_, 0, v_a_3994_);
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
                lean_dec(v___x_4022_);
                v___x_4032_ = l_Lean_Syntax_getArgs(v___x_4031_);
                lean_dec(v___x_4031_);
                v___x_4033_ = l_Lean_Syntax_TSepArray_getElems___redArg(v___x_4032_);
                lean_dec_ref(v___x_4032_);
                v___x_4034_ = lean_array_to_list(v___x_4033_);
                v___x_4035_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Action_ungroup_spec__0(
                    v___x_4034_,
                    v_tail_4005_,
                );
                if v_isShared_4030_ == 0 {
                    lean_ctor_set(v___x_4029_, 0, v___x_4035_);
                    v___x_4037_ = v___x_4029_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4041_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4041_, 0, v___x_4035_);
                    v___x_4037_ = v_reuseFailAlloc_4041_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_3999_ == 0 {
                    lean_ctor_set(v___x_3998_, 0, v___x_4037_);
                    v___x_4039_ = v___x_3998_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4040_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4040_, 0, v___x_4037_);
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
                lean_dec(v___x_4058_);
                v___x_4068_ = l_Lean_Syntax_getArgs(v___x_4067_);
                lean_dec(v___x_4067_);
                v___x_4069_ = l_Lean_Syntax_TSepArray_getElems___redArg(v___x_4068_);
                lean_dec_ref(v___x_4068_);
                v___x_4070_ = lean_array_to_list(v___x_4069_);
                v___x_4071_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Action_ungroup_spec__0(
                    v___x_4070_,
                    v_tail_4005_,
                );
                if v_isShared_4066_ == 0 {
                    lean_ctor_set(v___x_4065_, 0, v___x_4071_);
                    v___x_4073_ = v___x_4065_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4077_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4077_, 0, v___x_4071_);
                    v___x_4073_ = v_reuseFailAlloc_4077_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_3999_ == 0 {
                    lean_ctor_set(v___x_3998_, 0, v___x_4073_);
                    v___x_4075_ = v___x_3998_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4076_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4076_, 0, v___x_4073_);
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
                    v_reuseFailAlloc_4096_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4096_, 0, v_a_4090_);
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
    mut v_goal_4098_: *mut LeanObject,
    mut v_kp_4099_: *mut LeanObject,
    mut v_a_4100_: *mut LeanObject,
    mut v_a_4101_: *mut LeanObject,
    mut v_a_4102_: *mut LeanObject,
    mut v_a_4103_: *mut LeanObject,
    mut v_a_4104_: *mut LeanObject,
    mut v_a_4105_: *mut LeanObject,
    mut v_a_4106_: *mut LeanObject,
    mut v_a_4107_: *mut LeanObject,
    mut v_a_4108_: *mut LeanObject,
    mut v_a_4109_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4110_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_4108_);
    lean_dec_ref(v_a_4107_);
    lean_dec(v_a_4106_);
    lean_dec_ref(v_a_4105_);
    lean_dec(v_a_4104_);
    lean_dec_ref(v_a_4103_);
    lean_dec(v_a_4102_);
    lean_dec_ref(v_a_4101_);
    lean_dec(v_a_4100_);
    return v_res_4110_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_ungroup(
    mut v_goal_4111_: *mut LeanObject,
    mut v_x_4112_: *mut LeanObject,
    mut v_kp_4113_: *mut LeanObject,
    mut v_a_4114_: *mut LeanObject,
    mut v_a_4115_: *mut LeanObject,
    mut v_a_4116_: *mut LeanObject,
    mut v_a_4117_: *mut LeanObject,
    mut v_a_4118_: *mut LeanObject,
    mut v_a_4119_: *mut LeanObject,
    mut v_a_4120_: *mut LeanObject,
    mut v_a_4121_: *mut LeanObject,
    mut v_a_4122_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4124_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_goal_4125_: *mut LeanObject,
    mut v_x_4126_: *mut LeanObject,
    mut v_kp_4127_: *mut LeanObject,
    mut v_a_4128_: *mut LeanObject,
    mut v_a_4129_: *mut LeanObject,
    mut v_a_4130_: *mut LeanObject,
    mut v_a_4131_: *mut LeanObject,
    mut v_a_4132_: *mut LeanObject,
    mut v_a_4133_: *mut LeanObject,
    mut v_a_4134_: *mut LeanObject,
    mut v_a_4135_: *mut LeanObject,
    mut v_a_4136_: *mut LeanObject,
    mut v_a_4137_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4138_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_4136_);
    lean_dec_ref(v_a_4135_);
    lean_dec(v_a_4134_);
    lean_dec_ref(v_a_4133_);
    lean_dec(v_a_4132_);
    lean_dec_ref(v_a_4131_);
    lean_dec(v_a_4130_);
    lean_dec_ref(v_a_4129_);
    lean_dec(v_a_4128_);
    lean_dec_ref(v_x_4126_);
    return v_res_4138_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_concatTactic(
    mut v_r_4139_: *mut LeanObject,
    mut v_mk_4140_: *mut LeanObject,
    mut v_a_4141_: *mut LeanObject,
    mut v_a_4142_: *mut LeanObject,
    mut v_a_4143_: *mut LeanObject,
    mut v_a_4144_: *mut LeanObject,
    mut v_a_4145_: *mut LeanObject,
    mut v_a_4146_: *mut LeanObject,
    mut v_a_4147_: *mut LeanObject,
    mut v_a_4148_: *mut LeanObject,
    mut v_a_4149_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4155_: u8 = 0;
    let mut v_trace_4156_: u8 = 0;
    let mut v___x_4158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_seq_4160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4163_: u8 = 0;
    let mut v___x_4164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4168_: u8 = 0;
    let mut v___x_4169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4176_: u8 = 0;
    let mut v_a_4177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4180_: u8 = 0;
    let mut v___x_4182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4184_: u8 = 0;
    let mut v_isSharedCheck_4185_: u8 = 0;
    let mut v___x_4187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4189_: u8 = 0;
    let mut v_a_4190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4193_: u8 = 0;
    let mut v___x_4195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4197_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4151_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_4142_);
                if lean_obj_tag(v___x_4151_) == 0 {
                    v_a_4152_ = lean_ctor_get(v___x_4151_, 0);
                    v_isSharedCheck_4189_ = (!lean_is_exclusive(v___x_4151_)) as u8;
                    if v_isSharedCheck_4189_ == 0 {
                        v___x_4154_ = v___x_4151_;
                        v_isShared_4155_ = v_isSharedCheck_4189_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4152_);
                        lean_dec(v___x_4151_);
                        v___x_4154_ = lean_box(0);
                        v_isShared_4155_ = v_isSharedCheck_4189_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_mk_4140_);
                    lean_dec_ref(v_r_4139_);
                    v_a_4190_ = lean_ctor_get(v___x_4151_, 0);
                    v_isSharedCheck_4197_ = (!lean_is_exclusive(v___x_4151_)) as u8;
                    if v_isSharedCheck_4197_ == 0 {
                        v___x_4192_ = v___x_4151_;
                        v_isShared_4193_ = v_isSharedCheck_4197_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_4190_);
                        lean_dec(v___x_4151_);
                        v___x_4192_ = lean_box(0);
                        v_isShared_4193_ = v_isSharedCheck_4197_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v_trace_4156_ = lean_ctor_get_uint8(
                    v_a_4152_,
                    (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                );
                lean_dec(v_a_4152_);
                if v_trace_4156_ == 0 {
                    lean_dec_ref(v_mk_4140_);
                    if v_isShared_4155_ == 0 {
                        lean_ctor_set(v___x_4154_, 0, v_r_4139_);
                        v___x_4158_ = v___x_4154_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4159_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4159_, 0, v_r_4139_);
                        v___x_4158_ = v_reuseFailAlloc_4159_;
                        state = 2;
                        continue;
                    }
                } else {
                    if lean_obj_tag(v_r_4139_) == 0 {
                        lean_del_object(v___x_4154_);
                        v_seq_4160_ = lean_ctor_get(v_r_4139_, 0);
                        v_isSharedCheck_4185_ = (!lean_is_exclusive(v_r_4139_)) as u8;
                        if v_isSharedCheck_4185_ == 0 {
                            v___x_4162_ = v_r_4139_;
                            v_isShared_4163_ = v_isSharedCheck_4185_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_seq_4160_);
                            lean_dec(v_r_4139_);
                            v___x_4162_ = lean_box(0);
                            v_isShared_4163_ = v_isSharedCheck_4185_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_mk_4140_);
                        if v_isShared_4155_ == 0 {
                            lean_ctor_set(v___x_4154_, 0, v_r_4139_);
                            v___x_4187_ = v___x_4154_;
                            state = 9;
                            continue;
                        } else {
                            v_reuseFailAlloc_4188_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4188_, 0, v_r_4139_);
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
                lean_inc(v_a_4149_);
                lean_inc_ref(v_a_4148_);
                lean_inc(v_a_4147_);
                lean_inc_ref(v_a_4146_);
                lean_inc(v_a_4145_);
                lean_inc_ref(v_a_4144_);
                lean_inc(v_a_4143_);
                lean_inc_ref(v_a_4142_);
                lean_inc(v_a_4141_);
                v___x_4164_ = lean_apply_10(
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
                    lean_box(0),
                );
                if lean_obj_tag(v___x_4164_) == 0 {
                    v_a_4165_ = lean_ctor_get(v___x_4164_, 0);
                    v_isSharedCheck_4176_ = (!lean_is_exclusive(v___x_4164_)) as u8;
                    if v_isSharedCheck_4176_ == 0 {
                        v___x_4167_ = v___x_4164_;
                        v_isShared_4168_ = v_isSharedCheck_4176_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_4165_);
                        lean_dec(v___x_4164_);
                        v___x_4167_ = lean_box(0);
                        v_isShared_4168_ = v_isSharedCheck_4176_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4162_);
                    lean_dec(v_seq_4160_);
                    v_a_4177_ = lean_ctor_get(v___x_4164_, 0);
                    v_isSharedCheck_4184_ = (!lean_is_exclusive(v___x_4164_)) as u8;
                    if v_isSharedCheck_4184_ == 0 {
                        v___x_4179_ = v___x_4164_;
                        v_isShared_4180_ = v_isSharedCheck_4184_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_4177_);
                        lean_dec(v___x_4164_);
                        v___x_4179_ = lean_box(0);
                        v_isShared_4180_ = v_isSharedCheck_4184_;
                        state = 7;
                        continue;
                    }
                }
            }
            4 => {
                v___x_4169_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4169_, 0, v_a_4165_);
                lean_ctor_set(v___x_4169_, 1, v_seq_4160_);
                if v_isShared_4163_ == 0 {
                    lean_ctor_set(v___x_4162_, 0, v___x_4169_);
                    v___x_4171_ = v___x_4162_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4175_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4175_, 0, v___x_4169_);
                    v___x_4171_ = v_reuseFailAlloc_4175_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_4168_ == 0 {
                    lean_ctor_set(v___x_4167_, 0, v___x_4171_);
                    v___x_4173_ = v___x_4167_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4174_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4174_, 0, v___x_4171_);
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
                    v_reuseFailAlloc_4183_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4183_, 0, v_a_4177_);
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
                    v_reuseFailAlloc_4196_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4196_, 0, v_a_4190_);
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
    mut v_r_4198_: *mut LeanObject,
    mut v_mk_4199_: *mut LeanObject,
    mut v_a_4200_: *mut LeanObject,
    mut v_a_4201_: *mut LeanObject,
    mut v_a_4202_: *mut LeanObject,
    mut v_a_4203_: *mut LeanObject,
    mut v_a_4204_: *mut LeanObject,
    mut v_a_4205_: *mut LeanObject,
    mut v_a_4206_: *mut LeanObject,
    mut v_a_4207_: *mut LeanObject,
    mut v_a_4208_: *mut LeanObject,
    mut v_a_4209_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4210_: *mut LeanObject = core::ptr::null_mut();
    v_res_4210_ = l_Lean_Meta_Grind_Action_concatTactic(
        v_r_4198_, v_mk_4199_, v_a_4200_, v_a_4201_, v_a_4202_, v_a_4203_, v_a_4204_, v_a_4205_,
        v_a_4206_, v_a_4207_, v_a_4208_,
    );
    lean_dec(v_a_4208_);
    lean_dec_ref(v_a_4207_);
    lean_dec(v_a_4206_);
    lean_dec_ref(v_a_4205_);
    lean_dec(v_a_4204_);
    lean_dec_ref(v_a_4203_);
    lean_dec(v_a_4202_);
    lean_dec_ref(v_a_4201_);
    lean_dec(v_a_4200_);
    return v_res_4210_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_closeWith(
    mut v_mk_4211_: *mut LeanObject,
    mut v_a_4212_: *mut LeanObject,
    mut v_a_4213_: *mut LeanObject,
    mut v_a_4214_: *mut LeanObject,
    mut v_a_4215_: *mut LeanObject,
    mut v_a_4216_: *mut LeanObject,
    mut v_a_4217_: *mut LeanObject,
    mut v_a_4218_: *mut LeanObject,
    mut v_a_4219_: *mut LeanObject,
    mut v_a_4220_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4226_: u8 = 0;
    let mut v_trace_4227_: u8 = 0;
    let mut v___x_4228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4236_: u8 = 0;
    let mut v___x_4237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4243_: u8 = 0;
    let mut v_a_4244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4247_: u8 = 0;
    let mut v___x_4249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4251_: u8 = 0;
    let mut v_isSharedCheck_4252_: u8 = 0;
    let mut v_a_4253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4256_: u8 = 0;
    let mut v___x_4258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4260_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4222_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_4213_);
                if lean_obj_tag(v___x_4222_) == 0 {
                    v_a_4223_ = lean_ctor_get(v___x_4222_, 0);
                    v_isSharedCheck_4252_ = (!lean_is_exclusive(v___x_4222_)) as u8;
                    if v_isSharedCheck_4252_ == 0 {
                        v___x_4225_ = v___x_4222_;
                        v_isShared_4226_ = v_isSharedCheck_4252_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4223_);
                        lean_dec(v___x_4222_);
                        v___x_4225_ = lean_box(0);
                        v_isShared_4226_ = v_isSharedCheck_4252_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_mk_4211_);
                    v_a_4253_ = lean_ctor_get(v___x_4222_, 0);
                    v_isSharedCheck_4260_ = (!lean_is_exclusive(v___x_4222_)) as u8;
                    if v_isSharedCheck_4260_ == 0 {
                        v___x_4255_ = v___x_4222_;
                        v_isShared_4256_ = v_isSharedCheck_4260_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_4253_);
                        lean_dec(v___x_4222_);
                        v___x_4255_ = lean_box(0);
                        v_isShared_4256_ = v_isSharedCheck_4260_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_trace_4227_ = lean_ctor_get_uint8(
                    v_a_4223_,
                    (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                );
                lean_dec(v_a_4223_);
                if v_trace_4227_ == 0 {
                    lean_dec_ref(v_mk_4211_);
                    v___x_4228_ = l_Lean_Meta_Grind_Action_done___redArg___closed__0;
                    if v_isShared_4226_ == 0 {
                        lean_ctor_set(v___x_4225_, 0, v___x_4228_);
                        v___x_4230_ = v___x_4225_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4231_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4231_, 0, v___x_4228_);
                        v___x_4230_ = v_reuseFailAlloc_4231_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4225_);
                    lean_inc(v_a_4220_);
                    lean_inc_ref(v_a_4219_);
                    lean_inc(v_a_4218_);
                    lean_inc_ref(v_a_4217_);
                    lean_inc(v_a_4216_);
                    lean_inc_ref(v_a_4215_);
                    lean_inc(v_a_4214_);
                    lean_inc_ref(v_a_4213_);
                    lean_inc(v_a_4212_);
                    v___x_4232_ = lean_apply_10(
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
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_4232_) == 0 {
                        v_a_4233_ = lean_ctor_get(v___x_4232_, 0);
                        v_isSharedCheck_4243_ = (!lean_is_exclusive(v___x_4232_)) as u8;
                        if v_isSharedCheck_4243_ == 0 {
                            v___x_4235_ = v___x_4232_;
                            v_isShared_4236_ = v_isSharedCheck_4243_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_4233_);
                            lean_dec(v___x_4232_);
                            v___x_4235_ = lean_box(0);
                            v_isShared_4236_ = v_isSharedCheck_4243_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_4244_ = lean_ctor_get(v___x_4232_, 0);
                        v_isSharedCheck_4251_ = (!lean_is_exclusive(v___x_4232_)) as u8;
                        if v_isSharedCheck_4251_ == 0 {
                            v___x_4246_ = v___x_4232_;
                            v_isShared_4247_ = v_isSharedCheck_4251_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_4244_);
                            lean_dec(v___x_4232_);
                            v___x_4246_ = lean_box(0);
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
                v___x_4237_ = lean_box(0);
                v___x_4238_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4238_, 0, v_a_4233_);
                lean_ctor_set(v___x_4238_, 1, v___x_4237_);
                v___x_4239_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4239_, 0, v___x_4238_);
                if v_isShared_4236_ == 0 {
                    lean_ctor_set(v___x_4235_, 0, v___x_4239_);
                    v___x_4241_ = v___x_4235_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4242_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4242_, 0, v___x_4239_);
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
                    v_reuseFailAlloc_4250_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4250_, 0, v_a_4244_);
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
                    v_reuseFailAlloc_4259_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4259_, 0, v_a_4253_);
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
    mut v_mk_4261_: *mut LeanObject,
    mut v_a_4262_: *mut LeanObject,
    mut v_a_4263_: *mut LeanObject,
    mut v_a_4264_: *mut LeanObject,
    mut v_a_4265_: *mut LeanObject,
    mut v_a_4266_: *mut LeanObject,
    mut v_a_4267_: *mut LeanObject,
    mut v_a_4268_: *mut LeanObject,
    mut v_a_4269_: *mut LeanObject,
    mut v_a_4270_: *mut LeanObject,
    mut v_a_4271_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4272_: *mut LeanObject = core::ptr::null_mut();
    v_res_4272_ = l_Lean_Meta_Grind_Action_closeWith(
        v_mk_4261_, v_a_4262_, v_a_4263_, v_a_4264_, v_a_4265_, v_a_4266_, v_a_4267_, v_a_4268_,
        v_a_4269_, v_a_4270_,
    );
    lean_dec(v_a_4270_);
    lean_dec_ref(v_a_4269_);
    lean_dec(v_a_4268_);
    lean_dec_ref(v_a_4267_);
    lean_dec(v_a_4266_);
    lean_dec_ref(v_a_4265_);
    lean_dec(v_a_4264_);
    lean_dec_ref(v_a_4263_);
    lean_dec(v_a_4262_);
    return v_res_4272_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg___lam__0(
    mut v_x_4273_: *mut LeanObject,
    mut v___y_4274_: *mut LeanObject,
    mut v___y_4275_: *mut LeanObject,
    mut v___y_4276_: *mut LeanObject,
    mut v___y_4277_: *mut LeanObject,
    mut v___y_4278_: *mut LeanObject,
    mut v___y_4279_: *mut LeanObject,
    mut v___y_4280_: *mut LeanObject,
    mut v___y_4281_: *mut LeanObject,
    mut v___y_4282_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4284_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_4278_);
    lean_inc_ref(v___y_4277_);
    lean_inc(v___y_4276_);
    lean_inc_ref(v___y_4275_);
    lean_inc(v___y_4274_);
    v___x_4284_ = lean_apply_10(
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
        lean_box(0),
    );
    return v___x_4284_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg___lam__0___boxed(
    mut v_x_4285_: *mut LeanObject,
    mut v___y_4286_: *mut LeanObject,
    mut v___y_4287_: *mut LeanObject,
    mut v___y_4288_: *mut LeanObject,
    mut v___y_4289_: *mut LeanObject,
    mut v___y_4290_: *mut LeanObject,
    mut v___y_4291_: *mut LeanObject,
    mut v___y_4292_: *mut LeanObject,
    mut v___y_4293_: *mut LeanObject,
    mut v___y_4294_: *mut LeanObject,
    mut v___y_4295_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4296_: *mut LeanObject = core::ptr::null_mut();
    v_res_4296_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg___lam__0(v_x_4285_, v___y_4286_, v___y_4287_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_, v___y_4292_, v___y_4293_, v___y_4294_);
    lean_dec(v___y_4290_);
    lean_dec_ref(v___y_4289_);
    lean_dec(v___y_4288_);
    lean_dec_ref(v___y_4287_);
    lean_dec(v___y_4286_);
    return v_res_4296_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg(
    mut v_mvarId_4297_: *mut LeanObject,
    mut v_x_4298_: *mut LeanObject,
    mut v___y_4299_: *mut LeanObject,
    mut v___y_4300_: *mut LeanObject,
    mut v___y_4301_: *mut LeanObject,
    mut v___y_4302_: *mut LeanObject,
    mut v___y_4303_: *mut LeanObject,
    mut v___y_4304_: *mut LeanObject,
    mut v___y_4305_: *mut LeanObject,
    mut v___y_4306_: *mut LeanObject,
    mut v___y_4307_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4314_: u8 = 0;
    let mut v___x_4316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4318_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_4303_);
                lean_inc_ref(v___y_4302_);
                lean_inc(v___y_4301_);
                lean_inc_ref(v___y_4300_);
                lean_inc(v___y_4299_);
                v___f_4309_ = lean_alloc_closure(l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 11, 6);
                lean_closure_set(v___f_4309_, 0, v_x_4298_);
                lean_closure_set(v___f_4309_, 1, v___y_4299_);
                lean_closure_set(v___f_4309_, 2, v___y_4300_);
                lean_closure_set(v___f_4309_, 3, v___y_4301_);
                lean_closure_set(v___f_4309_, 4, v___y_4302_);
                lean_closure_set(v___f_4309_, 5, v___y_4303_);
                v___x_4310_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    lean_box(0),
                    v_mvarId_4297_,
                    v___f_4309_,
                    v___y_4304_,
                    v___y_4305_,
                    v___y_4306_,
                    v___y_4307_,
                );
                if lean_obj_tag(v___x_4310_) == 0 {
                    return v___x_4310_;
                } else {
                    v_a_4311_ = lean_ctor_get(v___x_4310_, 0);
                    v_isSharedCheck_4318_ = (!lean_is_exclusive(v___x_4310_)) as u8;
                    if v_isSharedCheck_4318_ == 0 {
                        v___x_4313_ = v___x_4310_;
                        v_isShared_4314_ = v_isSharedCheck_4318_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4311_);
                        lean_dec(v___x_4310_);
                        v___x_4313_ = lean_box(0);
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
                    v_reuseFailAlloc_4317_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4317_, 0, v_a_4311_);
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
    mut v_mvarId_4319_: *mut LeanObject,
    mut v_x_4320_: *mut LeanObject,
    mut v___y_4321_: *mut LeanObject,
    mut v___y_4322_: *mut LeanObject,
    mut v___y_4323_: *mut LeanObject,
    mut v___y_4324_: *mut LeanObject,
    mut v___y_4325_: *mut LeanObject,
    mut v___y_4326_: *mut LeanObject,
    mut v___y_4327_: *mut LeanObject,
    mut v___y_4328_: *mut LeanObject,
    mut v___y_4329_: *mut LeanObject,
    mut v___y_4330_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4331_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_4329_);
    lean_dec_ref(v___y_4328_);
    lean_dec(v___y_4327_);
    lean_dec_ref(v___y_4326_);
    lean_dec(v___y_4325_);
    lean_dec_ref(v___y_4324_);
    lean_dec(v___y_4323_);
    lean_dec_ref(v___y_4322_);
    lean_dec(v___y_4321_);
    return v_res_4331_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0(
    mut v_00_u03b1_4332_: *mut LeanObject,
    mut v_mvarId_4333_: *mut LeanObject,
    mut v_x_4334_: *mut LeanObject,
    mut v___y_4335_: *mut LeanObject,
    mut v___y_4336_: *mut LeanObject,
    mut v___y_4337_: *mut LeanObject,
    mut v___y_4338_: *mut LeanObject,
    mut v___y_4339_: *mut LeanObject,
    mut v___y_4340_: *mut LeanObject,
    mut v___y_4341_: *mut LeanObject,
    mut v___y_4342_: *mut LeanObject,
    mut v___y_4343_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4345_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_4346_: *mut LeanObject,
    mut v_mvarId_4347_: *mut LeanObject,
    mut v_x_4348_: *mut LeanObject,
    mut v___y_4349_: *mut LeanObject,
    mut v___y_4350_: *mut LeanObject,
    mut v___y_4351_: *mut LeanObject,
    mut v___y_4352_: *mut LeanObject,
    mut v___y_4353_: *mut LeanObject,
    mut v___y_4354_: *mut LeanObject,
    mut v___y_4355_: *mut LeanObject,
    mut v___y_4356_: *mut LeanObject,
    mut v___y_4357_: *mut LeanObject,
    mut v___y_4358_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4359_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_4357_);
    lean_dec_ref(v___y_4356_);
    lean_dec(v___y_4355_);
    lean_dec_ref(v___y_4354_);
    lean_dec(v___y_4353_);
    lean_dec_ref(v___y_4352_);
    lean_dec(v___y_4351_);
    lean_dec_ref(v___y_4350_);
    lean_dec(v___y_4349_);
    return v_res_4359_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_terminalAction___lam__0(
    mut v_goal_4360_: *mut LeanObject,
    mut v_check_4361_: *mut LeanObject,
    mut v___y_4362_: *mut LeanObject,
    mut v___y_4363_: *mut LeanObject,
    mut v___y_4364_: *mut LeanObject,
    mut v___y_4365_: *mut LeanObject,
    mut v___y_4366_: *mut LeanObject,
    mut v___y_4367_: *mut LeanObject,
    mut v___y_4368_: *mut LeanObject,
    mut v___y_4369_: *mut LeanObject,
    mut v___y_4370_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4377_: u8 = 0;
    let mut v___x_4378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4383_: u8 = 0;
    let mut v_a_4384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4387_: u8 = 0;
    let mut v___x_4389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4391_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4372_ = lean_st_mk_ref(v_goal_4360_);
                lean_inc(v___x_4372_);
                v___x_4373_ = lean_apply_11(
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
                    lean_box(0),
                );
                if lean_obj_tag(v___x_4373_) == 0 {
                    v_a_4374_ = lean_ctor_get(v___x_4373_, 0);
                    v_isSharedCheck_4383_ = (!lean_is_exclusive(v___x_4373_)) as u8;
                    if v_isSharedCheck_4383_ == 0 {
                        v___x_4376_ = v___x_4373_;
                        v_isShared_4377_ = v_isSharedCheck_4383_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4374_);
                        lean_dec(v___x_4373_);
                        v___x_4376_ = lean_box(0);
                        v_isShared_4377_ = v_isSharedCheck_4383_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_4372_);
                    v_a_4384_ = lean_ctor_get(v___x_4373_, 0);
                    v_isSharedCheck_4391_ = (!lean_is_exclusive(v___x_4373_)) as u8;
                    if v_isSharedCheck_4391_ == 0 {
                        v___x_4386_ = v___x_4373_;
                        v_isShared_4387_ = v_isSharedCheck_4391_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4384_);
                        lean_dec(v___x_4373_);
                        v___x_4386_ = lean_box(0);
                        v_isShared_4387_ = v_isSharedCheck_4391_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4378_ = lean_st_ref_get(v___x_4372_);
                lean_dec(v___x_4372_);
                v___x_4379_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4379_, 0, v_a_4374_);
                lean_ctor_set(v___x_4379_, 1, v___x_4378_);
                if v_isShared_4377_ == 0 {
                    lean_ctor_set(v___x_4376_, 0, v___x_4379_);
                    v___x_4381_ = v___x_4376_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4382_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4382_, 0, v___x_4379_);
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
                    v_reuseFailAlloc_4390_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4390_, 0, v_a_4384_);
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
    mut v_goal_4392_: *mut LeanObject,
    mut v_check_4393_: *mut LeanObject,
    mut v___y_4394_: *mut LeanObject,
    mut v___y_4395_: *mut LeanObject,
    mut v___y_4396_: *mut LeanObject,
    mut v___y_4397_: *mut LeanObject,
    mut v___y_4398_: *mut LeanObject,
    mut v___y_4399_: *mut LeanObject,
    mut v___y_4400_: *mut LeanObject,
    mut v___y_4401_: *mut LeanObject,
    mut v___y_4402_: *mut LeanObject,
    mut v___y_4403_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4404_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_check_4405_: *mut LeanObject,
    mut v_mkTac_4406_: *mut LeanObject,
    mut v_goal_4407_: *mut LeanObject,
    mut v_kna_4408_: *mut LeanObject,
    mut v_kp_4409_: *mut LeanObject,
    mut v_a_4410_: *mut LeanObject,
    mut v_a_4411_: *mut LeanObject,
    mut v_a_4412_: *mut LeanObject,
    mut v_a_4413_: *mut LeanObject,
    mut v_a_4414_: *mut LeanObject,
    mut v_a_4415_: *mut LeanObject,
    mut v_a_4416_: *mut LeanObject,
    mut v_a_4417_: *mut LeanObject,
    mut v_a_4418_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_mvarId_4420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: u8 = 0;
    let mut v_snd_4426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toGoalState_4429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inconsistent_4430_: u8 = 0;
    let mut v___x_4431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4436_: u8 = 0;
    let mut v___x_4438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4440_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_mvarId_4420_ = lean_ctor_get(v_goal_4407_, 1);
                lean_inc(v_mvarId_4420_);
                v___f_4421_ = lean_alloc_closure(
                    l_Lean_Meta_Grind_Action_terminalAction___lam__0___boxed
                        as *mut core::ffi::c_void,
                    12,
                    2,
                );
                lean_closure_set(v___f_4421_, 0, v_goal_4407_);
                lean_closure_set(v___f_4421_, 1, v_check_4405_);
                v___x_4422_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg(v_mvarId_4420_, v___f_4421_, v_a_4410_, v_a_4411_, v_a_4412_, v_a_4413_, v_a_4414_, v_a_4415_, v_a_4416_, v_a_4417_, v_a_4418_);
                if lean_obj_tag(v___x_4422_) == 0 {
                    v_a_4423_ = lean_ctor_get(v___x_4422_, 0);
                    lean_inc(v_a_4423_);
                    lean_dec_ref_known(v___x_4422_, 1);
                    v_fst_4424_ = lean_ctor_get(v_a_4423_, 0);
                    v___x_4425_ = (lean_unbox(v_fst_4424_) as u8);
                    if v___x_4425_ == 0 {
                        lean_dec_ref(v_kp_4409_);
                        lean_dec_ref(v_mkTac_4406_);
                        v_snd_4426_ = lean_ctor_get(v_a_4423_, 1);
                        lean_inc(v_snd_4426_);
                        lean_dec(v_a_4423_);
                        lean_inc(v_a_4418_);
                        lean_inc_ref(v_a_4417_);
                        lean_inc(v_a_4416_);
                        lean_inc_ref(v_a_4415_);
                        lean_inc(v_a_4414_);
                        lean_inc_ref(v_a_4413_);
                        lean_inc(v_a_4412_);
                        lean_inc_ref(v_a_4411_);
                        lean_inc(v_a_4410_);
                        v___x_4427_ = lean_apply_11(
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
                            lean_box(0),
                        );
                        return v___x_4427_;
                    } else {
                        lean_dec_ref(v_kna_4408_);
                        v_snd_4428_ = lean_ctor_get(v_a_4423_, 1);
                        lean_inc(v_snd_4428_);
                        lean_dec(v_a_4423_);
                        v_toGoalState_4429_ = lean_ctor_get(v_snd_4428_, 0);
                        v_inconsistent_4430_ = lean_ctor_get_uint8(
                            v_toGoalState_4429_,
                            (core::mem::size_of::<*mut LeanObject>() * 17) as u32,
                        );
                        if v_inconsistent_4430_ == 0 {
                            lean_dec_ref(v_mkTac_4406_);
                            lean_inc(v_a_4418_);
                            lean_inc_ref(v_a_4417_);
                            lean_inc(v_a_4416_);
                            lean_inc_ref(v_a_4415_);
                            lean_inc(v_a_4414_);
                            lean_inc_ref(v_a_4413_);
                            lean_inc(v_a_4412_);
                            lean_inc_ref(v_a_4411_);
                            lean_inc(v_a_4410_);
                            v___x_4431_ = lean_apply_11(
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
                                lean_box(0),
                            );
                            return v___x_4431_;
                        } else {
                            lean_dec(v_snd_4428_);
                            lean_dec_ref(v_kp_4409_);
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
                    lean_dec_ref(v_kp_4409_);
                    lean_dec_ref(v_kna_4408_);
                    lean_dec_ref(v_mkTac_4406_);
                    v_a_4433_ = lean_ctor_get(v___x_4422_, 0);
                    v_isSharedCheck_4440_ = (!lean_is_exclusive(v___x_4422_)) as u8;
                    if v_isSharedCheck_4440_ == 0 {
                        v___x_4435_ = v___x_4422_;
                        v_isShared_4436_ = v_isSharedCheck_4440_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4433_);
                        lean_dec(v___x_4422_);
                        v___x_4435_ = lean_box(0);
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
                    v_reuseFailAlloc_4439_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4439_, 0, v_a_4433_);
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
    mut v_check_4441_: *mut LeanObject,
    mut v_mkTac_4442_: *mut LeanObject,
    mut v_goal_4443_: *mut LeanObject,
    mut v_kna_4444_: *mut LeanObject,
    mut v_kp_4445_: *mut LeanObject,
    mut v_a_4446_: *mut LeanObject,
    mut v_a_4447_: *mut LeanObject,
    mut v_a_4448_: *mut LeanObject,
    mut v_a_4449_: *mut LeanObject,
    mut v_a_4450_: *mut LeanObject,
    mut v_a_4451_: *mut LeanObject,
    mut v_a_4452_: *mut LeanObject,
    mut v_a_4453_: *mut LeanObject,
    mut v_a_4454_: *mut LeanObject,
    mut v_a_4455_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4456_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_4454_);
    lean_dec_ref(v_a_4453_);
    lean_dec(v_a_4452_);
    lean_dec_ref(v_a_4451_);
    lean_dec(v_a_4450_);
    lean_dec_ref(v_a_4449_);
    lean_dec(v_a_4448_);
    lean_dec_ref(v_a_4447_);
    lean_dec(v_a_4446_);
    return v_res_4456_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_saveStateIfTracing___redArg(
    mut v_a_4457_: *mut LeanObject,
    mut v_a_4458_: *mut LeanObject,
    mut v_a_4459_: *mut LeanObject,
    mut v_a_4460_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4466_: u8 = 0;
    let mut v_trace_4467_: u8 = 0;
    let mut v___x_4468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4476_: u8 = 0;
    let mut v___x_4477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4481_: u8 = 0;
    let mut v_a_4482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4485_: u8 = 0;
    let mut v___x_4487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4489_: u8 = 0;
    let mut v_isSharedCheck_4490_: u8 = 0;
    let mut v_a_4491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4494_: u8 = 0;
    let mut v___x_4496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4498_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4462_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_4457_);
                if lean_obj_tag(v___x_4462_) == 0 {
                    v_a_4463_ = lean_ctor_get(v___x_4462_, 0);
                    v_isSharedCheck_4490_ = (!lean_is_exclusive(v___x_4462_)) as u8;
                    if v_isSharedCheck_4490_ == 0 {
                        v___x_4465_ = v___x_4462_;
                        v_isShared_4466_ = v_isSharedCheck_4490_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4463_);
                        lean_dec(v___x_4462_);
                        v___x_4465_ = lean_box(0);
                        v_isShared_4466_ = v_isSharedCheck_4490_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4491_ = lean_ctor_get(v___x_4462_, 0);
                    v_isSharedCheck_4498_ = (!lean_is_exclusive(v___x_4462_)) as u8;
                    if v_isSharedCheck_4498_ == 0 {
                        v___x_4493_ = v___x_4462_;
                        v_isShared_4494_ = v_isSharedCheck_4498_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_4491_);
                        lean_dec(v___x_4462_);
                        v___x_4493_ = lean_box(0);
                        v_isShared_4494_ = v_isSharedCheck_4498_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_trace_4467_ = lean_ctor_get_uint8(
                    v_a_4463_,
                    (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                );
                lean_dec(v_a_4463_);
                if v_trace_4467_ == 0 {
                    v___x_4468_ = lean_box(0);
                    if v_isShared_4466_ == 0 {
                        lean_ctor_set(v___x_4465_, 0, v___x_4468_);
                        v___x_4470_ = v___x_4465_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4471_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4471_, 0, v___x_4468_);
                        v___x_4470_ = v_reuseFailAlloc_4471_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4465_);
                    v___x_4472_ =
                        l_Lean_Meta_Grind_saveState___redArg(v_a_4458_, v_a_4459_, v_a_4460_);
                    if lean_obj_tag(v___x_4472_) == 0 {
                        v_a_4473_ = lean_ctor_get(v___x_4472_, 0);
                        v_isSharedCheck_4481_ = (!lean_is_exclusive(v___x_4472_)) as u8;
                        if v_isSharedCheck_4481_ == 0 {
                            v___x_4475_ = v___x_4472_;
                            v_isShared_4476_ = v_isSharedCheck_4481_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_4473_);
                            lean_dec(v___x_4472_);
                            v___x_4475_ = lean_box(0);
                            v_isShared_4476_ = v_isSharedCheck_4481_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_4482_ = lean_ctor_get(v___x_4472_, 0);
                        v_isSharedCheck_4489_ = (!lean_is_exclusive(v___x_4472_)) as u8;
                        if v_isSharedCheck_4489_ == 0 {
                            v___x_4484_ = v___x_4472_;
                            v_isShared_4485_ = v_isSharedCheck_4489_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_4482_);
                            lean_dec(v___x_4472_);
                            v___x_4484_ = lean_box(0);
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
                v___x_4477_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4477_, 0, v_a_4473_);
                if v_isShared_4476_ == 0 {
                    lean_ctor_set(v___x_4475_, 0, v___x_4477_);
                    v___x_4479_ = v___x_4475_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4480_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4480_, 0, v___x_4477_);
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
                    v_reuseFailAlloc_4488_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4488_, 0, v_a_4482_);
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
                    v_reuseFailAlloc_4497_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4497_, 0, v_a_4491_);
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
    mut v_a_4499_: *mut LeanObject,
    mut v_a_4500_: *mut LeanObject,
    mut v_a_4501_: *mut LeanObject,
    mut v_a_4502_: *mut LeanObject,
    mut v_a_4503_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4504_: *mut LeanObject = core::ptr::null_mut();
    v_res_4504_ = l_Lean_Meta_Grind_Action_saveStateIfTracing___redArg(
        v_a_4499_, v_a_4500_, v_a_4501_, v_a_4502_,
    );
    lean_dec(v_a_4502_);
    lean_dec(v_a_4501_);
    lean_dec(v_a_4500_);
    lean_dec_ref(v_a_4499_);
    return v_res_4504_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_saveStateIfTracing(
    mut v_a_4505_: *mut LeanObject,
    mut v_a_4506_: *mut LeanObject,
    mut v_a_4507_: *mut LeanObject,
    mut v_a_4508_: *mut LeanObject,
    mut v_a_4509_: *mut LeanObject,
    mut v_a_4510_: *mut LeanObject,
    mut v_a_4511_: *mut LeanObject,
    mut v_a_4512_: *mut LeanObject,
    mut v_a_4513_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4515_: *mut LeanObject = core::ptr::null_mut();
    v___x_4515_ = l_Lean_Meta_Grind_Action_saveStateIfTracing___redArg(
        v_a_4506_, v_a_4507_, v_a_4511_, v_a_4513_,
    );
    return v___x_4515_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_saveStateIfTracing___boxed(
    mut v_a_4516_: *mut LeanObject,
    mut v_a_4517_: *mut LeanObject,
    mut v_a_4518_: *mut LeanObject,
    mut v_a_4519_: *mut LeanObject,
    mut v_a_4520_: *mut LeanObject,
    mut v_a_4521_: *mut LeanObject,
    mut v_a_4522_: *mut LeanObject,
    mut v_a_4523_: *mut LeanObject,
    mut v_a_4524_: *mut LeanObject,
    mut v_a_4525_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4526_: *mut LeanObject = core::ptr::null_mut();
    v_res_4526_ = l_Lean_Meta_Grind_Action_saveStateIfTracing(
        v_a_4516_, v_a_4517_, v_a_4518_, v_a_4519_, v_a_4520_, v_a_4521_, v_a_4522_, v_a_4523_,
        v_a_4524_,
    );
    lean_dec(v_a_4524_);
    lean_dec_ref(v_a_4523_);
    lean_dec(v_a_4522_);
    lean_dec_ref(v_a_4521_);
    lean_dec(v_a_4520_);
    lean_dec_ref(v_a_4519_);
    lean_dec(v_a_4518_);
    lean_dec_ref(v_a_4517_);
    lean_dec(v_a_4516_);
    return v_res_4526_;
}
pub unsafe fn l_Lean_withoutModifyingState___at___00Lean_Meta_Grind_Action_checkSeqAt_spec__0___redArg(
    mut v_x_4527_: *mut LeanObject,
    mut v___y_4528_: *mut LeanObject,
    mut v___y_4529_: *mut LeanObject,
    mut v___y_4530_: *mut LeanObject,
    mut v___y_4531_: *mut LeanObject,
    mut v___y_4532_: *mut LeanObject,
    mut v___y_4533_: *mut LeanObject,
    mut v___y_4534_: *mut LeanObject,
    mut v___y_4535_: *mut LeanObject,
    mut v___y_4536_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_4540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4545_: u8 = 0;
    let mut v___x_4547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4549_: u8 = 0;
    let mut v_unused_4550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4554_: u8 = 0;
    let mut v___x_4556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4558_: u8 = 0;
    let mut v_a_4559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4563_: u8 = 0;
    let mut v___x_4565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4567_: u8 = 0;
    let mut v_unused_4568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4572_: u8 = 0;
    let mut v___x_4574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4576_: u8 = 0;
    let mut v_a_4577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4580_: u8 = 0;
    let mut v___x_4582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4584_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4538_ =
                    l_Lean_Meta_Grind_saveState___redArg(v___y_4530_, v___y_4534_, v___y_4536_);
                if lean_obj_tag(v___x_4538_) == 0 {
                    v_a_4539_ = lean_ctor_get(v___x_4538_, 0);
                    lean_inc(v_a_4539_);
                    lean_dec_ref_known(v___x_4538_, 1);
                    lean_inc(v___y_4536_);
                    lean_inc_ref(v___y_4535_);
                    lean_inc(v___y_4534_);
                    lean_inc_ref(v___y_4533_);
                    lean_inc(v___y_4532_);
                    lean_inc_ref(v___y_4531_);
                    lean_inc(v___y_4530_);
                    lean_inc_ref(v___y_4529_);
                    lean_inc(v___y_4528_);
                    v_r_4540_ = lean_apply_10(
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
                        lean_box(0),
                    );
                    if lean_obj_tag(v_r_4540_) == 0 {
                        v_a_4541_ = lean_ctor_get(v_r_4540_, 0);
                        lean_inc(v_a_4541_);
                        lean_dec_ref_known(v_r_4540_, 1);
                        v___x_4542_ = l_Lean_Meta_Grind_SavedState_restore___redArg(
                            v_a_4539_,
                            v___y_4530_,
                            v___y_4534_,
                            v___y_4536_,
                        );
                        if lean_obj_tag(v___x_4542_) == 0 {
                            v_isSharedCheck_4549_ = (!lean_is_exclusive(v___x_4542_)) as u8;
                            if v_isSharedCheck_4549_ == 0 {
                                v_unused_4550_ = lean_ctor_get(v___x_4542_, 0);
                                lean_dec(v_unused_4550_);
                                v___x_4544_ = v___x_4542_;
                                v_isShared_4545_ = v_isSharedCheck_4549_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec(v___x_4542_);
                                v___x_4544_ = lean_box(0);
                                v_isShared_4545_ = v_isSharedCheck_4549_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_4541_);
                            v_a_4551_ = lean_ctor_get(v___x_4542_, 0);
                            v_isSharedCheck_4558_ = (!lean_is_exclusive(v___x_4542_)) as u8;
                            if v_isSharedCheck_4558_ == 0 {
                                v___x_4553_ = v___x_4542_;
                                v_isShared_4554_ = v_isSharedCheck_4558_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_4551_);
                                lean_dec(v___x_4542_);
                                v___x_4553_ = lean_box(0);
                                v_isShared_4554_ = v_isSharedCheck_4558_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        v_a_4559_ = lean_ctor_get(v_r_4540_, 0);
                        lean_inc(v_a_4559_);
                        lean_dec_ref_known(v_r_4540_, 1);
                        v___x_4560_ = l_Lean_Meta_Grind_SavedState_restore___redArg(
                            v_a_4539_,
                            v___y_4530_,
                            v___y_4534_,
                            v___y_4536_,
                        );
                        if lean_obj_tag(v___x_4560_) == 0 {
                            v_isSharedCheck_4567_ = (!lean_is_exclusive(v___x_4560_)) as u8;
                            if v_isSharedCheck_4567_ == 0 {
                                v_unused_4568_ = lean_ctor_get(v___x_4560_, 0);
                                lean_dec(v_unused_4568_);
                                v___x_4562_ = v___x_4560_;
                                v_isShared_4563_ = v_isSharedCheck_4567_;
                                state = 5;
                                continue;
                            } else {
                                lean_dec(v___x_4560_);
                                v___x_4562_ = lean_box(0);
                                v_isShared_4563_ = v_isSharedCheck_4567_;
                                state = 5;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_4559_);
                            v_a_4569_ = lean_ctor_get(v___x_4560_, 0);
                            v_isSharedCheck_4576_ = (!lean_is_exclusive(v___x_4560_)) as u8;
                            if v_isSharedCheck_4576_ == 0 {
                                v___x_4571_ = v___x_4560_;
                                v_isShared_4572_ = v_isSharedCheck_4576_;
                                state = 7;
                                continue;
                            } else {
                                lean_inc(v_a_4569_);
                                lean_dec(v___x_4560_);
                                v___x_4571_ = lean_box(0);
                                v_isShared_4572_ = v_isSharedCheck_4576_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_x_4527_);
                    v_a_4577_ = lean_ctor_get(v___x_4538_, 0);
                    v_isSharedCheck_4584_ = (!lean_is_exclusive(v___x_4538_)) as u8;
                    if v_isSharedCheck_4584_ == 0 {
                        v___x_4579_ = v___x_4538_;
                        v_isShared_4580_ = v_isSharedCheck_4584_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_4577_);
                        lean_dec(v___x_4538_);
                        v___x_4579_ = lean_box(0);
                        v_isShared_4580_ = v_isSharedCheck_4584_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4545_ == 0 {
                    lean_ctor_set(v___x_4544_, 0, v_a_4541_);
                    v___x_4547_ = v___x_4544_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4548_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4548_, 0, v_a_4541_);
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
                    v_reuseFailAlloc_4557_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4557_, 0, v_a_4551_);
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
                    lean_ctor_set_tag(v___x_4562_, 1);
                    lean_ctor_set(v___x_4562_, 0, v_a_4559_);
                    v___x_4565_ = v___x_4562_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4566_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4566_, 0, v_a_4559_);
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
                    v_reuseFailAlloc_4575_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4575_, 0, v_a_4569_);
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
                    v_reuseFailAlloc_4583_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4583_, 0, v_a_4577_);
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
    mut v_x_4585_: *mut LeanObject,
    mut v___y_4586_: *mut LeanObject,
    mut v___y_4587_: *mut LeanObject,
    mut v___y_4588_: *mut LeanObject,
    mut v___y_4589_: *mut LeanObject,
    mut v___y_4590_: *mut LeanObject,
    mut v___y_4591_: *mut LeanObject,
    mut v___y_4592_: *mut LeanObject,
    mut v___y_4593_: *mut LeanObject,
    mut v___y_4594_: *mut LeanObject,
    mut v___y_4595_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4596_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_4594_);
    lean_dec_ref(v___y_4593_);
    lean_dec(v___y_4592_);
    lean_dec_ref(v___y_4591_);
    lean_dec(v___y_4590_);
    lean_dec_ref(v___y_4589_);
    lean_dec(v___y_4588_);
    lean_dec_ref(v___y_4587_);
    lean_dec(v___y_4586_);
    return v_res_4596_;
}
pub unsafe fn l_Lean_withoutModifyingState___at___00Lean_Meta_Grind_Action_checkSeqAt_spec__0(
    mut v_00_u03b1_4597_: *mut LeanObject,
    mut v_x_4598_: *mut LeanObject,
    mut v___y_4599_: *mut LeanObject,
    mut v___y_4600_: *mut LeanObject,
    mut v___y_4601_: *mut LeanObject,
    mut v___y_4602_: *mut LeanObject,
    mut v___y_4603_: *mut LeanObject,
    mut v___y_4604_: *mut LeanObject,
    mut v___y_4605_: *mut LeanObject,
    mut v___y_4606_: *mut LeanObject,
    mut v___y_4607_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4609_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_4610_: *mut LeanObject,
    mut v_x_4611_: *mut LeanObject,
    mut v___y_4612_: *mut LeanObject,
    mut v___y_4613_: *mut LeanObject,
    mut v___y_4614_: *mut LeanObject,
    mut v___y_4615_: *mut LeanObject,
    mut v___y_4616_: *mut LeanObject,
    mut v___y_4617_: *mut LeanObject,
    mut v___y_4618_: *mut LeanObject,
    mut v___y_4619_: *mut LeanObject,
    mut v___y_4620_: *mut LeanObject,
    mut v___y_4621_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4622_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_4620_);
    lean_dec_ref(v___y_4619_);
    lean_dec(v___y_4618_);
    lean_dec_ref(v___y_4617_);
    lean_dec(v___y_4616_);
    lean_dec_ref(v___y_4615_);
    lean_dec(v___y_4614_);
    lean_dec_ref(v___y_4613_);
    lean_dec(v___y_4612_);
    return v_res_4622_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_checkSeqAt___lam__0(
    mut v_val_4623_: *mut LeanObject,
    mut v_seq_4624_: *mut LeanObject,
    mut v_goal_4625_: *mut LeanObject,
    mut v___y_4626_: *mut LeanObject,
    mut v___y_4627_: *mut LeanObject,
    mut v___y_4628_: *mut LeanObject,
    mut v___y_4629_: *mut LeanObject,
    mut v___y_4630_: *mut LeanObject,
    mut v___y_4631_: *mut LeanObject,
    mut v___y_4632_: *mut LeanObject,
    mut v___y_4633_: *mut LeanObject,
    mut v___y_4634_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_4638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_simp_4640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_simpMethods_4641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_anchorRefs_x3f_4642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cheapCases_4643_: u8 = 0;
    let mut v_reportMVarIssue_4644_: u8 = 0;
    let mut v_splitSource_4645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ematchDiagSource_4646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_symPrios_4647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extensions_4648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_debug_4649_: u8 = 0;
    let mut v_ematchDiag_4650_: u8 = 0;
    let mut v_markInstances_4651_: u8 = 0;
    let mut v_lax_4652_: u8 = 0;
    let mut v_suggestions_4653_: u8 = 0;
    let mut v_locals_4654_: u8 = 0;
    let mut v_splits_4655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ematch_4656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_gen_4657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_genLocal_4658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_instances_4659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_matchEqs_4660_: u8 = 0;
    let mut v_splitMatch_4661_: u8 = 0;
    let mut v_splitIte_4662_: u8 = 0;
    let mut v_splitIndPred_4663_: u8 = 0;
    let mut v_splitImp_4664_: u8 = 0;
    let mut v_canonHeartbeats_4665_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v_ringSteps_4678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ringMaxDegree_4679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_linarith_4680_: u8 = 0;
    let mut v_lia_4681_: u8 = 0;
    let mut v_ac_4682_: u8 = 0;
    let mut v_acSteps_4683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exp_4684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_abstractProof_4685_: u8 = 0;
    let mut v_inj_4686_: u8 = 0;
    let mut v_order_4687_: u8 = 0;
    let mut v_min_4688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_detailed_4689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_useSorry_4690_: u8 = 0;
    let mut v_revert_4691_: u8 = 0;
    let mut v_funCC_4692_: u8 = 0;
    let mut v_reducible_4693_: u8 = 0;
    let mut v_maxSuggestions_4694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4695_: u8 = 0;
    let mut v___x_4696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4702_: u8 = 0;
    let mut v___x_4703_: u8 = 0;
    let mut v___x_4704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4708_: u8 = 0;
    let mut v_a_4709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4712_: u8 = 0;
    let mut v___y_4714_: u8 = 0;
    let mut v___x_4715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4722_: u8 = 0;
    let mut v___x_4723_: u8 = 0;
    let mut v_isSharedCheck_4724_: u8 = 0;
    let mut v_a_4725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4728_: u8 = 0;
    let mut v___x_4730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4731_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_4636_) == 0 {
                    lean_dec_ref_known(v___x_4636_, 1);
                    v___x_4637_ = l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg(v_seq_4624_, v___y_4633_);
                    v_config_4638_ = lean_ctor_get(v___y_4627_, 2);
                    v_a_4639_ = lean_ctor_get(v___x_4637_, 0);
                    lean_inc(v_a_4639_);
                    lean_dec_ref(v___x_4637_);
                    v_simp_4640_ = lean_ctor_get(v___y_4627_, 0);
                    v_simpMethods_4641_ = lean_ctor_get(v___y_4627_, 1);
                    v_anchorRefs_x3f_4642_ = lean_ctor_get(v___y_4627_, 3);
                    v_cheapCases_4643_ = lean_ctor_get_uint8(
                        v___y_4627_,
                        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                    );
                    v_reportMVarIssue_4644_ = lean_ctor_get_uint8(
                        v___y_4627_,
                        (core::mem::size_of::<*mut LeanObject>() * 8 + 1) as u32,
                    );
                    v_splitSource_4645_ = lean_ctor_get(v___y_4627_, 4);
                    v_ematchDiagSource_4646_ = lean_ctor_get(v___y_4627_, 5);
                    v_symPrios_4647_ = lean_ctor_get(v___y_4627_, 6);
                    v_extensions_4648_ = lean_ctor_get(v___y_4627_, 7);
                    v_debug_4649_ = lean_ctor_get_uint8(
                        v___y_4627_,
                        (core::mem::size_of::<*mut LeanObject>() * 8 + 2) as u32,
                    );
                    v_ematchDiag_4650_ = lean_ctor_get_uint8(
                        v___y_4627_,
                        (core::mem::size_of::<*mut LeanObject>() * 8 + 3) as u32,
                    );
                    v_markInstances_4651_ = lean_ctor_get_uint8(
                        v_config_4638_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
                    );
                    v_lax_4652_ = lean_ctor_get_uint8(
                        v_config_4638_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 2) as u32,
                    );
                    v_suggestions_4653_ = lean_ctor_get_uint8(
                        v_config_4638_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 3) as u32,
                    );
                    v_locals_4654_ = lean_ctor_get_uint8(
                        v_config_4638_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 4) as u32,
                    );
                    v_splits_4655_ = lean_ctor_get(v_config_4638_, 0);
                    v_ematch_4656_ = lean_ctor_get(v_config_4638_, 1);
                    v_gen_4657_ = lean_ctor_get(v_config_4638_, 2);
                    v_genLocal_4658_ = lean_ctor_get(v_config_4638_, 3);
                    v_instances_4659_ = lean_ctor_get(v_config_4638_, 4);
                    v_matchEqs_4660_ = lean_ctor_get_uint8(
                        v_config_4638_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 5) as u32,
                    );
                    v_splitMatch_4661_ = lean_ctor_get_uint8(
                        v_config_4638_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 6) as u32,
                    );
                    v_splitIte_4662_ = lean_ctor_get_uint8(
                        v_config_4638_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 7) as u32,
                    );
                    v_splitIndPred_4663_ = lean_ctor_get_uint8(
                        v_config_4638_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 8) as u32,
                    );
                    v_splitImp_4664_ = lean_ctor_get_uint8(
                        v_config_4638_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 9) as u32,
                    );
                    v_canonHeartbeats_4665_ = lean_ctor_get(v_config_4638_, 5);
                    v_ext_4666_ = lean_ctor_get_uint8(
                        v_config_4638_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 10) as u32,
                    );
                    v_extAll_4667_ = lean_ctor_get_uint8(
                        v_config_4638_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 11) as u32,
                    );
                    v_etaStruct_4668_ = lean_ctor_get_uint8(
                        v_config_4638_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 12) as u32,
                    );
                    v_funext_4669_ = lean_ctor_get_uint8(
                        v_config_4638_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 13) as u32,
                    );
                    v_lookahead_4670_ = lean_ctor_get_uint8(
                        v_config_4638_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 14) as u32,
                    );
                    v_verbose_4671_ = lean_ctor_get_uint8(
                        v_config_4638_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 15) as u32,
                    );
                    v_clean_4672_ = lean_ctor_get_uint8(
                        v_config_4638_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 16) as u32,
                    );
                    v_qlia_4673_ = lean_ctor_get_uint8(
                        v_config_4638_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 17) as u32,
                    );
                    v_mbtc_4674_ = lean_ctor_get_uint8(
                        v_config_4638_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 18) as u32,
                    );
                    v_zetaDelta_4675_ = lean_ctor_get_uint8(
                        v_config_4638_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 19) as u32,
                    );
                    v_zeta_4676_ = lean_ctor_get_uint8(
                        v_config_4638_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 20) as u32,
                    );
                    v_ring_4677_ = lean_ctor_get_uint8(
                        v_config_4638_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 21) as u32,
                    );
                    v_ringSteps_4678_ = lean_ctor_get(v_config_4638_, 6);
                    v_ringMaxDegree_4679_ = lean_ctor_get(v_config_4638_, 7);
                    v_linarith_4680_ = lean_ctor_get_uint8(
                        v_config_4638_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 22) as u32,
                    );
                    v_lia_4681_ = lean_ctor_get_uint8(
                        v_config_4638_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 23) as u32,
                    );
                    v_ac_4682_ = lean_ctor_get_uint8(
                        v_config_4638_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 24) as u32,
                    );
                    v_acSteps_4683_ = lean_ctor_get(v_config_4638_, 8);
                    v_exp_4684_ = lean_ctor_get(v_config_4638_, 9);
                    v_abstractProof_4685_ = lean_ctor_get_uint8(
                        v_config_4638_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 25) as u32,
                    );
                    v_inj_4686_ = lean_ctor_get_uint8(
                        v_config_4638_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 26) as u32,
                    );
                    v_order_4687_ = lean_ctor_get_uint8(
                        v_config_4638_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 27) as u32,
                    );
                    v_min_4688_ = lean_ctor_get(v_config_4638_, 10);
                    v_detailed_4689_ = lean_ctor_get(v_config_4638_, 11);
                    v_useSorry_4690_ = lean_ctor_get_uint8(
                        v_config_4638_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 28) as u32,
                    );
                    v_revert_4691_ = lean_ctor_get_uint8(
                        v_config_4638_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 29) as u32,
                    );
                    v_funCC_4692_ = lean_ctor_get_uint8(
                        v_config_4638_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 30) as u32,
                    );
                    v_reducible_4693_ = lean_ctor_get_uint8(
                        v_config_4638_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 31) as u32,
                    );
                    v_maxSuggestions_4694_ = lean_ctor_get(v_config_4638_, 12);
                    v___x_4695_ = 0;
                    lean_inc(v_maxSuggestions_4694_);
                    lean_inc(v_detailed_4689_);
                    lean_inc(v_min_4688_);
                    lean_inc(v_exp_4684_);
                    lean_inc(v_acSteps_4683_);
                    lean_inc(v_ringMaxDegree_4679_);
                    lean_inc(v_ringSteps_4678_);
                    lean_inc(v_canonHeartbeats_4665_);
                    lean_inc(v_instances_4659_);
                    lean_inc(v_genLocal_4658_);
                    lean_inc(v_gen_4657_);
                    lean_inc(v_ematch_4656_);
                    lean_inc(v_splits_4655_);
                    v___x_4696_ = lean_alloc_ctor(0, 13, (32) as u32);
                    lean_ctor_set(v___x_4696_, 0, v_splits_4655_);
                    lean_ctor_set(v___x_4696_, 1, v_ematch_4656_);
                    lean_ctor_set(v___x_4696_, 2, v_gen_4657_);
                    lean_ctor_set(v___x_4696_, 3, v_genLocal_4658_);
                    lean_ctor_set(v___x_4696_, 4, v_instances_4659_);
                    lean_ctor_set(v___x_4696_, 5, v_canonHeartbeats_4665_);
                    lean_ctor_set(v___x_4696_, 6, v_ringSteps_4678_);
                    lean_ctor_set(v___x_4696_, 7, v_ringMaxDegree_4679_);
                    lean_ctor_set(v___x_4696_, 8, v_acSteps_4683_);
                    lean_ctor_set(v___x_4696_, 9, v_exp_4684_);
                    lean_ctor_set(v___x_4696_, 10, v_min_4688_);
                    lean_ctor_set(v___x_4696_, 11, v_detailed_4689_);
                    lean_ctor_set(v___x_4696_, 12, v_maxSuggestions_4694_);
                    lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                        v___x_4695_,
                    );
                    lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
                        v_markInstances_4651_,
                    );
                    lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 2) as u32,
                        v_lax_4652_,
                    );
                    lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 3) as u32,
                        v_suggestions_4653_,
                    );
                    lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 4) as u32,
                        v_locals_4654_,
                    );
                    lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 5) as u32,
                        v_matchEqs_4660_,
                    );
                    lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 6) as u32,
                        v_splitMatch_4661_,
                    );
                    lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 7) as u32,
                        v_splitIte_4662_,
                    );
                    lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 8) as u32,
                        v_splitIndPred_4663_,
                    );
                    lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 9) as u32,
                        v_splitImp_4664_,
                    );
                    lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 10) as u32,
                        v_ext_4666_,
                    );
                    lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 11) as u32,
                        v_extAll_4667_,
                    );
                    lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 12) as u32,
                        v_etaStruct_4668_,
                    );
                    lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 13) as u32,
                        v_funext_4669_,
                    );
                    lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 14) as u32,
                        v_lookahead_4670_,
                    );
                    lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 15) as u32,
                        v_verbose_4671_,
                    );
                    lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 16) as u32,
                        v_clean_4672_,
                    );
                    lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 17) as u32,
                        v_qlia_4673_,
                    );
                    lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 18) as u32,
                        v_mbtc_4674_,
                    );
                    lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 19) as u32,
                        v_zetaDelta_4675_,
                    );
                    lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 20) as u32,
                        v_zeta_4676_,
                    );
                    lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 21) as u32,
                        v_ring_4677_,
                    );
                    lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 22) as u32,
                        v_linarith_4680_,
                    );
                    lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 23) as u32,
                        v_lia_4681_,
                    );
                    lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 24) as u32,
                        v_ac_4682_,
                    );
                    lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 25) as u32,
                        v_abstractProof_4685_,
                    );
                    lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 26) as u32,
                        v_inj_4686_,
                    );
                    lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 27) as u32,
                        v_order_4687_,
                    );
                    lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 28) as u32,
                        v_useSorry_4690_,
                    );
                    lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 29) as u32,
                        v_revert_4691_,
                    );
                    lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 30) as u32,
                        v_funCC_4692_,
                    );
                    lean_ctor_set_uint8(
                        v___x_4696_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 31) as u32,
                        v_reducible_4693_,
                    );
                    lean_inc_ref(v_extensions_4648_);
                    lean_inc_ref(v_symPrios_4647_);
                    lean_inc(v_ematchDiagSource_4646_);
                    lean_inc(v_splitSource_4645_);
                    lean_inc(v_anchorRefs_x3f_4642_);
                    lean_inc_ref(v_simpMethods_4641_);
                    lean_inc_ref(v_simp_4640_);
                    v___x_4697_ = lean_alloc_ctor(0, 8, (4) as u32);
                    lean_ctor_set(v___x_4697_, 0, v_simp_4640_);
                    lean_ctor_set(v___x_4697_, 1, v_simpMethods_4641_);
                    lean_ctor_set(v___x_4697_, 2, v___x_4696_);
                    lean_ctor_set(v___x_4697_, 3, v_anchorRefs_x3f_4642_);
                    lean_ctor_set(v___x_4697_, 4, v_splitSource_4645_);
                    lean_ctor_set(v___x_4697_, 5, v_ematchDiagSource_4646_);
                    lean_ctor_set(v___x_4697_, 6, v_symPrios_4647_);
                    lean_ctor_set(v___x_4697_, 7, v_extensions_4648_);
                    lean_ctor_set_uint8(
                        v___x_4697_,
                        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                        v_cheapCases_4643_,
                    );
                    lean_ctor_set_uint8(
                        v___x_4697_,
                        (core::mem::size_of::<*mut LeanObject>() * 8 + 1) as u32,
                        v_reportMVarIssue_4644_,
                    );
                    lean_ctor_set_uint8(
                        v___x_4697_,
                        (core::mem::size_of::<*mut LeanObject>() * 8 + 2) as u32,
                        v_debug_4649_,
                    );
                    lean_ctor_set_uint8(
                        v___x_4697_,
                        (core::mem::size_of::<*mut LeanObject>() * 8 + 3) as u32,
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
                    lean_dec_ref_known(v___x_4697_, 8);
                    if lean_obj_tag(v___x_4698_) == 0 {
                        v_a_4699_ = lean_ctor_get(v___x_4698_, 0);
                        v_isSharedCheck_4708_ = (!lean_is_exclusive(v___x_4698_)) as u8;
                        if v_isSharedCheck_4708_ == 0 {
                            v___x_4701_ = v___x_4698_;
                            v_isShared_4702_ = v_isSharedCheck_4708_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4699_);
                            lean_dec(v___x_4698_);
                            v___x_4701_ = lean_box(0);
                            v_isShared_4702_ = v_isSharedCheck_4708_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4709_ = lean_ctor_get(v___x_4698_, 0);
                        v_isSharedCheck_4724_ = (!lean_is_exclusive(v___x_4698_)) as u8;
                        if v_isSharedCheck_4724_ == 0 {
                            v___x_4711_ = v___x_4698_;
                            v_isShared_4712_ = v_isSharedCheck_4724_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_4709_);
                            lean_dec(v___x_4698_);
                            v___x_4711_ = lean_box(0);
                            v_isShared_4712_ = v_isSharedCheck_4724_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_goal_4625_);
                    lean_dec(v_seq_4624_);
                    v_a_4725_ = lean_ctor_get(v___x_4636_, 0);
                    v_isSharedCheck_4732_ = (!lean_is_exclusive(v___x_4636_)) as u8;
                    if v_isSharedCheck_4732_ == 0 {
                        v___x_4727_ = v___x_4636_;
                        v_isShared_4728_ = v_isSharedCheck_4732_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_4725_);
                        lean_dec(v___x_4636_);
                        v___x_4727_ = lean_box(0);
                        v_isShared_4728_ = v_isSharedCheck_4732_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4703_ = l_List_isEmpty___redArg(v_a_4699_);
                lean_dec(v_a_4699_);
                v___x_4704_ = lean_box((v___x_4703_) as usize);
                if v_isShared_4702_ == 0 {
                    lean_ctor_set(v___x_4701_, 0, v___x_4704_);
                    v___x_4706_ = v___x_4701_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4707_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4707_, 0, v___x_4704_);
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
                    lean_inc(v_a_4709_);
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
                    lean_dec(v_a_4709_);
                    v___x_4715_ = lean_box((v___y_4714_) as usize);
                    if v_isShared_4712_ == 0 {
                        lean_ctor_set_tag(v___x_4711_, 0);
                        lean_ctor_set(v___x_4711_, 0, v___x_4715_);
                        v___x_4717_ = v___x_4711_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4718_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4718_, 0, v___x_4715_);
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
                        v_reuseFailAlloc_4721_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4721_, 0, v_a_4709_);
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
                    v_reuseFailAlloc_4731_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4731_, 0, v_a_4725_);
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
    mut v_val_4733_: *mut LeanObject,
    mut v_seq_4734_: *mut LeanObject,
    mut v_goal_4735_: *mut LeanObject,
    mut v___y_4736_: *mut LeanObject,
    mut v___y_4737_: *mut LeanObject,
    mut v___y_4738_: *mut LeanObject,
    mut v___y_4739_: *mut LeanObject,
    mut v___y_4740_: *mut LeanObject,
    mut v___y_4741_: *mut LeanObject,
    mut v___y_4742_: *mut LeanObject,
    mut v___y_4743_: *mut LeanObject,
    mut v___y_4744_: *mut LeanObject,
    mut v___y_4745_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4746_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_4744_);
    lean_dec_ref(v___y_4743_);
    lean_dec(v___y_4742_);
    lean_dec_ref(v___y_4741_);
    lean_dec(v___y_4740_);
    lean_dec_ref(v___y_4739_);
    lean_dec(v___y_4738_);
    lean_dec_ref(v___y_4737_);
    lean_dec(v___y_4736_);
    return v_res_4746_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_checkSeqAt(
    mut v_s_x3f_4747_: *mut LeanObject,
    mut v_goal_4748_: *mut LeanObject,
    mut v_seq_4749_: *mut LeanObject,
    mut v_a_4750_: *mut LeanObject,
    mut v_a_4751_: *mut LeanObject,
    mut v_a_4752_: *mut LeanObject,
    mut v_a_4753_: *mut LeanObject,
    mut v_a_4754_: *mut LeanObject,
    mut v_a_4755_: *mut LeanObject,
    mut v_a_4756_: *mut LeanObject,
    mut v_a_4757_: *mut LeanObject,
    mut v_a_4758_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_s_x3f_4747_) == 1 {
        let mut v_val_4760_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_4761_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4762_: *mut LeanObject = core::ptr::null_mut();
        v_val_4760_ = lean_ctor_get(v_s_x3f_4747_, 0);
        lean_inc(v_val_4760_);
        lean_dec_ref_known(v_s_x3f_4747_, 1);
        v___f_4761_ = lean_alloc_closure(
            l_Lean_Meta_Grind_Action_checkSeqAt___lam__0___boxed as *mut core::ffi::c_void,
            13,
            3,
        );
        lean_closure_set(v___f_4761_, 0, v_val_4760_);
        lean_closure_set(v___f_4761_, 1, v_seq_4749_);
        lean_closure_set(v___f_4761_, 2, v_goal_4748_);
        v___x_4762_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Grind_Action_checkSeqAt_spec__0___redArg(v___f_4761_, v_a_4750_, v_a_4751_, v_a_4752_, v_a_4753_, v_a_4754_, v_a_4755_, v_a_4756_, v_a_4757_, v_a_4758_);
        return v___x_4762_;
    } else {
        let mut v___x_4763_: u8 = 0;
        let mut v___x_4764_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4765_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_seq_4749_);
        lean_dec_ref(v_goal_4748_);
        lean_dec(v_s_x3f_4747_);
        v___x_4763_ = 1;
        v___x_4764_ = lean_box((v___x_4763_) as usize);
        v___x_4765_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_4765_, 0, v___x_4764_);
        return v___x_4765_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Action_checkSeqAt___boxed(
    mut v_s_x3f_4766_: *mut LeanObject,
    mut v_goal_4767_: *mut LeanObject,
    mut v_seq_4768_: *mut LeanObject,
    mut v_a_4769_: *mut LeanObject,
    mut v_a_4770_: *mut LeanObject,
    mut v_a_4771_: *mut LeanObject,
    mut v_a_4772_: *mut LeanObject,
    mut v_a_4773_: *mut LeanObject,
    mut v_a_4774_: *mut LeanObject,
    mut v_a_4775_: *mut LeanObject,
    mut v_a_4776_: *mut LeanObject,
    mut v_a_4777_: *mut LeanObject,
    mut v_a_4778_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4779_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_4777_);
    lean_dec_ref(v_a_4776_);
    lean_dec(v_a_4775_);
    lean_dec_ref(v_a_4774_);
    lean_dec(v_a_4773_);
    lean_dec_ref(v_a_4772_);
    lean_dec(v_a_4771_);
    lean_dec_ref(v_a_4770_);
    lean_dec(v_a_4769_);
    return v_res_4779_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0_spec__0(
    mut v_msgData_4780_: *mut LeanObject,
    mut v___y_4781_: *mut LeanObject,
    mut v___y_4782_: *mut LeanObject,
    mut v___y_4783_: *mut LeanObject,
    mut v___y_4784_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_4789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_4790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4794_: *mut LeanObject = core::ptr::null_mut();
    v___x_4786_ = lean_st_ref_get(v___y_4784_);
    v_env_4787_ = lean_ctor_get(v___x_4786_, 0);
    lean_inc_ref(v_env_4787_);
    lean_dec(v___x_4786_);
    v___x_4788_ = lean_st_ref_get(v___y_4782_);
    v_mctx_4789_ = lean_ctor_get(v___x_4788_, 0);
    lean_inc_ref(v_mctx_4789_);
    lean_dec(v___x_4788_);
    v_lctx_4790_ = lean_ctor_get(v___y_4781_, 2);
    v_options_4791_ = lean_ctor_get(v___y_4783_, 2);
    lean_inc_ref(v_options_4791_);
    lean_inc_ref(v_lctx_4790_);
    v___x_4792_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_4792_, 0, v_env_4787_);
    lean_ctor_set(v___x_4792_, 1, v_mctx_4789_);
    lean_ctor_set(v___x_4792_, 2, v_lctx_4790_);
    lean_ctor_set(v___x_4792_, 3, v_options_4791_);
    v___x_4793_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_4793_, 0, v___x_4792_);
    lean_ctor_set(v___x_4793_, 1, v_msgData_4780_);
    v___x_4794_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4794_, 0, v___x_4793_);
    return v___x_4794_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0_spec__0___boxed(
    mut v_msgData_4795_: *mut LeanObject,
    mut v___y_4796_: *mut LeanObject,
    mut v___y_4797_: *mut LeanObject,
    mut v___y_4798_: *mut LeanObject,
    mut v___y_4799_: *mut LeanObject,
    mut v___y_4800_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4801_: *mut LeanObject = core::ptr::null_mut();
    v_res_4801_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0_spec__0(v_msgData_4795_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_);
    lean_dec(v___y_4799_);
    lean_dec_ref(v___y_4798_);
    lean_dec(v___y_4797_);
    lean_dec_ref(v___y_4796_);
    return v_res_4801_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0___redArg(
    mut v_msg_4802_: *mut LeanObject,
    mut v___y_4803_: *mut LeanObject,
    mut v___y_4804_: *mut LeanObject,
    mut v___y_4805_: *mut LeanObject,
    mut v___y_4806_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_4808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4813_: u8 = 0;
    let mut v___x_4814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4818_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4808_ = lean_ctor_get(v___y_4805_, 5);
                v___x_4809_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0_spec__0(v_msg_4802_, v___y_4803_, v___y_4804_, v___y_4805_, v___y_4806_);
                v_a_4810_ = lean_ctor_get(v___x_4809_, 0);
                v_isSharedCheck_4818_ = (!lean_is_exclusive(v___x_4809_)) as u8;
                if v_isSharedCheck_4818_ == 0 {
                    v___x_4812_ = v___x_4809_;
                    v_isShared_4813_ = v_isSharedCheck_4818_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_4810_);
                    lean_dec(v___x_4809_);
                    v___x_4812_ = lean_box(0);
                    v_isShared_4813_ = v_isSharedCheck_4818_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_4808_);
                v___x_4814_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4814_, 0, v_ref_4808_);
                lean_ctor_set(v___x_4814_, 1, v_a_4810_);
                if v_isShared_4813_ == 0 {
                    lean_ctor_set_tag(v___x_4812_, 1);
                    lean_ctor_set(v___x_4812_, 0, v___x_4814_);
                    v___x_4816_ = v___x_4812_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4817_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4817_, 0, v___x_4814_);
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
    mut v_msg_4819_: *mut LeanObject,
    mut v___y_4820_: *mut LeanObject,
    mut v___y_4821_: *mut LeanObject,
    mut v___y_4822_: *mut LeanObject,
    mut v___y_4823_: *mut LeanObject,
    mut v___y_4824_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4825_: *mut LeanObject = core::ptr::null_mut();
    v_res_4825_ = l_Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0___redArg(
        v_msg_4819_,
        v___y_4820_,
        v___y_4821_,
        v___y_4822_,
        v___y_4823_,
    );
    lean_dec(v___y_4823_);
    lean_dec_ref(v___y_4822_);
    lean_dec(v___y_4821_);
    lean_dec_ref(v___y_4820_);
    return v_res_4825_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3_spec__4(
    mut v_opts_4826_: *mut LeanObject,
    mut v_opt_4827_: *mut LeanObject,
) -> u8 {
    let mut v_name_4828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_4829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_4830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4831_: *mut LeanObject = core::ptr::null_mut();
    v_name_4828_ = lean_ctor_get(v_opt_4827_, 0);
    v_defValue_4829_ = lean_ctor_get(v_opt_4827_, 1);
    v_map_4830_ = lean_ctor_get(v_opts_4826_, 0);
    v___x_4831_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_4830_,
            v_name_4828_,
        );
    if lean_obj_tag(v___x_4831_) == 0 {
        let mut v___x_4832_: u8 = 0;
        v___x_4832_ = (lean_unbox(v_defValue_4829_) as u8);
        return v___x_4832_;
    } else {
        let mut v_val_4833_: *mut LeanObject = core::ptr::null_mut();
        v_val_4833_ = lean_ctor_get(v___x_4831_, 0);
        lean_inc(v_val_4833_);
        lean_dec_ref_known(v___x_4831_, 1);
        if lean_obj_tag(v_val_4833_) == 1 {
            let mut v_v_4834_: u8 = 0;
            v_v_4834_ = lean_ctor_get_uint8(v_val_4833_, 0 as u32);
            lean_dec_ref_known(v_val_4833_, 0);
            return v_v_4834_;
        } else {
            let mut v___x_4835_: u8 = 0;
            lean_dec(v_val_4833_);
            v___x_4835_ = (lean_unbox(v_defValue_4829_) as u8);
            return v___x_4835_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3_spec__4___boxed(
    mut v_opts_4836_: *mut LeanObject,
    mut v_opt_4837_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4838_: u8 = 0;
    let mut v_r_4839_: *mut LeanObject = core::ptr::null_mut();
    v_res_4838_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3_spec__4(v_opts_4836_, v_opt_4837_);
    lean_dec_ref(v_opt_4837_);
    lean_dec_ref(v_opts_4836_);
    v_r_4839_ = lean_box((v_res_4838_) as usize);
    return v_r_4839_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0(
    mut v___y_4847_: u8,
    mut v_suppressElabErrors_4848_: u8,
    mut v_x_4849_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_4849_) == 1 {
        let mut v_pre_4850_: *mut LeanObject = core::ptr::null_mut();
        v_pre_4850_ = lean_ctor_get(v_x_4849_, 0);
        match lean_obj_tag(v_pre_4850_) {
            1 => {
                let mut v_pre_4851_: *mut LeanObject = core::ptr::null_mut();
                v_pre_4851_ = lean_ctor_get(v_pre_4850_, 0);
                match lean_obj_tag(v_pre_4851_) {
                    0 => {
                        let mut v_str_4852_: *mut LeanObject = core::ptr::null_mut();
                        let mut v_str_4853_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_4854_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_4855_: u8 = 0;
                        v_str_4852_ = lean_ctor_get(v_x_4849_, 1);
                        v_str_4853_ = lean_ctor_get(v_pre_4850_, 1);
                        v___x_4854_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__0;
                        v___x_4855_ = lean_string_dec_eq(v_str_4853_, v___x_4854_);
                        if v___x_4855_ == 0 {
                            let mut v___x_4856_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_4857_: u8 = 0;
                            v___x_4856_ = l_Lean_Meta_Grind_Action_run___lam__0___closed__2;
                            v___x_4857_ = lean_string_dec_eq(v_str_4853_, v___x_4856_);
                            if v___x_4857_ == 0 {
                                return v___y_4847_;
                            } else {
                                let mut v___x_4858_: *mut LeanObject = core::ptr::null_mut();
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
                            let mut v___x_4860_: *mut LeanObject = core::ptr::null_mut();
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
                        let mut v_pre_4862_: *mut LeanObject = core::ptr::null_mut();
                        v_pre_4862_ = lean_ctor_get(v_pre_4851_, 0);
                        if lean_obj_tag(v_pre_4862_) == 0 {
                            let mut v_str_4863_: *mut LeanObject = core::ptr::null_mut();
                            let mut v_str_4864_: *mut LeanObject = core::ptr::null_mut();
                            let mut v_str_4865_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_4866_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_4867_: u8 = 0;
                            v_str_4863_ = lean_ctor_get(v_x_4849_, 1);
                            v_str_4864_ = lean_ctor_get(v_pre_4850_, 1);
                            v_str_4865_ = lean_ctor_get(v_pre_4851_, 1);
                            v___x_4866_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__3;
                            v___x_4867_ = lean_string_dec_eq(v_str_4865_, v___x_4866_);
                            if v___x_4867_ == 0 {
                                return v___y_4847_;
                            } else {
                                let mut v___x_4868_: *mut LeanObject = core::ptr::null_mut();
                                let mut v___x_4869_: u8 = 0;
                                v___x_4868_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__4;
                                v___x_4869_ = lean_string_dec_eq(v_str_4864_, v___x_4868_);
                                if v___x_4869_ == 0 {
                                    return v___y_4847_;
                                } else {
                                    let mut v___x_4870_: *mut LeanObject = core::ptr::null_mut();
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
                let mut v_str_4872_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4873_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4874_: u8 = 0;
                v_str_4872_ = lean_ctor_get(v_x_4849_, 1);
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
    mut v___y_4875_: *mut LeanObject,
    mut v_suppressElabErrors_4876_: *mut LeanObject,
    mut v_x_4877_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_29452__boxed_4878_: u8 = 0;
    let mut v_suppressElabErrors_boxed_4879_: u8 = 0;
    let mut v_res_4880_: u8 = 0;
    let mut v_r_4881_: *mut LeanObject = core::ptr::null_mut();
    v___y_29452__boxed_4878_ = (lean_unbox(v___y_4875_) as u8);
    v_suppressElabErrors_boxed_4879_ = (lean_unbox(v_suppressElabErrors_4876_) as u8);
    v_res_4880_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0(v___y_29452__boxed_4878_, v_suppressElabErrors_boxed_4879_, v_x_4877_);
    lean_dec(v_x_4877_);
    v_r_4881_ = lean_box((v_res_4880_) as usize);
    return v_r_4881_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg(
    mut v_ref_4883_: *mut LeanObject,
    mut v_msgData_4884_: *mut LeanObject,
    mut v_severity_4885_: u8,
    mut v_isSilent_4886_: u8,
    mut v___y_4887_: *mut LeanObject,
    mut v___y_4888_: *mut LeanObject,
    mut v___y_4889_: *mut LeanObject,
    mut v___y_4890_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4893_: u8 = 0;
    let mut v___y_4894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4899_: u8 = 0;
    let mut v___y_4900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_4907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_4909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_4910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_4911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_4912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4916_: u8 = 0;
    let mut v___x_4917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4927_: u8 = 0;
    let mut v___y_4929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4930_: u8 = 0;
    let mut v___y_4931_: u8 = 0;
    let mut v___y_4932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4934_: u8 = 0;
    let mut v___y_4935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4942_: u8 = 0;
    let mut v___x_4943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4947_: u8 = 0;
    let mut v___x_4948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4952_: u8 = 0;
    let mut v___y_4954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4955_: u8 = 0;
    let mut v___y_4956_: u8 = 0;
    let mut v___y_4957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4960_: u8 = 0;
    let mut v___y_4961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4966_: u8 = 0;
    let mut v___y_4967_: u8 = 0;
    let mut v___y_4968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4971_: u8 = 0;
    let mut v_ref_4972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4976_: u8 = 0;
    let mut v___y_4978_: u8 = 0;
    let mut v___y_4979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4983_: u8 = 0;
    let mut v___y_4984_: u8 = 0;
    let mut v___y_4986_: u8 = 0;
    let mut v_fileName_4987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4991_: u8 = 0;
    let mut v___x_4992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4995_: u8 = 0;
    let mut v___x_4996_: u8 = 0;
    let mut v___x_4997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4998_: u8 = 0;
    let mut v___x_4999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5000_: *mut LeanObject = core::ptr::null_mut();
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
                    lean_inc_ref(v_msgData_4884_);
                    v___x_5002_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_4884_);
                    v___y_4986_ = v___x_5002_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_4902_ = lean_st_ref_take(v___y_4901_);
                v_currNamespace_4903_ = lean_ctor_get(v___y_4900_, 6);
                v_openDecls_4904_ = lean_ctor_get(v___y_4900_, 7);
                v_env_4905_ = lean_ctor_get(v___x_4902_, 0);
                v_nextMacroScope_4906_ = lean_ctor_get(v___x_4902_, 1);
                v_ngen_4907_ = lean_ctor_get(v___x_4902_, 2);
                v_auxDeclNGen_4908_ = lean_ctor_get(v___x_4902_, 3);
                v_traceState_4909_ = lean_ctor_get(v___x_4902_, 4);
                v_cache_4910_ = lean_ctor_get(v___x_4902_, 5);
                v_messages_4911_ = lean_ctor_get(v___x_4902_, 6);
                v_infoState_4912_ = lean_ctor_get(v___x_4902_, 7);
                v_snapshotTasks_4913_ = lean_ctor_get(v___x_4902_, 8);
                v_isSharedCheck_4927_ = (!lean_is_exclusive(v___x_4902_)) as u8;
                if v_isSharedCheck_4927_ == 0 {
                    v___x_4915_ = v___x_4902_;
                    v_isShared_4916_ = v_isSharedCheck_4927_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_4913_);
                    lean_inc(v_infoState_4912_);
                    lean_inc(v_messages_4911_);
                    lean_inc(v_cache_4910_);
                    lean_inc(v_traceState_4909_);
                    lean_inc(v_auxDeclNGen_4908_);
                    lean_inc(v_ngen_4907_);
                    lean_inc(v_nextMacroScope_4906_);
                    lean_inc(v_env_4905_);
                    lean_dec(v___x_4902_);
                    v___x_4915_ = lean_box(0);
                    v_isShared_4916_ = v_isSharedCheck_4927_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc(v_openDecls_4904_);
                lean_inc(v_currNamespace_4903_);
                v___x_4917_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4917_, 0, v_currNamespace_4903_);
                lean_ctor_set(v___x_4917_, 1, v_openDecls_4904_);
                v___x_4918_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4918_, 0, v___x_4917_);
                lean_ctor_set(v___x_4918_, 1, v___y_4897_);
                lean_inc_ref(v___y_4895_);
                lean_inc_ref(v___y_4898_);
                v___x_4919_ = lean_alloc_ctor(0, 5, (3) as u32);
                lean_ctor_set(v___x_4919_, 0, v___y_4898_);
                lean_ctor_set(v___x_4919_, 1, v___y_4896_);
                lean_ctor_set(v___x_4919_, 2, v___y_4894_);
                lean_ctor_set(v___x_4919_, 3, v___y_4895_);
                lean_ctor_set(v___x_4919_, 4, v___x_4918_);
                lean_ctor_set_uint8(
                    v___x_4919_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    v___y_4893_,
                );
                lean_ctor_set_uint8(
                    v___x_4919_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                    v___y_4899_,
                );
                lean_ctor_set_uint8(
                    v___x_4919_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 2) as u32,
                    v_isSilent_4886_,
                );
                v___x_4920_ = l_Lean_MessageLog_add(v___x_4919_, v_messages_4911_);
                if v_isShared_4916_ == 0 {
                    lean_ctor_set(v___x_4915_, 6, v___x_4920_);
                    v___x_4922_ = v___x_4915_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4926_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4926_, 0, v_env_4905_);
                    lean_ctor_set(v_reuseFailAlloc_4926_, 1, v_nextMacroScope_4906_);
                    lean_ctor_set(v_reuseFailAlloc_4926_, 2, v_ngen_4907_);
                    lean_ctor_set(v_reuseFailAlloc_4926_, 3, v_auxDeclNGen_4908_);
                    lean_ctor_set(v_reuseFailAlloc_4926_, 4, v_traceState_4909_);
                    lean_ctor_set(v_reuseFailAlloc_4926_, 5, v_cache_4910_);
                    lean_ctor_set(v_reuseFailAlloc_4926_, 6, v___x_4920_);
                    lean_ctor_set(v_reuseFailAlloc_4926_, 7, v_infoState_4912_);
                    lean_ctor_set(v_reuseFailAlloc_4926_, 8, v_snapshotTasks_4913_);
                    v___x_4922_ = v_reuseFailAlloc_4926_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4923_ = lean_st_ref_set(v___y_4901_, v___x_4922_);
                v___x_4924_ = lean_box(0);
                v___x_4925_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4925_, 0, v___x_4924_);
                return v___x_4925_;
            }
            4 => {
                v___x_4937_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_4884_,
                    );
                v___x_4938_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0_spec__0(v___x_4937_, v___y_4887_, v___y_4888_, v___y_4889_, v___y_4890_);
                v_a_4939_ = lean_ctor_get(v___x_4938_, 0);
                v_isSharedCheck_4952_ = (!lean_is_exclusive(v___x_4938_)) as u8;
                if v_isSharedCheck_4952_ == 0 {
                    v___x_4941_ = v___x_4938_;
                    v_isShared_4942_ = v_isSharedCheck_4952_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_a_4939_);
                    lean_dec(v___x_4938_);
                    v___x_4941_ = lean_box(0);
                    v_isShared_4942_ = v_isSharedCheck_4952_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                lean_inc_ref_n(v___y_4932_, 2);
                v___x_4943_ = l_Lean_FileMap_toPosition(v___y_4932_, v___y_4935_);
                lean_dec(v___y_4935_);
                v___x_4944_ = l_Lean_FileMap_toPosition(v___y_4932_, v___y_4936_);
                lean_dec(v___y_4936_);
                v___x_4945_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4945_, 0, v___x_4944_);
                v___x_4946_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___closed__0;
                if v___y_4931_ == 0 {
                    lean_del_object(v___x_4941_);
                    lean_dec_ref(v___y_4929_);
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
                    lean_inc(v_a_4939_);
                    v___x_4947_ = l_Lean_MessageData_hasTag(v___y_4929_, v_a_4939_);
                    if v___x_4947_ == 0 {
                        lean_dec_ref_known(v___x_4945_, 1);
                        lean_dec_ref(v___x_4943_);
                        lean_dec(v_a_4939_);
                        v___x_4948_ = lean_box(0);
                        if v_isShared_4942_ == 0 {
                            lean_ctor_set(v___x_4941_, 0, v___x_4948_);
                            v___x_4950_ = v___x_4941_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_4951_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4951_, 0, v___x_4948_);
                            v___x_4950_ = v_reuseFailAlloc_4951_;
                            state = 6;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_4941_);
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
                lean_dec(v___y_4958_);
                if lean_obj_tag(v___x_4962_) == 0 {
                    lean_inc(v___y_4961_);
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
                    v_val_4963_ = lean_ctor_get(v___x_4962_, 0);
                    lean_inc(v_val_4963_);
                    lean_dec_ref_known(v___x_4962_, 1);
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
                if lean_obj_tag(v___x_4973_) == 0 {
                    v___x_4974_ = lean_unsigned_to_nat(0);
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
                    v_val_4975_ = lean_ctor_get(v___x_4973_, 0);
                    lean_inc(v_val_4975_);
                    lean_dec_ref_known(v___x_4973_, 1);
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
                    v_fileName_4987_ = lean_ctor_get(v___y_4889_, 0);
                    v_fileMap_4988_ = lean_ctor_get(v___y_4889_, 1);
                    v_options_4989_ = lean_ctor_get(v___y_4889_, 2);
                    v_ref_4990_ = lean_ctor_get(v___y_4889_, 5);
                    v_suppressElabErrors_4991_ = lean_ctor_get_uint8(
                        v___y_4889_,
                        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_4992_ = lean_box((v___y_4986_) as usize);
                    v___x_4993_ = lean_box((v_suppressElabErrors_4991_) as usize);
                    v___f_4994_ = lean_alloc_closure(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    lean_closure_set(v___f_4994_, 0, v___x_4992_);
                    lean_closure_set(v___f_4994_, 1, v___x_4993_);
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
                    lean_dec_ref(v_msgData_4884_);
                    v___x_4999_ = lean_box(0);
                    v___x_5000_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5000_, 0, v___x_4999_);
                    return v___x_5000_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___boxed(
    mut v_ref_5003_: *mut LeanObject,
    mut v_msgData_5004_: *mut LeanObject,
    mut v_severity_5005_: *mut LeanObject,
    mut v_isSilent_5006_: *mut LeanObject,
    mut v___y_5007_: *mut LeanObject,
    mut v___y_5008_: *mut LeanObject,
    mut v___y_5009_: *mut LeanObject,
    mut v___y_5010_: *mut LeanObject,
    mut v___y_5011_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_5012_: u8 = 0;
    let mut v_isSilent_boxed_5013_: u8 = 0;
    let mut v_res_5014_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_5012_ = (lean_unbox(v_severity_5005_) as u8);
    v_isSilent_boxed_5013_ = (lean_unbox(v_isSilent_5006_) as u8);
    v_res_5014_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg(v_ref_5003_, v_msgData_5004_, v_severity_boxed_5012_, v_isSilent_boxed_5013_, v___y_5007_, v___y_5008_, v___y_5009_, v___y_5010_);
    lean_dec(v___y_5010_);
    lean_dec_ref(v___y_5009_);
    lean_dec(v___y_5008_);
    lean_dec_ref(v___y_5007_);
    lean_dec(v_ref_5003_);
    return v_res_5014_;
}
pub unsafe fn l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2(
    mut v_msgData_5015_: *mut LeanObject,
    mut v_severity_5016_: u8,
    mut v_isSilent_5017_: u8,
    mut v___y_5018_: *mut LeanObject,
    mut v___y_5019_: *mut LeanObject,
    mut v___y_5020_: *mut LeanObject,
    mut v___y_5021_: *mut LeanObject,
    mut v___y_5022_: *mut LeanObject,
    mut v___y_5023_: *mut LeanObject,
    mut v___y_5024_: *mut LeanObject,
    mut v___y_5025_: *mut LeanObject,
    mut v___y_5026_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_5028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5029_: *mut LeanObject = core::ptr::null_mut();
    v_ref_5028_ = lean_ctor_get(v___y_5025_, 5);
    v___x_5029_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg(v_ref_5028_, v_msgData_5015_, v_severity_5016_, v_isSilent_5017_, v___y_5023_, v___y_5024_, v___y_5025_, v___y_5026_);
    return v___x_5029_;
}
pub unsafe fn l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2___boxed(
    mut v_msgData_5030_: *mut LeanObject,
    mut v_severity_5031_: *mut LeanObject,
    mut v_isSilent_5032_: *mut LeanObject,
    mut v___y_5033_: *mut LeanObject,
    mut v___y_5034_: *mut LeanObject,
    mut v___y_5035_: *mut LeanObject,
    mut v___y_5036_: *mut LeanObject,
    mut v___y_5037_: *mut LeanObject,
    mut v___y_5038_: *mut LeanObject,
    mut v___y_5039_: *mut LeanObject,
    mut v___y_5040_: *mut LeanObject,
    mut v___y_5041_: *mut LeanObject,
    mut v___y_5042_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_5043_: u8 = 0;
    let mut v_isSilent_boxed_5044_: u8 = 0;
    let mut v_res_5045_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_5043_ = (lean_unbox(v_severity_5031_) as u8);
    v_isSilent_boxed_5044_ = (lean_unbox(v_isSilent_5032_) as u8);
    v_res_5045_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2(v_msgData_5030_, v_severity_boxed_5043_, v_isSilent_boxed_5044_, v___y_5033_, v___y_5034_, v___y_5035_, v___y_5036_, v___y_5037_, v___y_5038_, v___y_5039_, v___y_5040_, v___y_5041_);
    lean_dec(v___y_5041_);
    lean_dec_ref(v___y_5040_);
    lean_dec(v___y_5039_);
    lean_dec_ref(v___y_5038_);
    lean_dec(v___y_5037_);
    lean_dec_ref(v___y_5036_);
    lean_dec(v___y_5035_);
    lean_dec_ref(v___y_5034_);
    lean_dec(v___y_5033_);
    return v_res_5045_;
}
pub unsafe fn l_Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1(
    mut v_msgData_5046_: *mut LeanObject,
    mut v___y_5047_: *mut LeanObject,
    mut v___y_5048_: *mut LeanObject,
    mut v___y_5049_: *mut LeanObject,
    mut v___y_5050_: *mut LeanObject,
    mut v___y_5051_: *mut LeanObject,
    mut v___y_5052_: *mut LeanObject,
    mut v___y_5053_: *mut LeanObject,
    mut v___y_5054_: *mut LeanObject,
    mut v___y_5055_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5057_: u8 = 0;
    let mut v___x_5058_: u8 = 0;
    let mut v___x_5059_: *mut LeanObject = core::ptr::null_mut();
    v___x_5057_ = 1;
    v___x_5058_ = 0;
    v___x_5059_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2(v_msgData_5046_, v___x_5057_, v___x_5058_, v___y_5047_, v___y_5048_, v___y_5049_, v___y_5050_, v___y_5051_, v___y_5052_, v___y_5053_, v___y_5054_, v___y_5055_);
    return v___x_5059_;
}
pub unsafe fn l_Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1___boxed(
    mut v_msgData_5060_: *mut LeanObject,
    mut v___y_5061_: *mut LeanObject,
    mut v___y_5062_: *mut LeanObject,
    mut v___y_5063_: *mut LeanObject,
    mut v___y_5064_: *mut LeanObject,
    mut v___y_5065_: *mut LeanObject,
    mut v___y_5066_: *mut LeanObject,
    mut v___y_5067_: *mut LeanObject,
    mut v___y_5068_: *mut LeanObject,
    mut v___y_5069_: *mut LeanObject,
    mut v___y_5070_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5071_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_5069_);
    lean_dec_ref(v___y_5068_);
    lean_dec(v___y_5067_);
    lean_dec_ref(v___y_5066_);
    lean_dec(v___y_5065_);
    lean_dec_ref(v___y_5064_);
    lean_dec(v___y_5063_);
    lean_dec_ref(v___y_5062_);
    lean_dec(v___y_5061_);
    return v_res_5071_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__1() -> *mut LeanObject {
    let mut v___x_5073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5074_: *mut LeanObject = core::ptr::null_mut();
    v___x_5073_ = l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__0;
    v___x_5074_ = l_Lean_stringToMessageData(v___x_5073_);
    return v___x_5074_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__3() -> *mut LeanObject {
    let mut v___x_5076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5077_: *mut LeanObject = core::ptr::null_mut();
    v___x_5076_ = l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__2;
    v___x_5077_ = l_Lean_stringToMessageData(v___x_5076_);
    return v___x_5077_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_checkTactic___redArg(
    mut v_warnOnly_5078_: u8,
    mut v_goal_5079_: *mut LeanObject,
    mut v_kp_5080_: *mut LeanObject,
    mut v_a_5081_: *mut LeanObject,
    mut v_a_5082_: *mut LeanObject,
    mut v_a_5083_: *mut LeanObject,
    mut v_a_5084_: *mut LeanObject,
    mut v_a_5085_: *mut LeanObject,
    mut v_a_5086_: *mut LeanObject,
    mut v_a_5087_: *mut LeanObject,
    mut v_a_5088_: *mut LeanObject,
    mut v_a_5089_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_seq_5095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5100_: u8 = 0;
    let mut v___x_5101_: u8 = 0;
    let mut v___x_5102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5106_: u8 = 0;
    let mut v_mvarId_5107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5110_: u8 = 0;
    let mut v___x_5111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5125_: u8 = 0;
    let mut v___x_5127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5129_: u8 = 0;
    let mut v___x_5130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5133_: u8 = 0;
    let mut v___x_5135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5137_: u8 = 0;
    let mut v_unused_5138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5142_: u8 = 0;
    let mut v___x_5144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5146_: u8 = 0;
    let mut v_reuseFailAlloc_5147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5149_: u8 = 0;
    let mut v_unused_5150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5151_: u8 = 0;
    let mut v___x_5153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5155_: u8 = 0;
    let mut v_a_5156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5159_: u8 = 0;
    let mut v___x_5161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5163_: u8 = 0;
    let mut v_a_5164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5167_: u8 = 0;
    let mut v___x_5169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5171_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5091_ = l_Lean_Meta_Grind_Action_saveStateIfTracing___redArg(
                    v_a_5082_, v_a_5083_, v_a_5087_, v_a_5089_,
                );
                if lean_obj_tag(v___x_5091_) == 0 {
                    v_a_5092_ = lean_ctor_get(v___x_5091_, 0);
                    lean_inc(v_a_5092_);
                    lean_dec_ref_known(v___x_5091_, 1);
                    lean_inc(v_a_5089_);
                    lean_inc_ref(v_a_5088_);
                    lean_inc(v_a_5087_);
                    lean_inc_ref(v_a_5086_);
                    lean_inc(v_a_5085_);
                    lean_inc_ref(v_a_5084_);
                    lean_inc(v_a_5083_);
                    lean_inc_ref(v_a_5082_);
                    lean_inc(v_a_5081_);
                    lean_inc_ref(v_goal_5079_);
                    v___x_5093_ = lean_apply_11(
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
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_5093_) == 0 {
                        v_a_5094_ = lean_ctor_get(v___x_5093_, 0);
                        lean_inc(v_a_5094_);
                        if lean_obj_tag(v_a_5094_) == 0 {
                            lean_dec_ref_known(v___x_5093_, 1);
                            v_seq_5095_ = lean_ctor_get(v_a_5094_, 0);
                            lean_inc(v_seq_5095_);
                            lean_inc_ref(v_goal_5079_);
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
                            if lean_obj_tag(v___x_5096_) == 0 {
                                v_a_5097_ = lean_ctor_get(v___x_5096_, 0);
                                v_isSharedCheck_5155_ = (!lean_is_exclusive(v___x_5096_)) as u8;
                                if v_isSharedCheck_5155_ == 0 {
                                    v___x_5099_ = v___x_5096_;
                                    v_isShared_5100_ = v_isSharedCheck_5155_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_a_5097_);
                                    lean_dec(v___x_5096_);
                                    v___x_5099_ = lean_box(0);
                                    v_isShared_5100_ = v_isSharedCheck_5155_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec_ref_known(v_a_5094_, 1);
                                lean_dec_ref(v_goal_5079_);
                                v_a_5156_ = lean_ctor_get(v___x_5096_, 0);
                                v_isSharedCheck_5163_ = (!lean_is_exclusive(v___x_5096_)) as u8;
                                if v_isSharedCheck_5163_ == 0 {
                                    v___x_5158_ = v___x_5096_;
                                    v_isShared_5159_ = v_isSharedCheck_5163_;
                                    state = 13;
                                    continue;
                                } else {
                                    lean_inc(v_a_5156_);
                                    lean_dec(v___x_5096_);
                                    v___x_5158_ = lean_box(0);
                                    v_isShared_5159_ = v_isSharedCheck_5163_;
                                    state = 13;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_5094_);
                            lean_dec(v_a_5092_);
                            lean_dec_ref(v_goal_5079_);
                            return v___x_5093_;
                        }
                    } else {
                        lean_dec(v_a_5092_);
                        lean_dec_ref(v_goal_5079_);
                        return v___x_5093_;
                    }
                } else {
                    lean_dec_ref(v_kp_5080_);
                    lean_dec_ref(v_goal_5079_);
                    v_a_5164_ = lean_ctor_get(v___x_5091_, 0);
                    v_isSharedCheck_5171_ = (!lean_is_exclusive(v___x_5091_)) as u8;
                    if v_isSharedCheck_5171_ == 0 {
                        v___x_5166_ = v___x_5091_;
                        v_isShared_5167_ = v_isSharedCheck_5171_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_5164_);
                        lean_dec(v___x_5091_);
                        v___x_5166_ = lean_box(0);
                        v_isShared_5167_ = v_isSharedCheck_5171_;
                        state = 15;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5101_ = (lean_unbox(v_a_5097_) as u8);
                lean_dec(v_a_5097_);
                if v___x_5101_ == 0 {
                    lean_del_object(v___x_5099_);
                    lean_inc(v_seq_5095_);
                    v___x_5102_ =
                        l_Lean_Meta_Grind_Action_mkGrindNext___redArg(v_seq_5095_, v_a_5088_);
                    v_a_5103_ = lean_ctor_get(v___x_5102_, 0);
                    v_isSharedCheck_5151_ = (!lean_is_exclusive(v___x_5102_)) as u8;
                    if v_isSharedCheck_5151_ == 0 {
                        v___x_5105_ = v___x_5102_;
                        v_isShared_5106_ = v_isSharedCheck_5151_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_5103_);
                        lean_dec(v___x_5102_);
                        v___x_5105_ = lean_box(0);
                        v_isShared_5106_ = v_isSharedCheck_5151_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_goal_5079_);
                    if v_isShared_5100_ == 0 {
                        lean_ctor_set(v___x_5099_, 0, v_a_5094_);
                        v___x_5153_ = v___x_5099_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_5154_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5154_, 0, v_a_5094_);
                        v___x_5153_ = v_reuseFailAlloc_5154_;
                        state = 12;
                        continue;
                    }
                }
            }
            2 => {
                v_mvarId_5107_ = lean_ctor_get(v_goal_5079_, 1);
                v_isSharedCheck_5149_ = (!lean_is_exclusive(v_goal_5079_)) as u8;
                if v_isSharedCheck_5149_ == 0 {
                    v_unused_5150_ = lean_ctor_get(v_goal_5079_, 0);
                    lean_dec(v_unused_5150_);
                    v___x_5109_ = v_goal_5079_;
                    v_isShared_5110_ = v_isSharedCheck_5149_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_mvarId_5107_);
                    lean_dec(v_goal_5079_);
                    v___x_5109_ = lean_box(0);
                    v_isShared_5110_ = v_isSharedCheck_5149_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5111_ = lean_obj_once(
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
                    lean_ctor_set_tag(v___x_5109_, 7);
                    lean_ctor_set(v___x_5109_, 1, v___x_5113_);
                    lean_ctor_set(v___x_5109_, 0, v___x_5111_);
                    v___x_5115_ = v___x_5109_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5148_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5148_, 0, v___x_5111_);
                    lean_ctor_set(v_reuseFailAlloc_5148_, 1, v___x_5113_);
                    v___x_5115_ = v_reuseFailAlloc_5148_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5116_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__3_once
                    ),
                    _init_l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__3,
                );
                v___x_5117_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5117_, 0, v___x_5115_);
                lean_ctor_set(v___x_5117_, 1, v___x_5116_);
                if v_isShared_5106_ == 0 {
                    lean_ctor_set_tag(v___x_5105_, 1);
                    lean_ctor_set(v___x_5105_, 0, v_mvarId_5107_);
                    v___x_5119_ = v___x_5105_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5147_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5147_, 0, v_mvarId_5107_);
                    v___x_5119_ = v_reuseFailAlloc_5147_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5120_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5120_, 0, v___x_5117_);
                lean_ctor_set(v___x_5120_, 1, v___x_5119_);
                if v_warnOnly_5078_ == 0 {
                    lean_dec_ref_known(v_a_5094_, 1);
                    v___x_5121_ = l_Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0___redArg(v___x_5120_, v_a_5086_, v_a_5087_, v_a_5088_, v_a_5089_);
                    v_a_5122_ = lean_ctor_get(v___x_5121_, 0);
                    v_isSharedCheck_5129_ = (!lean_is_exclusive(v___x_5121_)) as u8;
                    if v_isSharedCheck_5129_ == 0 {
                        v___x_5124_ = v___x_5121_;
                        v_isShared_5125_ = v_isSharedCheck_5129_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_5122_);
                        lean_dec(v___x_5121_);
                        v___x_5124_ = lean_box(0);
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
                    if lean_obj_tag(v___x_5130_) == 0 {
                        v_isSharedCheck_5137_ = (!lean_is_exclusive(v___x_5130_)) as u8;
                        if v_isSharedCheck_5137_ == 0 {
                            v_unused_5138_ = lean_ctor_get(v___x_5130_, 0);
                            lean_dec(v_unused_5138_);
                            v___x_5132_ = v___x_5130_;
                            v_isShared_5133_ = v_isSharedCheck_5137_;
                            state = 8;
                            continue;
                        } else {
                            lean_dec(v___x_5130_);
                            v___x_5132_ = lean_box(0);
                            v_isShared_5133_ = v_isSharedCheck_5137_;
                            state = 8;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_a_5094_, 1);
                        v_a_5139_ = lean_ctor_get(v___x_5130_, 0);
                        v_isSharedCheck_5146_ = (!lean_is_exclusive(v___x_5130_)) as u8;
                        if v_isSharedCheck_5146_ == 0 {
                            v___x_5141_ = v___x_5130_;
                            v_isShared_5142_ = v_isSharedCheck_5146_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_5139_);
                            lean_dec(v___x_5130_);
                            v___x_5141_ = lean_box(0);
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
                    v_reuseFailAlloc_5128_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5128_, 0, v_a_5122_);
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
                    lean_ctor_set(v___x_5132_, 0, v_a_5094_);
                    v___x_5135_ = v___x_5132_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5136_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5136_, 0, v_a_5094_);
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
                    v_reuseFailAlloc_5145_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5145_, 0, v_a_5139_);
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
                    v_reuseFailAlloc_5162_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5162_, 0, v_a_5156_);
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
                    v_reuseFailAlloc_5170_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5170_, 0, v_a_5164_);
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
    mut v_warnOnly_5172_: *mut LeanObject,
    mut v_goal_5173_: *mut LeanObject,
    mut v_kp_5174_: *mut LeanObject,
    mut v_a_5175_: *mut LeanObject,
    mut v_a_5176_: *mut LeanObject,
    mut v_a_5177_: *mut LeanObject,
    mut v_a_5178_: *mut LeanObject,
    mut v_a_5179_: *mut LeanObject,
    mut v_a_5180_: *mut LeanObject,
    mut v_a_5181_: *mut LeanObject,
    mut v_a_5182_: *mut LeanObject,
    mut v_a_5183_: *mut LeanObject,
    mut v_a_5184_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_warnOnly_boxed_5185_: u8 = 0;
    let mut v_res_5186_: *mut LeanObject = core::ptr::null_mut();
    v_warnOnly_boxed_5185_ = (lean_unbox(v_warnOnly_5172_) as u8);
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
    lean_dec(v_a_5183_);
    lean_dec_ref(v_a_5182_);
    lean_dec(v_a_5181_);
    lean_dec_ref(v_a_5180_);
    lean_dec(v_a_5179_);
    lean_dec_ref(v_a_5178_);
    lean_dec(v_a_5177_);
    lean_dec_ref(v_a_5176_);
    lean_dec(v_a_5175_);
    return v_res_5186_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_checkTactic(
    mut v_warnOnly_5187_: u8,
    mut v_goal_5188_: *mut LeanObject,
    mut v_x_5189_: *mut LeanObject,
    mut v_kp_5190_: *mut LeanObject,
    mut v_a_5191_: *mut LeanObject,
    mut v_a_5192_: *mut LeanObject,
    mut v_a_5193_: *mut LeanObject,
    mut v_a_5194_: *mut LeanObject,
    mut v_a_5195_: *mut LeanObject,
    mut v_a_5196_: *mut LeanObject,
    mut v_a_5197_: *mut LeanObject,
    mut v_a_5198_: *mut LeanObject,
    mut v_a_5199_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5201_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_warnOnly_5202_: *mut LeanObject,
    mut v_goal_5203_: *mut LeanObject,
    mut v_x_5204_: *mut LeanObject,
    mut v_kp_5205_: *mut LeanObject,
    mut v_a_5206_: *mut LeanObject,
    mut v_a_5207_: *mut LeanObject,
    mut v_a_5208_: *mut LeanObject,
    mut v_a_5209_: *mut LeanObject,
    mut v_a_5210_: *mut LeanObject,
    mut v_a_5211_: *mut LeanObject,
    mut v_a_5212_: *mut LeanObject,
    mut v_a_5213_: *mut LeanObject,
    mut v_a_5214_: *mut LeanObject,
    mut v_a_5215_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_warnOnly_boxed_5216_: u8 = 0;
    let mut v_res_5217_: *mut LeanObject = core::ptr::null_mut();
    v_warnOnly_boxed_5216_ = (lean_unbox(v_warnOnly_5202_) as u8);
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
    lean_dec(v_a_5214_);
    lean_dec_ref(v_a_5213_);
    lean_dec(v_a_5212_);
    lean_dec_ref(v_a_5211_);
    lean_dec(v_a_5210_);
    lean_dec_ref(v_a_5209_);
    lean_dec(v_a_5208_);
    lean_dec_ref(v_a_5207_);
    lean_dec(v_a_5206_);
    lean_dec_ref(v_x_5204_);
    return v_res_5217_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0(
    mut v_00_u03b1_5218_: *mut LeanObject,
    mut v_msg_5219_: *mut LeanObject,
    mut v___y_5220_: *mut LeanObject,
    mut v___y_5221_: *mut LeanObject,
    mut v___y_5222_: *mut LeanObject,
    mut v___y_5223_: *mut LeanObject,
    mut v___y_5224_: *mut LeanObject,
    mut v___y_5225_: *mut LeanObject,
    mut v___y_5226_: *mut LeanObject,
    mut v___y_5227_: *mut LeanObject,
    mut v___y_5228_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5230_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_5231_: *mut LeanObject,
    mut v_msg_5232_: *mut LeanObject,
    mut v___y_5233_: *mut LeanObject,
    mut v___y_5234_: *mut LeanObject,
    mut v___y_5235_: *mut LeanObject,
    mut v___y_5236_: *mut LeanObject,
    mut v___y_5237_: *mut LeanObject,
    mut v___y_5238_: *mut LeanObject,
    mut v___y_5239_: *mut LeanObject,
    mut v___y_5240_: *mut LeanObject,
    mut v___y_5241_: *mut LeanObject,
    mut v___y_5242_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5243_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_5241_);
    lean_dec_ref(v___y_5240_);
    lean_dec(v___y_5239_);
    lean_dec_ref(v___y_5238_);
    lean_dec(v___y_5237_);
    lean_dec_ref(v___y_5236_);
    lean_dec(v___y_5235_);
    lean_dec_ref(v___y_5234_);
    lean_dec(v___y_5233_);
    return v_res_5243_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3(
    mut v_ref_5244_: *mut LeanObject,
    mut v_msgData_5245_: *mut LeanObject,
    mut v_severity_5246_: u8,
    mut v_isSilent_5247_: u8,
    mut v___y_5248_: *mut LeanObject,
    mut v___y_5249_: *mut LeanObject,
    mut v___y_5250_: *mut LeanObject,
    mut v___y_5251_: *mut LeanObject,
    mut v___y_5252_: *mut LeanObject,
    mut v___y_5253_: *mut LeanObject,
    mut v___y_5254_: *mut LeanObject,
    mut v___y_5255_: *mut LeanObject,
    mut v___y_5256_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5258_: *mut LeanObject = core::ptr::null_mut();
    v___x_5258_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg(v_ref_5244_, v_msgData_5245_, v_severity_5246_, v_isSilent_5247_, v___y_5253_, v___y_5254_, v___y_5255_, v___y_5256_);
    return v___x_5258_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___boxed(
    mut v_ref_5259_: *mut LeanObject,
    mut v_msgData_5260_: *mut LeanObject,
    mut v_severity_5261_: *mut LeanObject,
    mut v_isSilent_5262_: *mut LeanObject,
    mut v___y_5263_: *mut LeanObject,
    mut v___y_5264_: *mut LeanObject,
    mut v___y_5265_: *mut LeanObject,
    mut v___y_5266_: *mut LeanObject,
    mut v___y_5267_: *mut LeanObject,
    mut v___y_5268_: *mut LeanObject,
    mut v___y_5269_: *mut LeanObject,
    mut v___y_5270_: *mut LeanObject,
    mut v___y_5271_: *mut LeanObject,
    mut v___y_5272_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_5273_: u8 = 0;
    let mut v_isSilent_boxed_5274_: u8 = 0;
    let mut v_res_5275_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_5273_ = (lean_unbox(v_severity_5261_) as u8);
    v_isSilent_boxed_5274_ = (lean_unbox(v_isSilent_5262_) as u8);
    v_res_5275_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3(v_ref_5259_, v_msgData_5260_, v_severity_boxed_5273_, v_isSilent_boxed_5274_, v___y_5263_, v___y_5264_, v___y_5265_, v___y_5266_, v___y_5267_, v___y_5268_, v___y_5269_, v___y_5270_, v___y_5271_);
    lean_dec(v___y_5271_);
    lean_dec_ref(v___y_5270_);
    lean_dec(v___y_5269_);
    lean_dec_ref(v___y_5268_);
    lean_dec(v___y_5267_);
    lean_dec_ref(v___y_5266_);
    lean_dec(v___y_5265_);
    lean_dec_ref(v___y_5264_);
    lean_dec(v___y_5263_);
    lean_dec(v_ref_5259_);
    return v_res_5275_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_solverAction___lam__0(
    mut v_goal_5276_: *mut LeanObject,
    mut v_check_5277_: *mut LeanObject,
    mut v___y_5278_: *mut LeanObject,
    mut v___y_5279_: *mut LeanObject,
    mut v___y_5280_: *mut LeanObject,
    mut v___y_5281_: *mut LeanObject,
    mut v___y_5282_: *mut LeanObject,
    mut v___y_5283_: *mut LeanObject,
    mut v___y_5284_: *mut LeanObject,
    mut v___y_5285_: *mut LeanObject,
    mut v___y_5286_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5293_: u8 = 0;
    let mut v___x_5294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5299_: u8 = 0;
    let mut v_a_5300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5303_: u8 = 0;
    let mut v___x_5305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5307_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5288_ = lean_st_mk_ref(v_goal_5276_);
                lean_inc(v___x_5288_);
                v___x_5289_ = lean_apply_11(
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
                    lean_box(0),
                );
                if lean_obj_tag(v___x_5289_) == 0 {
                    v_a_5290_ = lean_ctor_get(v___x_5289_, 0);
                    v_isSharedCheck_5299_ = (!lean_is_exclusive(v___x_5289_)) as u8;
                    if v_isSharedCheck_5299_ == 0 {
                        v___x_5292_ = v___x_5289_;
                        v_isShared_5293_ = v_isSharedCheck_5299_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5290_);
                        lean_dec(v___x_5289_);
                        v___x_5292_ = lean_box(0);
                        v_isShared_5293_ = v_isSharedCheck_5299_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_5288_);
                    v_a_5300_ = lean_ctor_get(v___x_5289_, 0);
                    v_isSharedCheck_5307_ = (!lean_is_exclusive(v___x_5289_)) as u8;
                    if v_isSharedCheck_5307_ == 0 {
                        v___x_5302_ = v___x_5289_;
                        v_isShared_5303_ = v_isSharedCheck_5307_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5300_);
                        lean_dec(v___x_5289_);
                        v___x_5302_ = lean_box(0);
                        v_isShared_5303_ = v_isSharedCheck_5307_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5294_ = lean_st_ref_get(v___x_5288_);
                lean_dec(v___x_5288_);
                v___x_5295_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5295_, 0, v_a_5290_);
                lean_ctor_set(v___x_5295_, 1, v___x_5294_);
                if v_isShared_5293_ == 0 {
                    lean_ctor_set(v___x_5292_, 0, v___x_5295_);
                    v___x_5297_ = v___x_5292_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5298_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5298_, 0, v___x_5295_);
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
                    v_reuseFailAlloc_5306_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5306_, 0, v_a_5300_);
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
    mut v_goal_5308_: *mut LeanObject,
    mut v_check_5309_: *mut LeanObject,
    mut v___y_5310_: *mut LeanObject,
    mut v___y_5311_: *mut LeanObject,
    mut v___y_5312_: *mut LeanObject,
    mut v___y_5313_: *mut LeanObject,
    mut v___y_5314_: *mut LeanObject,
    mut v___y_5315_: *mut LeanObject,
    mut v___y_5316_: *mut LeanObject,
    mut v___y_5317_: *mut LeanObject,
    mut v___y_5318_: *mut LeanObject,
    mut v___y_5319_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5320_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_snd_5321_: *mut LeanObject,
    mut v___y_5322_: *mut LeanObject,
    mut v___y_5323_: *mut LeanObject,
    mut v___y_5324_: *mut LeanObject,
    mut v___y_5325_: *mut LeanObject,
    mut v___y_5326_: *mut LeanObject,
    mut v___y_5327_: *mut LeanObject,
    mut v___y_5328_: *mut LeanObject,
    mut v___y_5329_: *mut LeanObject,
    mut v___y_5330_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5336_: u8 = 0;
    let mut v___x_5337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5342_: u8 = 0;
    let mut v_unused_5343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5347_: u8 = 0;
    let mut v___x_5349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5351_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5332_ = lean_st_mk_ref(v_snd_5321_);
                lean_inc(v___y_5330_);
                lean_inc_ref(v___y_5329_);
                lean_inc(v___y_5328_);
                lean_inc_ref(v___y_5327_);
                lean_inc(v___y_5326_);
                lean_inc_ref(v___y_5325_);
                lean_inc(v___y_5324_);
                lean_inc_ref(v___y_5323_);
                lean_inc(v___y_5322_);
                lean_inc(v___x_5332_);
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
                if lean_obj_tag(v___x_5333_) == 0 {
                    v_isSharedCheck_5342_ = (!lean_is_exclusive(v___x_5333_)) as u8;
                    if v_isSharedCheck_5342_ == 0 {
                        v_unused_5343_ = lean_ctor_get(v___x_5333_, 0);
                        lean_dec(v_unused_5343_);
                        v___x_5335_ = v___x_5333_;
                        v_isShared_5336_ = v_isSharedCheck_5342_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_5333_);
                        v___x_5335_ = lean_box(0);
                        v_isShared_5336_ = v_isSharedCheck_5342_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_5332_);
                    v_a_5344_ = lean_ctor_get(v___x_5333_, 0);
                    v_isSharedCheck_5351_ = (!lean_is_exclusive(v___x_5333_)) as u8;
                    if v_isSharedCheck_5351_ == 0 {
                        v___x_5346_ = v___x_5333_;
                        v_isShared_5347_ = v_isSharedCheck_5351_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5344_);
                        lean_dec(v___x_5333_);
                        v___x_5346_ = lean_box(0);
                        v_isShared_5347_ = v_isSharedCheck_5351_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5337_ = lean_st_ref_get(v___x_5332_);
                v___x_5338_ = lean_st_ref_get(v___x_5332_);
                lean_dec(v___x_5332_);
                lean_dec(v___x_5338_);
                if v_isShared_5336_ == 0 {
                    lean_ctor_set(v___x_5335_, 0, v___x_5337_);
                    v___x_5340_ = v___x_5335_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5341_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5341_, 0, v___x_5337_);
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
                    v_reuseFailAlloc_5350_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5350_, 0, v_a_5344_);
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
    mut v_snd_5352_: *mut LeanObject,
    mut v___y_5353_: *mut LeanObject,
    mut v___y_5354_: *mut LeanObject,
    mut v___y_5355_: *mut LeanObject,
    mut v___y_5356_: *mut LeanObject,
    mut v___y_5357_: *mut LeanObject,
    mut v___y_5358_: *mut LeanObject,
    mut v___y_5359_: *mut LeanObject,
    mut v___y_5360_: *mut LeanObject,
    mut v___y_5361_: *mut LeanObject,
    mut v___y_5362_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5363_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_5361_);
    lean_dec_ref(v___y_5360_);
    lean_dec(v___y_5359_);
    lean_dec_ref(v___y_5358_);
    lean_dec(v___y_5357_);
    lean_dec_ref(v___y_5356_);
    lean_dec(v___y_5355_);
    lean_dec_ref(v___y_5354_);
    lean_dec(v___y_5353_);
    return v_res_5363_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_solverAction(
    mut v_check_5364_: *mut LeanObject,
    mut v_mkTac_5365_: *mut LeanObject,
    mut v_goal_5366_: *mut LeanObject,
    mut v_kna_5367_: *mut LeanObject,
    mut v_kp_5368_: *mut LeanObject,
    mut v_a_5369_: *mut LeanObject,
    mut v_a_5370_: *mut LeanObject,
    mut v_a_5371_: *mut LeanObject,
    mut v_a_5372_: *mut LeanObject,
    mut v_a_5373_: *mut LeanObject,
    mut v_a_5374_: *mut LeanObject,
    mut v_a_5375_: *mut LeanObject,
    mut v_a_5376_: *mut LeanObject,
    mut v_a_5377_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarId_5381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5386_: u8 = 0;
    let mut v_snd_5387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5394_: u8 = 0;
    let mut v_mvarId_5395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toGoalState_5399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inconsistent_5400_: u8 = 0;
    let mut v___x_5401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trace_5403_: u8 = 0;
    let mut v___x_5404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_seq_5407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5412_: u8 = 0;
    let mut v___x_5413_: u8 = 0;
    let mut v___x_5415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5416_: u8 = 0;
    let mut v___x_5417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5421_: u8 = 0;
    let mut v___x_5423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5431_: u8 = 0;
    let mut v_a_5432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5435_: u8 = 0;
    let mut v___x_5437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5439_: u8 = 0;
    let mut v_isSharedCheck_5440_: u8 = 0;
    let mut v_unused_5441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5445_: u8 = 0;
    let mut v_a_5446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5449_: u8 = 0;
    let mut v___x_5451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5453_: u8 = 0;
    let mut v_a_5454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5457_: u8 = 0;
    let mut v___x_5459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5461_: u8 = 0;
    let mut v___x_5462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5466_: u8 = 0;
    let mut v___x_5468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5470_: u8 = 0;
    let mut v_isSharedCheck_5471_: u8 = 0;
    let mut v_unused_5472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5477_: u8 = 0;
    let mut v___x_5479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5481_: u8 = 0;
    let mut v_a_5482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5485_: u8 = 0;
    let mut v___x_5487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5489_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5379_ = l_Lean_Meta_Grind_Action_saveStateIfTracing___redArg(
                    v_a_5370_, v_a_5371_, v_a_5375_, v_a_5377_,
                );
                if lean_obj_tag(v___x_5379_) == 0 {
                    v_a_5380_ = lean_ctor_get(v___x_5379_, 0);
                    lean_inc(v_a_5380_);
                    lean_dec_ref_known(v___x_5379_, 1);
                    v_mvarId_5381_ = lean_ctor_get(v_goal_5366_, 1);
                    lean_inc_ref(v_goal_5366_);
                    v___f_5382_ = lean_alloc_closure(
                        l_Lean_Meta_Grind_Action_solverAction___lam__0___boxed
                            as *mut core::ffi::c_void,
                        12,
                        2,
                    );
                    lean_closure_set(v___f_5382_, 0, v_goal_5366_);
                    lean_closure_set(v___f_5382_, 1, v_check_5364_);
                    lean_inc(v_mvarId_5381_);
                    v___x_5383_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg(v_mvarId_5381_, v___f_5382_, v_a_5369_, v_a_5370_, v_a_5371_, v_a_5372_, v_a_5373_, v_a_5374_, v_a_5375_, v_a_5376_, v_a_5377_);
                    if lean_obj_tag(v___x_5383_) == 0 {
                        v_a_5384_ = lean_ctor_get(v___x_5383_, 0);
                        lean_inc(v_a_5384_);
                        lean_dec_ref_known(v___x_5383_, 1);
                        v_fst_5385_ = lean_ctor_get(v_a_5384_, 0);
                        v___x_5386_ = (lean_unbox(v_fst_5385_) as u8);
                        match v___x_5386_ {
                            0 => {
                                lean_dec(v_a_5380_);
                                lean_dec_ref(v_kp_5368_);
                                lean_dec_ref(v_goal_5366_);
                                lean_dec_ref(v_mkTac_5365_);
                                v_snd_5387_ = lean_ctor_get(v_a_5384_, 1);
                                lean_inc(v_snd_5387_);
                                lean_dec(v_a_5384_);
                                lean_inc(v_a_5377_);
                                lean_inc_ref(v_a_5376_);
                                lean_inc(v_a_5375_);
                                lean_inc_ref(v_a_5374_);
                                lean_inc(v_a_5373_);
                                lean_inc_ref(v_a_5372_);
                                lean_inc(v_a_5371_);
                                lean_inc_ref(v_a_5370_);
                                lean_inc(v_a_5369_);
                                v___x_5388_ = lean_apply_11(
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
                                    lean_box(0),
                                );
                                return v___x_5388_;
                            }
                            1 => {
                                lean_dec(v_a_5380_);
                                lean_dec_ref(v_kna_5367_);
                                lean_dec_ref(v_goal_5366_);
                                lean_dec_ref(v_mkTac_5365_);
                                v_snd_5389_ = lean_ctor_get(v_a_5384_, 1);
                                lean_inc(v_snd_5389_);
                                lean_dec(v_a_5384_);
                                lean_inc(v_a_5377_);
                                lean_inc_ref(v_a_5376_);
                                lean_inc(v_a_5375_);
                                lean_inc_ref(v_a_5374_);
                                lean_inc(v_a_5373_);
                                lean_inc_ref(v_a_5372_);
                                lean_inc(v_a_5371_);
                                lean_inc_ref(v_a_5370_);
                                lean_inc(v_a_5369_);
                                v___x_5390_ = lean_apply_11(
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
                                    lean_box(0),
                                );
                                return v___x_5390_;
                            }
                            2 => {
                                lean_dec_ref(v_kna_5367_);
                                v_snd_5391_ = lean_ctor_get(v_a_5384_, 1);
                                v_isSharedCheck_5471_ = (!lean_is_exclusive(v_a_5384_)) as u8;
                                if v_isSharedCheck_5471_ == 0 {
                                    v_unused_5472_ = lean_ctor_get(v_a_5384_, 0);
                                    lean_dec(v_unused_5472_);
                                    v___x_5393_ = v_a_5384_;
                                    v_isShared_5394_ = v_isSharedCheck_5471_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_snd_5391_);
                                    lean_dec(v_a_5384_);
                                    v___x_5393_ = lean_box(0);
                                    v_isShared_5394_ = v_isSharedCheck_5471_;
                                    state = 1;
                                    continue;
                                }
                            }
                            _ => {
                                lean_dec(v_a_5384_);
                                lean_dec(v_a_5380_);
                                lean_dec_ref(v_kp_5368_);
                                lean_dec_ref(v_kna_5367_);
                                lean_dec_ref(v_goal_5366_);
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
                        lean_dec(v_a_5380_);
                        lean_dec_ref(v_kp_5368_);
                        lean_dec_ref(v_kna_5367_);
                        lean_dec_ref(v_goal_5366_);
                        lean_dec_ref(v_mkTac_5365_);
                        v_a_5474_ = lean_ctor_get(v___x_5383_, 0);
                        v_isSharedCheck_5481_ = (!lean_is_exclusive(v___x_5383_)) as u8;
                        if v_isSharedCheck_5481_ == 0 {
                            v___x_5476_ = v___x_5383_;
                            v_isShared_5477_ = v_isSharedCheck_5481_;
                            state = 17;
                            continue;
                        } else {
                            lean_inc(v_a_5474_);
                            lean_dec(v___x_5383_);
                            v___x_5476_ = lean_box(0);
                            v_isShared_5477_ = v_isSharedCheck_5481_;
                            state = 17;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_kp_5368_);
                    lean_dec_ref(v_kna_5367_);
                    lean_dec_ref(v_goal_5366_);
                    lean_dec_ref(v_mkTac_5365_);
                    lean_dec_ref(v_check_5364_);
                    v_a_5482_ = lean_ctor_get(v___x_5379_, 0);
                    v_isSharedCheck_5489_ = (!lean_is_exclusive(v___x_5379_)) as u8;
                    if v_isSharedCheck_5489_ == 0 {
                        v___x_5484_ = v___x_5379_;
                        v_isShared_5485_ = v_isSharedCheck_5489_;
                        state = 19;
                        continue;
                    } else {
                        lean_inc(v_a_5482_);
                        lean_dec(v___x_5379_);
                        v___x_5484_ = lean_box(0);
                        v_isShared_5485_ = v_isSharedCheck_5489_;
                        state = 19;
                        continue;
                    }
                }
            }
            1 => {
                v_mvarId_5395_ = lean_ctor_get(v_snd_5391_, 1);
                lean_inc(v_mvarId_5395_);
                v___f_5396_ = lean_alloc_closure(
                    l_Lean_Meta_Grind_Action_solverAction___lam__1___boxed
                        as *mut core::ffi::c_void,
                    11,
                    1,
                );
                lean_closure_set(v___f_5396_, 0, v_snd_5391_);
                v___x_5397_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg(v_mvarId_5395_, v___f_5396_, v_a_5369_, v_a_5370_, v_a_5371_, v_a_5372_, v_a_5373_, v_a_5374_, v_a_5375_, v_a_5376_, v_a_5377_);
                if lean_obj_tag(v___x_5397_) == 0 {
                    v_a_5398_ = lean_ctor_get(v___x_5397_, 0);
                    lean_inc(v_a_5398_);
                    lean_dec_ref_known(v___x_5397_, 1);
                    v_toGoalState_5399_ = lean_ctor_get(v_a_5398_, 0);
                    v_inconsistent_5400_ = lean_ctor_get_uint8(
                        v_toGoalState_5399_,
                        (core::mem::size_of::<*mut LeanObject>() * 17) as u32,
                    );
                    if v_inconsistent_5400_ == 0 {
                        v___x_5401_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_5370_);
                        if lean_obj_tag(v___x_5401_) == 0 {
                            v_a_5402_ = lean_ctor_get(v___x_5401_, 0);
                            lean_inc(v_a_5402_);
                            lean_dec_ref_known(v___x_5401_, 1);
                            v_trace_5403_ = lean_ctor_get_uint8(
                                v_a_5402_,
                                (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                            );
                            lean_dec(v_a_5402_);
                            if v_trace_5403_ == 0 {
                                lean_del_object(v___x_5393_);
                                lean_dec(v_a_5380_);
                                lean_dec_ref(v_goal_5366_);
                                lean_dec_ref(v_mkTac_5365_);
                                lean_inc(v_a_5377_);
                                lean_inc_ref(v_a_5376_);
                                lean_inc(v_a_5375_);
                                lean_inc_ref(v_a_5374_);
                                lean_inc(v_a_5373_);
                                lean_inc_ref(v_a_5372_);
                                lean_inc(v_a_5371_);
                                lean_inc_ref(v_a_5370_);
                                lean_inc(v_a_5369_);
                                v___x_5404_ = lean_apply_11(
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
                                    lean_box(0),
                                );
                                return v___x_5404_;
                            } else {
                                lean_inc(v_a_5377_);
                                lean_inc_ref(v_a_5376_);
                                lean_inc(v_a_5375_);
                                lean_inc_ref(v_a_5374_);
                                lean_inc(v_a_5373_);
                                lean_inc_ref(v_a_5372_);
                                lean_inc(v_a_5371_);
                                lean_inc_ref(v_a_5370_);
                                lean_inc(v_a_5369_);
                                v___x_5405_ = lean_apply_11(
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
                                    lean_box(0),
                                );
                                if lean_obj_tag(v___x_5405_) == 0 {
                                    v_a_5406_ = lean_ctor_get(v___x_5405_, 0);
                                    lean_inc(v_a_5406_);
                                    if lean_obj_tag(v_a_5406_) == 0 {
                                        lean_dec_ref_known(v___x_5405_, 1);
                                        v_seq_5407_ = lean_ctor_get(v_a_5406_, 0);
                                        lean_inc(v_seq_5407_);
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
                                        if lean_obj_tag(v___x_5408_) == 0 {
                                            v_a_5409_ = lean_ctor_get(v___x_5408_, 0);
                                            v_isSharedCheck_5445_ =
                                                (!lean_is_exclusive(v___x_5408_)) as u8;
                                            if v_isSharedCheck_5445_ == 0 {
                                                v___x_5411_ = v___x_5408_;
                                                v_isShared_5412_ = v_isSharedCheck_5445_;
                                                state = 2;
                                                continue;
                                            } else {
                                                lean_inc(v_a_5409_);
                                                lean_dec(v___x_5408_);
                                                v___x_5411_ = lean_box(0);
                                                v_isShared_5412_ = v_isSharedCheck_5445_;
                                                state = 2;
                                                continue;
                                            }
                                        } else {
                                            lean_dec_ref_known(v_a_5406_, 1);
                                            lean_del_object(v___x_5393_);
                                            lean_dec_ref(v_mkTac_5365_);
                                            v_a_5446_ = lean_ctor_get(v___x_5408_, 0);
                                            v_isSharedCheck_5453_ =
                                                (!lean_is_exclusive(v___x_5408_)) as u8;
                                            if v_isSharedCheck_5453_ == 0 {
                                                v___x_5448_ = v___x_5408_;
                                                v_isShared_5449_ = v_isSharedCheck_5453_;
                                                state = 11;
                                                continue;
                                            } else {
                                                lean_inc(v_a_5446_);
                                                lean_dec(v___x_5408_);
                                                v___x_5448_ = lean_box(0);
                                                v_isShared_5449_ = v_isSharedCheck_5453_;
                                                state = 11;
                                                continue;
                                            }
                                        }
                                    } else {
                                        lean_dec(v_a_5406_);
                                        lean_del_object(v___x_5393_);
                                        lean_dec(v_a_5380_);
                                        lean_dec_ref(v_goal_5366_);
                                        lean_dec_ref(v_mkTac_5365_);
                                        return v___x_5405_;
                                    }
                                } else {
                                    lean_del_object(v___x_5393_);
                                    lean_dec(v_a_5380_);
                                    lean_dec_ref(v_goal_5366_);
                                    lean_dec_ref(v_mkTac_5365_);
                                    return v___x_5405_;
                                }
                            }
                        } else {
                            lean_dec(v_a_5398_);
                            lean_del_object(v___x_5393_);
                            lean_dec(v_a_5380_);
                            lean_dec_ref(v_kp_5368_);
                            lean_dec_ref(v_goal_5366_);
                            lean_dec_ref(v_mkTac_5365_);
                            v_a_5454_ = lean_ctor_get(v___x_5401_, 0);
                            v_isSharedCheck_5461_ = (!lean_is_exclusive(v___x_5401_)) as u8;
                            if v_isSharedCheck_5461_ == 0 {
                                v___x_5456_ = v___x_5401_;
                                v_isShared_5457_ = v_isSharedCheck_5461_;
                                state = 13;
                                continue;
                            } else {
                                lean_inc(v_a_5454_);
                                lean_dec(v___x_5401_);
                                v___x_5456_ = lean_box(0);
                                v_isShared_5457_ = v_isSharedCheck_5461_;
                                state = 13;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_5398_);
                        lean_del_object(v___x_5393_);
                        lean_dec(v_a_5380_);
                        lean_dec_ref(v_kp_5368_);
                        lean_dec_ref(v_goal_5366_);
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
                    lean_del_object(v___x_5393_);
                    lean_dec(v_a_5380_);
                    lean_dec_ref(v_kp_5368_);
                    lean_dec_ref(v_goal_5366_);
                    lean_dec_ref(v_mkTac_5365_);
                    v_a_5463_ = lean_ctor_get(v___x_5397_, 0);
                    v_isSharedCheck_5470_ = (!lean_is_exclusive(v___x_5397_)) as u8;
                    if v_isSharedCheck_5470_ == 0 {
                        v___x_5465_ = v___x_5397_;
                        v_isShared_5466_ = v_isSharedCheck_5470_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_5463_);
                        lean_dec(v___x_5397_);
                        v___x_5465_ = lean_box(0);
                        v_isShared_5466_ = v_isSharedCheck_5470_;
                        state = 15;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5413_ = (lean_unbox(v_a_5409_) as u8);
                lean_dec(v_a_5409_);
                if v___x_5413_ == 0 {
                    lean_inc(v_seq_5407_);
                    lean_del_object(v___x_5411_);
                    v_isSharedCheck_5440_ = (!lean_is_exclusive(v_a_5406_)) as u8;
                    if v_isSharedCheck_5440_ == 0 {
                        v_unused_5441_ = lean_ctor_get(v_a_5406_, 0);
                        lean_dec(v_unused_5441_);
                        v___x_5415_ = v_a_5406_;
                        v_isShared_5416_ = v_isSharedCheck_5440_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v_a_5406_);
                        v___x_5415_ = lean_box(0);
                        v_isShared_5416_ = v_isSharedCheck_5440_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5393_);
                    lean_dec_ref(v_mkTac_5365_);
                    if v_isShared_5412_ == 0 {
                        lean_ctor_set(v___x_5411_, 0, v_a_5406_);
                        v___x_5443_ = v___x_5411_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_5444_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5444_, 0, v_a_5406_);
                        v___x_5443_ = v_reuseFailAlloc_5444_;
                        state = 10;
                        continue;
                    }
                }
            }
            3 => {
                lean_inc(v_a_5377_);
                lean_inc_ref(v_a_5376_);
                lean_inc(v_a_5375_);
                lean_inc_ref(v_a_5374_);
                lean_inc(v_a_5373_);
                lean_inc_ref(v_a_5372_);
                lean_inc(v_a_5371_);
                lean_inc_ref(v_a_5370_);
                lean_inc(v_a_5369_);
                v___x_5417_ = lean_apply_10(
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
                    lean_box(0),
                );
                if lean_obj_tag(v___x_5417_) == 0 {
                    v_a_5418_ = lean_ctor_get(v___x_5417_, 0);
                    v_isSharedCheck_5431_ = (!lean_is_exclusive(v___x_5417_)) as u8;
                    if v_isSharedCheck_5431_ == 0 {
                        v___x_5420_ = v___x_5417_;
                        v_isShared_5421_ = v_isSharedCheck_5431_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_5418_);
                        lean_dec(v___x_5417_);
                        v___x_5420_ = lean_box(0);
                        v_isShared_5421_ = v_isSharedCheck_5431_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5415_);
                    lean_dec(v_seq_5407_);
                    lean_del_object(v___x_5393_);
                    v_a_5432_ = lean_ctor_get(v___x_5417_, 0);
                    v_isSharedCheck_5439_ = (!lean_is_exclusive(v___x_5417_)) as u8;
                    if v_isSharedCheck_5439_ == 0 {
                        v___x_5434_ = v___x_5417_;
                        v_isShared_5435_ = v_isSharedCheck_5439_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_5432_);
                        lean_dec(v___x_5417_);
                        v___x_5434_ = lean_box(0);
                        v_isShared_5435_ = v_isSharedCheck_5439_;
                        state = 8;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_5394_ == 0 {
                    lean_ctor_set_tag(v___x_5393_, 1);
                    lean_ctor_set(v___x_5393_, 1, v_seq_5407_);
                    lean_ctor_set(v___x_5393_, 0, v_a_5418_);
                    v___x_5423_ = v___x_5393_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5430_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5430_, 0, v_a_5418_);
                    lean_ctor_set(v_reuseFailAlloc_5430_, 1, v_seq_5407_);
                    v___x_5423_ = v_reuseFailAlloc_5430_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_5416_ == 0 {
                    lean_ctor_set(v___x_5415_, 0, v___x_5423_);
                    v___x_5425_ = v___x_5415_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5429_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5429_, 0, v___x_5423_);
                    v___x_5425_ = v_reuseFailAlloc_5429_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_5421_ == 0 {
                    lean_ctor_set(v___x_5420_, 0, v___x_5425_);
                    v___x_5427_ = v___x_5420_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5428_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5428_, 0, v___x_5425_);
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
                    v_reuseFailAlloc_5438_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5438_, 0, v_a_5432_);
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
                    v_reuseFailAlloc_5452_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5452_, 0, v_a_5446_);
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
                    v_reuseFailAlloc_5460_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5460_, 0, v_a_5454_);
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
                    v_reuseFailAlloc_5469_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5469_, 0, v_a_5463_);
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
                    v_reuseFailAlloc_5480_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5480_, 0, v_a_5474_);
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
                    v_reuseFailAlloc_5488_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5488_, 0, v_a_5482_);
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
    mut v_check_5490_: *mut LeanObject,
    mut v_mkTac_5491_: *mut LeanObject,
    mut v_goal_5492_: *mut LeanObject,
    mut v_kna_5493_: *mut LeanObject,
    mut v_kp_5494_: *mut LeanObject,
    mut v_a_5495_: *mut LeanObject,
    mut v_a_5496_: *mut LeanObject,
    mut v_a_5497_: *mut LeanObject,
    mut v_a_5498_: *mut LeanObject,
    mut v_a_5499_: *mut LeanObject,
    mut v_a_5500_: *mut LeanObject,
    mut v_a_5501_: *mut LeanObject,
    mut v_a_5502_: *mut LeanObject,
    mut v_a_5503_: *mut LeanObject,
    mut v_a_5504_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5505_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_5503_);
    lean_dec_ref(v_a_5502_);
    lean_dec(v_a_5501_);
    lean_dec_ref(v_a_5500_);
    lean_dec(v_a_5499_);
    lean_dec_ref(v_a_5498_);
    lean_dec(v_a_5497_);
    lean_dec_ref(v_a_5496_);
    lean_dec(v_a_5495_);
    return v_res_5505_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_mbtc___lam__0(
    mut v_goal_5506_: *mut LeanObject,
    mut v___y_5507_: *mut LeanObject,
    mut v___y_5508_: *mut LeanObject,
    mut v___y_5509_: *mut LeanObject,
    mut v___y_5510_: *mut LeanObject,
    mut v___y_5511_: *mut LeanObject,
    mut v___y_5512_: *mut LeanObject,
    mut v___y_5513_: *mut LeanObject,
    mut v___y_5514_: *mut LeanObject,
    mut v___y_5515_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5522_: u8 = 0;
    let mut v___x_5523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5528_: u8 = 0;
    let mut v_a_5529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5532_: u8 = 0;
    let mut v___x_5534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5535_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_5518_) == 0 {
                    v_a_5519_ = lean_ctor_get(v___x_5518_, 0);
                    v_isSharedCheck_5528_ = (!lean_is_exclusive(v___x_5518_)) as u8;
                    if v_isSharedCheck_5528_ == 0 {
                        v___x_5521_ = v___x_5518_;
                        v_isShared_5522_ = v_isSharedCheck_5528_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5519_);
                        lean_dec(v___x_5518_);
                        v___x_5521_ = lean_box(0);
                        v_isShared_5522_ = v_isSharedCheck_5528_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_5517_);
                    v_a_5529_ = lean_ctor_get(v___x_5518_, 0);
                    v_isSharedCheck_5536_ = (!lean_is_exclusive(v___x_5518_)) as u8;
                    if v_isSharedCheck_5536_ == 0 {
                        v___x_5531_ = v___x_5518_;
                        v_isShared_5532_ = v_isSharedCheck_5536_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5529_);
                        lean_dec(v___x_5518_);
                        v___x_5531_ = lean_box(0);
                        v_isShared_5532_ = v_isSharedCheck_5536_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5523_ = lean_st_ref_get(v___x_5517_);
                lean_dec(v___x_5517_);
                v___x_5524_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5524_, 0, v_a_5519_);
                lean_ctor_set(v___x_5524_, 1, v___x_5523_);
                if v_isShared_5522_ == 0 {
                    lean_ctor_set(v___x_5521_, 0, v___x_5524_);
                    v___x_5526_ = v___x_5521_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5527_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5527_, 0, v___x_5524_);
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
                    v_reuseFailAlloc_5535_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5535_, 0, v_a_5529_);
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
    mut v_goal_5537_: *mut LeanObject,
    mut v___y_5538_: *mut LeanObject,
    mut v___y_5539_: *mut LeanObject,
    mut v___y_5540_: *mut LeanObject,
    mut v___y_5541_: *mut LeanObject,
    mut v___y_5542_: *mut LeanObject,
    mut v___y_5543_: *mut LeanObject,
    mut v___y_5544_: *mut LeanObject,
    mut v___y_5545_: *mut LeanObject,
    mut v___y_5546_: *mut LeanObject,
    mut v___y_5547_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5548_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_5546_);
    lean_dec_ref(v___y_5545_);
    lean_dec(v___y_5544_);
    lean_dec_ref(v___y_5543_);
    lean_dec(v___y_5542_);
    lean_dec_ref(v___y_5541_);
    lean_dec(v___y_5540_);
    lean_dec_ref(v___y_5539_);
    lean_dec(v___y_5538_);
    return v_res_5548_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_mbtc(
    mut v_goal_5556_: *mut LeanObject,
    mut v_kna_5557_: *mut LeanObject,
    mut v_kp_5558_: *mut LeanObject,
    mut v_a_5559_: *mut LeanObject,
    mut v_a_5560_: *mut LeanObject,
    mut v_a_5561_: *mut LeanObject,
    mut v_a_5562_: *mut LeanObject,
    mut v_a_5563_: *mut LeanObject,
    mut v_a_5564_: *mut LeanObject,
    mut v_a_5565_: *mut LeanObject,
    mut v_a_5566_: *mut LeanObject,
    mut v_a_5567_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarId_5571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5576_: u8 = 0;
    let mut v_snd_5577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5582_: u8 = 0;
    let mut v___x_5583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trace_5585_: u8 = 0;
    let mut v___x_5586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_seq_5589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5594_: u8 = 0;
    let mut v___x_5595_: u8 = 0;
    let mut v___x_5597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5598_: u8 = 0;
    let mut v_ref_5599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5600_: u8 = 0;
    let mut v___x_5601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5615_: u8 = 0;
    let mut v_unused_5616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5620_: u8 = 0;
    let mut v_a_5621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5624_: u8 = 0;
    let mut v___x_5626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5628_: u8 = 0;
    let mut v_a_5629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5632_: u8 = 0;
    let mut v___x_5634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5636_: u8 = 0;
    let mut v_isSharedCheck_5637_: u8 = 0;
    let mut v_unused_5638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5642_: u8 = 0;
    let mut v___x_5644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5646_: u8 = 0;
    let mut v_a_5647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5650_: u8 = 0;
    let mut v___x_5652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5654_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5569_ = l_Lean_Meta_Grind_Action_saveStateIfTracing___redArg(
                    v_a_5560_, v_a_5561_, v_a_5565_, v_a_5567_,
                );
                if lean_obj_tag(v___x_5569_) == 0 {
                    v_a_5570_ = lean_ctor_get(v___x_5569_, 0);
                    lean_inc(v_a_5570_);
                    lean_dec_ref_known(v___x_5569_, 1);
                    v_mvarId_5571_ = lean_ctor_get(v_goal_5556_, 1);
                    lean_inc_ref(v_goal_5556_);
                    v___f_5572_ = lean_alloc_closure(
                        l_Lean_Meta_Grind_Action_mbtc___lam__0___boxed as *mut core::ffi::c_void,
                        11,
                        1,
                    );
                    lean_closure_set(v___f_5572_, 0, v_goal_5556_);
                    lean_inc(v_mvarId_5571_);
                    v___x_5573_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg(v_mvarId_5571_, v___f_5572_, v_a_5559_, v_a_5560_, v_a_5561_, v_a_5562_, v_a_5563_, v_a_5564_, v_a_5565_, v_a_5566_, v_a_5567_);
                    if lean_obj_tag(v___x_5573_) == 0 {
                        v_a_5574_ = lean_ctor_get(v___x_5573_, 0);
                        lean_inc(v_a_5574_);
                        lean_dec_ref_known(v___x_5573_, 1);
                        v_fst_5575_ = lean_ctor_get(v_a_5574_, 0);
                        v___x_5576_ = (lean_unbox(v_fst_5575_) as u8);
                        if v___x_5576_ == 0 {
                            lean_dec(v_a_5570_);
                            lean_dec_ref(v_kp_5558_);
                            lean_dec_ref(v_goal_5556_);
                            v_snd_5577_ = lean_ctor_get(v_a_5574_, 1);
                            lean_inc(v_snd_5577_);
                            lean_dec(v_a_5574_);
                            lean_inc(v_a_5567_);
                            lean_inc_ref(v_a_5566_);
                            lean_inc(v_a_5565_);
                            lean_inc_ref(v_a_5564_);
                            lean_inc(v_a_5563_);
                            lean_inc_ref(v_a_5562_);
                            lean_inc(v_a_5561_);
                            lean_inc_ref(v_a_5560_);
                            lean_inc(v_a_5559_);
                            v___x_5578_ = lean_apply_11(
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
                                lean_box(0),
                            );
                            return v___x_5578_;
                        } else {
                            lean_dec_ref(v_kna_5557_);
                            v_snd_5579_ = lean_ctor_get(v_a_5574_, 1);
                            v_isSharedCheck_5637_ = (!lean_is_exclusive(v_a_5574_)) as u8;
                            if v_isSharedCheck_5637_ == 0 {
                                v_unused_5638_ = lean_ctor_get(v_a_5574_, 0);
                                lean_dec(v_unused_5638_);
                                v___x_5581_ = v_a_5574_;
                                v_isShared_5582_ = v_isSharedCheck_5637_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_snd_5579_);
                                lean_dec(v_a_5574_);
                                v___x_5581_ = lean_box(0);
                                v_isShared_5582_ = v_isSharedCheck_5637_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_5570_);
                        lean_dec_ref(v_kp_5558_);
                        lean_dec_ref(v_kna_5557_);
                        lean_dec_ref(v_goal_5556_);
                        v_a_5639_ = lean_ctor_get(v___x_5573_, 0);
                        v_isSharedCheck_5646_ = (!lean_is_exclusive(v___x_5573_)) as u8;
                        if v_isSharedCheck_5646_ == 0 {
                            v___x_5641_ = v___x_5573_;
                            v_isShared_5642_ = v_isSharedCheck_5646_;
                            state = 12;
                            continue;
                        } else {
                            lean_inc(v_a_5639_);
                            lean_dec(v___x_5573_);
                            v___x_5641_ = lean_box(0);
                            v_isShared_5642_ = v_isSharedCheck_5646_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_kp_5558_);
                    lean_dec_ref(v_kna_5557_);
                    lean_dec_ref(v_goal_5556_);
                    v_a_5647_ = lean_ctor_get(v___x_5569_, 0);
                    v_isSharedCheck_5654_ = (!lean_is_exclusive(v___x_5569_)) as u8;
                    if v_isSharedCheck_5654_ == 0 {
                        v___x_5649_ = v___x_5569_;
                        v_isShared_5650_ = v_isSharedCheck_5654_;
                        state = 14;
                        continue;
                    } else {
                        lean_inc(v_a_5647_);
                        lean_dec(v___x_5569_);
                        v___x_5649_ = lean_box(0);
                        v_isShared_5650_ = v_isSharedCheck_5654_;
                        state = 14;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5583_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_5560_);
                if lean_obj_tag(v___x_5583_) == 0 {
                    v_a_5584_ = lean_ctor_get(v___x_5583_, 0);
                    lean_inc(v_a_5584_);
                    lean_dec_ref_known(v___x_5583_, 1);
                    v_trace_5585_ = lean_ctor_get_uint8(
                        v_a_5584_,
                        (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                    );
                    lean_dec(v_a_5584_);
                    if v_trace_5585_ == 0 {
                        lean_del_object(v___x_5581_);
                        lean_dec(v_a_5570_);
                        lean_dec_ref(v_goal_5556_);
                        lean_inc(v_a_5567_);
                        lean_inc_ref(v_a_5566_);
                        lean_inc(v_a_5565_);
                        lean_inc_ref(v_a_5564_);
                        lean_inc(v_a_5563_);
                        lean_inc_ref(v_a_5562_);
                        lean_inc(v_a_5561_);
                        lean_inc_ref(v_a_5560_);
                        lean_inc(v_a_5559_);
                        v___x_5586_ = lean_apply_11(
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
                            lean_box(0),
                        );
                        return v___x_5586_;
                    } else {
                        lean_inc(v_a_5567_);
                        lean_inc_ref(v_a_5566_);
                        lean_inc(v_a_5565_);
                        lean_inc_ref(v_a_5564_);
                        lean_inc(v_a_5563_);
                        lean_inc_ref(v_a_5562_);
                        lean_inc(v_a_5561_);
                        lean_inc_ref(v_a_5560_);
                        lean_inc(v_a_5559_);
                        v___x_5587_ = lean_apply_11(
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
                            lean_box(0),
                        );
                        if lean_obj_tag(v___x_5587_) == 0 {
                            v_a_5588_ = lean_ctor_get(v___x_5587_, 0);
                            lean_inc(v_a_5588_);
                            if lean_obj_tag(v_a_5588_) == 0 {
                                lean_dec_ref_known(v___x_5587_, 1);
                                v_seq_5589_ = lean_ctor_get(v_a_5588_, 0);
                                lean_inc(v_seq_5589_);
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
                                if lean_obj_tag(v___x_5590_) == 0 {
                                    v_a_5591_ = lean_ctor_get(v___x_5590_, 0);
                                    v_isSharedCheck_5620_ = (!lean_is_exclusive(v___x_5590_)) as u8;
                                    if v_isSharedCheck_5620_ == 0 {
                                        v___x_5593_ = v___x_5590_;
                                        v_isShared_5594_ = v_isSharedCheck_5620_;
                                        state = 2;
                                        continue;
                                    } else {
                                        lean_inc(v_a_5591_);
                                        lean_dec(v___x_5590_);
                                        v___x_5593_ = lean_box(0);
                                        v_isShared_5594_ = v_isSharedCheck_5620_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    lean_dec_ref_known(v_a_5588_, 1);
                                    lean_del_object(v___x_5581_);
                                    v_a_5621_ = lean_ctor_get(v___x_5590_, 0);
                                    v_isSharedCheck_5628_ = (!lean_is_exclusive(v___x_5590_)) as u8;
                                    if v_isSharedCheck_5628_ == 0 {
                                        v___x_5623_ = v___x_5590_;
                                        v_isShared_5624_ = v_isSharedCheck_5628_;
                                        state = 8;
                                        continue;
                                    } else {
                                        lean_inc(v_a_5621_);
                                        lean_dec(v___x_5590_);
                                        v___x_5623_ = lean_box(0);
                                        v_isShared_5624_ = v_isSharedCheck_5628_;
                                        state = 8;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_a_5588_);
                                lean_del_object(v___x_5581_);
                                lean_dec(v_a_5570_);
                                lean_dec_ref(v_goal_5556_);
                                return v___x_5587_;
                            }
                        } else {
                            lean_del_object(v___x_5581_);
                            lean_dec(v_a_5570_);
                            lean_dec_ref(v_goal_5556_);
                            return v___x_5587_;
                        }
                    }
                } else {
                    lean_del_object(v___x_5581_);
                    lean_dec(v_snd_5579_);
                    lean_dec(v_a_5570_);
                    lean_dec_ref(v_kp_5558_);
                    lean_dec_ref(v_goal_5556_);
                    v_a_5629_ = lean_ctor_get(v___x_5583_, 0);
                    v_isSharedCheck_5636_ = (!lean_is_exclusive(v___x_5583_)) as u8;
                    if v_isSharedCheck_5636_ == 0 {
                        v___x_5631_ = v___x_5583_;
                        v_isShared_5632_ = v_isSharedCheck_5636_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_5629_);
                        lean_dec(v___x_5583_);
                        v___x_5631_ = lean_box(0);
                        v_isShared_5632_ = v_isSharedCheck_5636_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5595_ = (lean_unbox(v_a_5591_) as u8);
                if v___x_5595_ == 0 {
                    lean_inc(v_seq_5589_);
                    v_isSharedCheck_5615_ = (!lean_is_exclusive(v_a_5588_)) as u8;
                    if v_isSharedCheck_5615_ == 0 {
                        v_unused_5616_ = lean_ctor_get(v_a_5588_, 0);
                        lean_dec(v_unused_5616_);
                        v___x_5597_ = v_a_5588_;
                        v_isShared_5598_ = v_isSharedCheck_5615_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v_a_5588_);
                        v___x_5597_ = lean_box(0);
                        v_isShared_5598_ = v_isSharedCheck_5615_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_5591_);
                    lean_del_object(v___x_5581_);
                    if v_isShared_5594_ == 0 {
                        lean_ctor_set(v___x_5593_, 0, v_a_5588_);
                        v___x_5618_ = v___x_5593_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_5619_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5619_, 0, v_a_5588_);
                        v___x_5618_ = v_reuseFailAlloc_5619_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                v_ref_5599_ = lean_ctor_get(v_a_5566_, 5);
                v___x_5600_ = (lean_unbox(v_a_5591_) as u8);
                lean_dec(v_a_5591_);
                v___x_5601_ = l_Lean_SourceInfo_fromRef(v_ref_5599_, v___x_5600_);
                v___x_5602_ = l_Lean_Meta_Grind_Action_mbtc___closed__0;
                v___x_5603_ = l_Lean_Meta_Grind_Action_mbtc___closed__1;
                lean_inc(v___x_5601_);
                if v_isShared_5582_ == 0 {
                    lean_ctor_set_tag(v___x_5581_, 2);
                    lean_ctor_set(v___x_5581_, 1, v___x_5602_);
                    lean_ctor_set(v___x_5581_, 0, v___x_5601_);
                    v___x_5605_ = v___x_5581_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5614_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5614_, 0, v___x_5601_);
                    lean_ctor_set(v_reuseFailAlloc_5614_, 1, v___x_5602_);
                    v___x_5605_ = v_reuseFailAlloc_5614_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5606_ = l_Lean_Syntax_node1(v___x_5601_, v___x_5603_, v___x_5605_);
                v___x_5607_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_5607_, 0, v___x_5606_);
                lean_ctor_set(v___x_5607_, 1, v_seq_5589_);
                if v_isShared_5598_ == 0 {
                    lean_ctor_set(v___x_5597_, 0, v___x_5607_);
                    v___x_5609_ = v___x_5597_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5613_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5613_, 0, v___x_5607_);
                    v___x_5609_ = v_reuseFailAlloc_5613_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_5594_ == 0 {
                    lean_ctor_set(v___x_5593_, 0, v___x_5609_);
                    v___x_5611_ = v___x_5593_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5612_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5612_, 0, v___x_5609_);
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
                    v_reuseFailAlloc_5627_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5627_, 0, v_a_5621_);
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
                    v_reuseFailAlloc_5635_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5635_, 0, v_a_5629_);
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
                    v_reuseFailAlloc_5645_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5645_, 0, v_a_5639_);
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
                    v_reuseFailAlloc_5653_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5653_, 0, v_a_5647_);
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
    mut v_goal_5655_: *mut LeanObject,
    mut v_kna_5656_: *mut LeanObject,
    mut v_kp_5657_: *mut LeanObject,
    mut v_a_5658_: *mut LeanObject,
    mut v_a_5659_: *mut LeanObject,
    mut v_a_5660_: *mut LeanObject,
    mut v_a_5661_: *mut LeanObject,
    mut v_a_5662_: *mut LeanObject,
    mut v_a_5663_: *mut LeanObject,
    mut v_a_5664_: *mut LeanObject,
    mut v_a_5665_: *mut LeanObject,
    mut v_a_5666_: *mut LeanObject,
    mut v_a_5667_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5668_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_5666_);
    lean_dec_ref(v_a_5665_);
    lean_dec(v_a_5664_);
    lean_dec_ref(v_a_5663_);
    lean_dec(v_a_5662_);
    lean_dec_ref(v_a_5661_);
    lean_dec(v_a_5660_);
    lean_dec_ref(v_a_5659_);
    lean_dec(v_a_5658_);
    return v_res_5668_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_loop_match__1_splitter___redArg(
    mut v_n_5669_: *mut LeanObject,
    mut v_h__1_5670_: *mut LeanObject,
    mut v_h__2_5671_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_5672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_5673_: u8 = 0;
    v_zero_5672_ = lean_unsigned_to_nat(0);
    v_isZero_5673_ = lean_nat_dec_eq(v_n_5669_, v_zero_5672_);
    if v_isZero_5673_ == 1 {
        let mut v___x_5674_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5675_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_5671_);
        v___x_5674_ = lean_box(0);
        v___x_5675_ = lean_apply_1(v_h__1_5670_, v___x_5674_);
        return v___x_5675_;
    } else {
        let mut v_one_5676_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_5677_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5678_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_5670_);
        v_one_5676_ = lean_unsigned_to_nat(1);
        v_n_5677_ = lean_nat_sub(v_n_5669_, v_one_5676_);
        v___x_5678_ = lean_apply_1(v_h__2_5671_, v_n_5677_);
        return v___x_5678_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_loop_match__1_splitter___redArg___boxed(
    mut v_n_5679_: *mut LeanObject,
    mut v_h__1_5680_: *mut LeanObject,
    mut v_h__2_5681_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5682_: *mut LeanObject = core::ptr::null_mut();
    v_res_5682_ = l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_loop_match__1_splitter___redArg(v_n_5679_, v_h__1_5680_, v_h__2_5681_);
    lean_dec(v_n_5679_);
    return v_res_5682_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_loop_match__1_splitter(
    mut v_motive_5683_: *mut LeanObject,
    mut v_n_5684_: *mut LeanObject,
    mut v_h__1_5685_: *mut LeanObject,
    mut v_h__2_5686_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_5687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_5688_: u8 = 0;
    v_zero_5687_ = lean_unsigned_to_nat(0);
    v_isZero_5688_ = lean_nat_dec_eq(v_n_5684_, v_zero_5687_);
    if v_isZero_5688_ == 1 {
        let mut v___x_5689_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5690_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_5686_);
        v___x_5689_ = lean_box(0);
        v___x_5690_ = lean_apply_1(v_h__1_5685_, v___x_5689_);
        return v___x_5690_;
    } else {
        let mut v_one_5691_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_5692_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5693_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_5685_);
        v_one_5691_ = lean_unsigned_to_nat(1);
        v_n_5692_ = lean_nat_sub(v_n_5684_, v_one_5691_);
        v___x_5693_ = lean_apply_1(v_h__2_5686_, v_n_5692_);
        return v___x_5693_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_loop_match__1_splitter___boxed(
    mut v_motive_5694_: *mut LeanObject,
    mut v_n_5695_: *mut LeanObject,
    mut v_h__1_5696_: *mut LeanObject,
    mut v_h__2_5697_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5698_: *mut LeanObject = core::ptr::null_mut();
    v_res_5698_ =
        l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_loop_match__1_splitter(
            v_motive_5694_,
            v_n_5695_,
            v_h__1_5696_,
            v_h__2_5697_,
        );
    lean_dec(v_n_5695_);
    return v_res_5698_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Action(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Action(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Action(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Action(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Action(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Action(builtin);
}
