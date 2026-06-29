// Lean compiler output
// Module: Lean.Elab.ConfigEval.MetaInstances
// Imports: Lean.Elab.ConfigEval.Commands Lean.Elab.ConfigEval.Instances Lean.Elab.ConfigEval.DeriveEvalTerm Lean.Elab.ConfigEval.DeriveEvalExpr
use crate::r#gen::Init::Prelude::l_Lean_Name_mkStr4;
use crate::r#gen::Lean::Elab::ConfigEval::Commands::{
    initialize_Lean_Elab_ConfigEval_Commands, runtime_initialize_Lean_Elab_ConfigEval_Commands,
};
use crate::r#gen::Lean::Elab::ConfigEval::DeriveEvalExpr::{
    initialize_Lean_Elab_ConfigEval_DeriveEvalExpr,
    l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg,
    runtime_initialize_Lean_Elab_ConfigEval_DeriveEvalExpr,
};
use crate::r#gen::Lean::Elab::ConfigEval::DeriveEvalTerm::{
    initialize_Lean_Elab_ConfigEval_DeriveEvalTerm,
    l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments,
    l_Lean_Elab_ConfigEval_EvalTerm_withSimpleEvalStx___redArg,
    runtime_initialize_Lean_Elab_ConfigEval_DeriveEvalTerm,
};
use crate::r#gen::Lean::Elab::ConfigEval::Instances::{
    initialize_Lean_Elab_ConfigEval_Instances, l_Lean_Elab_ConfigEval_EvalExpr_instList___redArg,
    l_Lean_Elab_ConfigEval_EvalExpr_instNat, l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg,
    l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___boxed,
    runtime_initialize_Lean_Elab_ConfigEval_Instances,
};
use crate::r#gen::Lean::Elab::ConfigEval::Types::l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_const___override, l_Lean_instInhabitedExpr,
    l_Lean_mkConst,
};
use crate::r#gen::Lean::Message::l_Lean_stringToMessageData;
use crate::ffi::{
    lean_array_get_borrowed, lean_array_get_size, lean_nat_dec_eq, lean_string_dec_eq,
};
use crate::ffi::lean_st_ref_get;
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [97, 108, 108, 0],
};
static mut l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__1_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
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
        110, 111, 110, 68, 101, 112, 101, 110, 100, 101, 110, 116, 70, 105, 114, 115, 116, 0,
    ],
};
static mut l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__2_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        110, 111, 110, 68, 101, 112, 101, 110, 100, 101, 110, 116, 79, 110, 108, 121, 0,
    ],
};
static mut l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__0_value:
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
static mut l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__1_value:
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
    m_data: [77, 101, 116, 97, 0],
};
static mut l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__2_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        65, 112, 112, 108, 121, 78, 101, 119, 71, 111, 97, 108, 115, 0,
    ],
};
static mut l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__3_value:
    crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 12,
    m_num_fixed: 3,
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__2_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__3_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__4_value_aux_0:
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__4_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__4_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        15449383196166861506 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__4_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__4_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        1913141712249469064 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__0_value:
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
    m_fun: l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___boxed
        as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__0_value:
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
    m_data: [102, 97, 105, 108, 101, 100, 0],
};
static mut l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___closed__0_value:
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
    m_fun: l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals___closed__0_value:
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
    m_fun: l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___boxed
        as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___lam__0___closed__0_value:
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
    m_data: [110, 111, 110, 101, 0],
};
static mut l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___lam__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___lam__0___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___lam__0___closed__1_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [110, 111, 116, 67, 108, 97, 115, 115, 101, 115, 0],
};
static mut l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___lam__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___lam__0___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___closed__0_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        69, 116, 97, 83, 116, 114, 117, 99, 116, 77, 111, 100, 101, 0,
    ],
};
static mut l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___closed__1_value:
    crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 12,
    m_num_fixed: 3,
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___closed__0_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___closed__1_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___closed__2_value_aux_0:
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___closed__2_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___closed__2_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        15449383196166861506 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___closed__2_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___closed__2_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        10917271421258176470 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__0_value:
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
    m_fun: l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___boxed
        as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode_evalExpr___closed__0_value:
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
    m_fun: l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode_evalExpr___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode_evalExpr___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode_evalExpr___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode___closed__0_value:
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
    m_fun: l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode_evalExpr___boxed
        as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__0_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [100, 101, 102, 97, 117, 108, 116, 0]};
static mut l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__1_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [105, 110, 115, 116, 97, 110, 99, 101, 115, 0]};
static mut l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__2_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [114, 101, 100, 117, 99, 105, 98, 108, 101, 0]};
static mut l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___closed__0_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        84, 114, 97, 110, 115, 112, 97, 114, 101, 110, 99, 121, 77, 111, 100, 101, 0,
    ],
};
static mut l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___closed__1_value:
    crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 12,
    m_num_fixed: 3,
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___closed__0_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___closed__1_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___closed__2_value_aux_0:
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___closed__2_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___closed__2_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        15449383196166861506 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___closed__2_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___closed__2_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        7920553410559161077 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__0_value:
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
    m_fun: l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___boxed
        as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr___closed__0_value:
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
    m_fun: l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__0_value:
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
    m_fun: l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr___boxed
        as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [110, 101, 103, 0],
};
static mut l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__1_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [112, 111, 115, 0],
};
static mut l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__2_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [78, 97, 116, 0],
};
static mut l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__3_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        11442535297760353691 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__3_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__5_value:
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
    m_fun: l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___boxed as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___closed__0_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [79, 99, 99, 117, 114, 114, 101, 110, 99, 101, 115, 0],
};
static mut l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___closed__1_value:
    crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 12,
    m_num_fixed: 3,
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___closed__0_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___closed__2_value_aux_0:
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___closed__2_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___closed__2_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        15449383196166861506 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___closed__2_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___closed__2_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        10189614426786410228 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__0_value:
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
    m_fun: l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___boxed
        as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Elab_ConfigEval_instEvalTermOccurrences: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___lam__0___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___lam__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___closed__0_value:
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
    m_fun: l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__0_value:
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
    m_fun: l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___boxed
        as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Elab_ConfigEval_instEvalExprOccurrences: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1259_ = crate::leanh::lean_box(0);
    v___x_1260_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_1261_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1261_, 0, v___x_1260_);
    crate::leanh::lean_ctor_set(v___x_1261_, 1, v___x_1259_);
    return v___x_1261_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1263_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___redArg___closed__0);
    v___x_1264_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1264_, 0, v___x_1263_);
    return v___x_1264_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___redArg___boxed(
    mut v___y_1265_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1266_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___redArg();
    return v_res_1266_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0(
    mut v_00_u03b1_1267_: *mut crate::leanh::LeanObject,
    mut v___y_1268_: *mut crate::leanh::LeanObject,
    mut v___y_1269_: *mut crate::leanh::LeanObject,
    mut v___y_1270_: *mut crate::leanh::LeanObject,
    mut v___y_1271_: *mut crate::leanh::LeanObject,
    mut v___y_1272_: *mut crate::leanh::LeanObject,
    mut v___y_1273_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1275_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___redArg();
    return v___x_1275_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___boxed(
    mut v_00_u03b1_1276_: *mut crate::leanh::LeanObject,
    mut v___y_1277_: *mut crate::leanh::LeanObject,
    mut v___y_1278_: *mut crate::leanh::LeanObject,
    mut v___y_1279_: *mut crate::leanh::LeanObject,
    mut v___y_1280_: *mut crate::leanh::LeanObject,
    mut v___y_1281_: *mut crate::leanh::LeanObject,
    mut v___y_1282_: *mut crate::leanh::LeanObject,
    mut v___y_1283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1284_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0(v_00_u03b1_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_);
    crate::leanh::lean_dec(v___y_1282_);
    crate::leanh::lean_dec_ref(v___y_1281_);
    crate::leanh::lean_dec(v___y_1280_);
    crate::leanh::lean_dec_ref(v___y_1279_);
    crate::leanh::lean_dec(v___y_1278_);
    crate::leanh::lean_dec_ref(v___y_1277_);
    return v_res_1284_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0(
    mut v___x_1288_: *mut crate::leanh::LeanObject,
    mut v___x_1289_: *mut crate::leanh::LeanObject,
    mut v___x_1290_: *mut crate::leanh::LeanObject,
    mut v_ctor_1291_: *mut crate::leanh::LeanObject,
    mut v_args_1292_: *mut crate::leanh::LeanObject,
    mut v___y_1293_: *mut crate::leanh::LeanObject,
    mut v___y_1294_: *mut crate::leanh::LeanObject,
    mut v___y_1295_: *mut crate::leanh::LeanObject,
    mut v___y_1296_: *mut crate::leanh::LeanObject,
    mut v___y_1297_: *mut crate::leanh::LeanObject,
    mut v___y_1298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: u8 = 0;
    let mut v___x_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: u8 = 0;
    let mut v___x_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: u8 = 0;
    let mut v___x_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1312_: u8 = 0;
    let mut v___x_1313_: u8 = 0;
    let mut v___x_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1321_: u8 = 0;
    let mut v_unused_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1326_: u8 = 0;
    let mut v___x_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1330_: u8 = 0;
    let mut v___x_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1336_: u8 = 0;
    let mut v___x_1337_: u8 = 0;
    let mut v___x_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1345_: u8 = 0;
    let mut v_unused_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1350_: u8 = 0;
    let mut v___x_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1354_: u8 = 0;
    let mut v___x_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1360_: u8 = 0;
    let mut v___x_1361_: u8 = 0;
    let mut v___x_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1369_: u8 = 0;
    let mut v_unused_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1374_: u8 = 0;
    let mut v___x_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1378_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1300_ =
                    l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__0;
                v___x_1301_ = lean_string_dec_eq(v_ctor_1291_, v___x_1300_);
                if v___x_1301_ == 0 {
                    v___x_1302_ = l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__1;
                    v___x_1303_ = lean_string_dec_eq(v_ctor_1291_, v___x_1302_);
                    if v___x_1303_ == 0 {
                        v___x_1304_ = l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__2;
                        v___x_1305_ = lean_string_dec_eq(v_ctor_1291_, v___x_1304_);
                        if v___x_1305_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_1290_);
                            crate::leanh::lean_dec_ref(v___x_1289_);
                            crate::leanh::lean_dec_ref(v___x_1288_);
                            v___x_1306_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___redArg();
                            return v___x_1306_;
                        } else {
                            v___x_1307_ = l_Lean_Name_mkStr4(
                                v___x_1288_,
                                v___x_1289_,
                                v___x_1290_,
                                v___x_1304_,
                            );
                            v___x_1308_ = crate::leanh::lean_unsigned_to_nat(0);
                            crate::leanh::lean_inc(v___x_1307_);
                            v___x_1309_ =
                                l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(
                                    v___x_1307_,
                                    v___x_1308_,
                                    v_args_1292_,
                                    v___y_1293_,
                                    v___y_1294_,
                                    v___y_1295_,
                                    v___y_1296_,
                                    v___y_1297_,
                                    v___y_1298_,
                                );
                            if crate::leanh::lean_obj_tag(v___x_1309_) == 0 {
                                v_isSharedCheck_1321_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1309_)) as u8;
                                if v_isSharedCheck_1321_ == 0 {
                                    v_unused_1322_ = crate::leanh::lean_ctor_get(v___x_1309_, 0);
                                    crate::leanh::lean_dec(v_unused_1322_);
                                    v___x_1311_ = v___x_1309_;
                                    v_isShared_1312_ = v_isSharedCheck_1321_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v___x_1309_);
                                    v___x_1311_ = crate::leanh::lean_box(0);
                                    v_isShared_1312_ = v_isSharedCheck_1321_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v___x_1307_);
                                v_a_1323_ = crate::leanh::lean_ctor_get(v___x_1309_, 0);
                                v_isSharedCheck_1330_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1309_)) as u8;
                                if v_isSharedCheck_1330_ == 0 {
                                    v___x_1325_ = v___x_1309_;
                                    v_isShared_1326_ = v_isSharedCheck_1330_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1323_);
                                    crate::leanh::lean_dec(v___x_1309_);
                                    v___x_1325_ = crate::leanh::lean_box(0);
                                    v_isShared_1326_ = v_isSharedCheck_1330_;
                                    state = 3;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v___x_1331_ =
                            l_Lean_Name_mkStr4(v___x_1288_, v___x_1289_, v___x_1290_, v___x_1302_);
                        v___x_1332_ = crate::leanh::lean_unsigned_to_nat(0);
                        crate::leanh::lean_inc(v___x_1331_);
                        v___x_1333_ =
                            l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(
                                v___x_1331_,
                                v___x_1332_,
                                v_args_1292_,
                                v___y_1293_,
                                v___y_1294_,
                                v___y_1295_,
                                v___y_1296_,
                                v___y_1297_,
                                v___y_1298_,
                            );
                        if crate::leanh::lean_obj_tag(v___x_1333_) == 0 {
                            v_isSharedCheck_1345_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1333_)) as u8;
                            if v_isSharedCheck_1345_ == 0 {
                                v_unused_1346_ = crate::leanh::lean_ctor_get(v___x_1333_, 0);
                                crate::leanh::lean_dec(v_unused_1346_);
                                v___x_1335_ = v___x_1333_;
                                v_isShared_1336_ = v_isSharedCheck_1345_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_1333_);
                                v___x_1335_ = crate::leanh::lean_box(0);
                                v_isShared_1336_ = v_isSharedCheck_1345_;
                                state = 5;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_1331_);
                            v_a_1347_ = crate::leanh::lean_ctor_get(v___x_1333_, 0);
                            v_isSharedCheck_1354_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1333_)) as u8;
                            if v_isSharedCheck_1354_ == 0 {
                                v___x_1349_ = v___x_1333_;
                                v_isShared_1350_ = v_isSharedCheck_1354_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1347_);
                                crate::leanh::lean_dec(v___x_1333_);
                                v___x_1349_ = crate::leanh::lean_box(0);
                                v_isShared_1350_ = v_isSharedCheck_1354_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                } else {
                    v___x_1355_ =
                        l_Lean_Name_mkStr4(v___x_1288_, v___x_1289_, v___x_1290_, v___x_1300_);
                    v___x_1356_ = crate::leanh::lean_unsigned_to_nat(0);
                    crate::leanh::lean_inc(v___x_1355_);
                    v___x_1357_ = l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(
                        v___x_1355_,
                        v___x_1356_,
                        v_args_1292_,
                        v___y_1293_,
                        v___y_1294_,
                        v___y_1295_,
                        v___y_1296_,
                        v___y_1297_,
                        v___y_1298_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1357_) == 0 {
                        v_isSharedCheck_1369_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1357_)) as u8;
                        if v_isSharedCheck_1369_ == 0 {
                            v_unused_1370_ = crate::leanh::lean_ctor_get(v___x_1357_, 0);
                            crate::leanh::lean_dec(v_unused_1370_);
                            v___x_1359_ = v___x_1357_;
                            v_isShared_1360_ = v_isSharedCheck_1369_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_1357_);
                            v___x_1359_ = crate::leanh::lean_box(0);
                            v_isShared_1360_ = v_isSharedCheck_1369_;
                            state = 9;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_1355_);
                        v_a_1371_ = crate::leanh::lean_ctor_get(v___x_1357_, 0);
                        v_isSharedCheck_1378_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1357_)) as u8;
                        if v_isSharedCheck_1378_ == 0 {
                            v___x_1373_ = v___x_1357_;
                            v_isShared_1374_ = v_isSharedCheck_1378_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1371_);
                            crate::leanh::lean_dec(v___x_1357_);
                            v___x_1373_ = crate::leanh::lean_box(0);
                            v_isShared_1374_ = v_isSharedCheck_1378_;
                            state = 11;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1313_ = 1;
                v___x_1314_ = crate::leanh::lean_box(0);
                v___x_1315_ = l_Lean_Expr_const___override(v___x_1307_, v___x_1314_);
                v___x_1316_ = crate::leanh::lean_box((v___x_1313_) as usize);
                v___x_1317_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1317_, 0, v___x_1316_);
                crate::leanh::lean_ctor_set(v___x_1317_, 1, v___x_1315_);
                if v_isShared_1312_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1311_, 0, v___x_1317_);
                    v___x_1319_ = v___x_1311_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1320_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1320_, 0, v___x_1317_);
                    v___x_1319_ = v_reuseFailAlloc_1320_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1319_;
            }
            3 => {
                if v_isShared_1326_ == 0 {
                    v___x_1328_ = v___x_1325_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1329_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1329_, 0, v_a_1323_);
                    v___x_1328_ = v_reuseFailAlloc_1329_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1328_;
            }
            5 => {
                v___x_1337_ = 0;
                v___x_1338_ = crate::leanh::lean_box(0);
                v___x_1339_ = l_Lean_Expr_const___override(v___x_1331_, v___x_1338_);
                v___x_1340_ = crate::leanh::lean_box((v___x_1337_) as usize);
                v___x_1341_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1341_, 0, v___x_1340_);
                crate::leanh::lean_ctor_set(v___x_1341_, 1, v___x_1339_);
                if v_isShared_1336_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1335_, 0, v___x_1341_);
                    v___x_1343_ = v___x_1335_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1344_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1344_, 0, v___x_1341_);
                    v___x_1343_ = v_reuseFailAlloc_1344_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1343_;
            }
            7 => {
                if v_isShared_1350_ == 0 {
                    v___x_1352_ = v___x_1349_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1353_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1353_, 0, v_a_1347_);
                    v___x_1352_ = v_reuseFailAlloc_1353_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1352_;
            }
            9 => {
                v___x_1361_ = 2;
                v___x_1362_ = crate::leanh::lean_box(0);
                v___x_1363_ = l_Lean_Expr_const___override(v___x_1355_, v___x_1362_);
                v___x_1364_ = crate::leanh::lean_box((v___x_1361_) as usize);
                v___x_1365_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1365_, 0, v___x_1364_);
                crate::leanh::lean_ctor_set(v___x_1365_, 1, v___x_1363_);
                if v_isShared_1360_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1359_, 0, v___x_1365_);
                    v___x_1367_ = v___x_1359_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1368_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1368_, 0, v___x_1365_);
                    v___x_1367_ = v_reuseFailAlloc_1368_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1367_;
            }
            11 => {
                if v_isShared_1374_ == 0 {
                    v___x_1376_ = v___x_1373_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1377_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_a_1371_);
                    v___x_1376_ = v_reuseFailAlloc_1377_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1376_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___boxed(
    mut v___x_1379_: *mut crate::leanh::LeanObject,
    mut v___x_1380_: *mut crate::leanh::LeanObject,
    mut v___x_1381_: *mut crate::leanh::LeanObject,
    mut v_ctor_1382_: *mut crate::leanh::LeanObject,
    mut v_args_1383_: *mut crate::leanh::LeanObject,
    mut v___y_1384_: *mut crate::leanh::LeanObject,
    mut v___y_1385_: *mut crate::leanh::LeanObject,
    mut v___y_1386_: *mut crate::leanh::LeanObject,
    mut v___y_1387_: *mut crate::leanh::LeanObject,
    mut v___y_1388_: *mut crate::leanh::LeanObject,
    mut v___y_1389_: *mut crate::leanh::LeanObject,
    mut v___y_1390_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1391_ = l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0(
        v___x_1379_,
        v___x_1380_,
        v___x_1381_,
        v_ctor_1382_,
        v_args_1383_,
        v___y_1384_,
        v___y_1385_,
        v___y_1386_,
        v___y_1387_,
        v___y_1388_,
        v___y_1389_,
    );
    crate::leanh::lean_dec(v___y_1389_);
    crate::leanh::lean_dec_ref(v___y_1388_);
    crate::leanh::lean_dec(v___y_1387_);
    crate::leanh::lean_dec_ref(v___y_1386_);
    crate::leanh::lean_dec(v___y_1385_);
    crate::leanh::lean_dec_ref(v___y_1384_);
    crate::leanh::lean_dec_ref(v_args_1383_);
    crate::leanh::lean_dec_ref(v_ctor_1382_);
    return v_res_1391_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm(
    mut v_a_1403_: *mut crate::leanh::LeanObject,
    mut v_a_1404_: *mut crate::leanh::LeanObject,
    mut v_a_1405_: *mut crate::leanh::LeanObject,
    mut v_a_1406_: *mut crate::leanh::LeanObject,
    mut v_a_1407_: *mut crate::leanh::LeanObject,
    mut v_a_1408_: *mut crate::leanh::LeanObject,
    mut v_a_1409_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1411_ = l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__3;
    v___x_1412_ = l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__4;
    v___x_1413_ = l_Lean_Elab_ConfigEval_EvalTerm_withSimpleEvalStx___redArg(
        v___x_1412_,
        v___f_1411_,
        v_a_1403_,
        v_a_1404_,
        v_a_1405_,
        v_a_1406_,
        v_a_1407_,
        v_a_1408_,
        v_a_1409_,
    );
    return v___x_1413_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___boxed(
    mut v_a_1414_: *mut crate::leanh::LeanObject,
    mut v_a_1415_: *mut crate::leanh::LeanObject,
    mut v_a_1416_: *mut crate::leanh::LeanObject,
    mut v_a_1417_: *mut crate::leanh::LeanObject,
    mut v_a_1418_: *mut crate::leanh::LeanObject,
    mut v_a_1419_: *mut crate::leanh::LeanObject,
    mut v_a_1420_: *mut crate::leanh::LeanObject,
    mut v_a_1421_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1422_ = l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm(
        v_a_1414_, v_a_1415_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_,
    );
    crate::leanh::lean_dec(v_a_1420_);
    crate::leanh::lean_dec_ref(v_a_1419_);
    crate::leanh::lean_dec(v_a_1418_);
    crate::leanh::lean_dec_ref(v_a_1417_);
    crate::leanh::lean_dec(v_a_1416_);
    crate::leanh::lean_dec_ref(v_a_1415_);
    return v_res_1422_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1424_ = crate::leanh::lean_box(0);
    v___x_1425_ = l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__4;
    v___x_1426_ = l_Lean_Expr_const___override(v___x_1425_, v___x_1424_);
    return v___x_1426_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1427_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__1_once),
        _init_l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__1,
    );
    v___x_1428_ = l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__0;
    v___x_1429_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1429_, 0, v___x_1428_);
    crate::leanh::lean_ctor_set(v___x_1429_, 1, v___x_1427_);
    return v___x_1429_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1430_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__2_once),
        _init_l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__2,
    );
    return v___x_1430_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1431_ = crate::leanh::lean_box(0);
    v___x_1432_ = l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
    v___x_1433_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1433_, 0, v___x_1432_);
    crate::leanh::lean_ctor_set(v___x_1433_, 1, v___x_1431_);
    return v___x_1433_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1435_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___redArg___closed__0);
    v___x_1436_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1436_, 0, v___x_1435_);
    return v___x_1436_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___redArg___boxed(
    mut v___y_1437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1438_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___redArg();
    return v_res_1438_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0(
    mut v_00_u03b1_1439_: *mut crate::leanh::LeanObject,
    mut v___y_1440_: *mut crate::leanh::LeanObject,
    mut v___y_1441_: *mut crate::leanh::LeanObject,
    mut v___y_1442_: *mut crate::leanh::LeanObject,
    mut v___y_1443_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1445_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___redArg();
    return v___x_1445_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___boxed(
    mut v_00_u03b1_1446_: *mut crate::leanh::LeanObject,
    mut v___y_1447_: *mut crate::leanh::LeanObject,
    mut v___y_1448_: *mut crate::leanh::LeanObject,
    mut v___y_1449_: *mut crate::leanh::LeanObject,
    mut v___y_1450_: *mut crate::leanh::LeanObject,
    mut v___y_1451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1452_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0(v_00_u03b1_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
    crate::leanh::lean_dec(v___y_1450_);
    crate::leanh::lean_dec_ref(v___y_1449_);
    crate::leanh::lean_dec(v___y_1448_);
    crate::leanh::lean_dec_ref(v___y_1447_);
    return v_res_1452_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1_spec__1(
    mut v_msgData_1453_: *mut crate::leanh::LeanObject,
    mut v___y_1454_: *mut crate::leanh::LeanObject,
    mut v___y_1455_: *mut crate::leanh::LeanObject,
    mut v___y_1456_: *mut crate::leanh::LeanObject,
    mut v___y_1457_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1459_ = lean_st_ref_get(v___y_1457_);
    v_env_1460_ = crate::leanh::lean_ctor_get(v___x_1459_, 0);
    crate::leanh::lean_inc_ref(v_env_1460_);
    crate::leanh::lean_dec(v___x_1459_);
    v___x_1461_ = lean_st_ref_get(v___y_1455_);
    v_mctx_1462_ = crate::leanh::lean_ctor_get(v___x_1461_, 0);
    crate::leanh::lean_inc_ref(v_mctx_1462_);
    crate::leanh::lean_dec(v___x_1461_);
    v_lctx_1463_ = crate::leanh::lean_ctor_get(v___y_1454_, 2);
    v_options_1464_ = crate::leanh::lean_ctor_get(v___y_1456_, 2);
    crate::leanh::lean_inc_ref(v_options_1464_);
    crate::leanh::lean_inc_ref(v_lctx_1463_);
    v___x_1465_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1465_, 0, v_env_1460_);
    crate::leanh::lean_ctor_set(v___x_1465_, 1, v_mctx_1462_);
    crate::leanh::lean_ctor_set(v___x_1465_, 2, v_lctx_1463_);
    crate::leanh::lean_ctor_set(v___x_1465_, 3, v_options_1464_);
    v___x_1466_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1466_, 0, v___x_1465_);
    crate::leanh::lean_ctor_set(v___x_1466_, 1, v_msgData_1453_);
    v___x_1467_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1467_, 0, v___x_1466_);
    return v___x_1467_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1_spec__1___boxed(
    mut v_msgData_1468_: *mut crate::leanh::LeanObject,
    mut v___y_1469_: *mut crate::leanh::LeanObject,
    mut v___y_1470_: *mut crate::leanh::LeanObject,
    mut v___y_1471_: *mut crate::leanh::LeanObject,
    mut v___y_1472_: *mut crate::leanh::LeanObject,
    mut v___y_1473_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1474_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1_spec__1(v_msgData_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_);
    crate::leanh::lean_dec(v___y_1472_);
    crate::leanh::lean_dec_ref(v___y_1471_);
    crate::leanh::lean_dec(v___y_1470_);
    crate::leanh::lean_dec_ref(v___y_1469_);
    return v_res_1474_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(
    mut v_msg_1475_: *mut crate::leanh::LeanObject,
    mut v___y_1476_: *mut crate::leanh::LeanObject,
    mut v___y_1477_: *mut crate::leanh::LeanObject,
    mut v___y_1478_: *mut crate::leanh::LeanObject,
    mut v___y_1479_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1486_: u8 = 0;
    let mut v___x_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1491_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1481_ = crate::leanh::lean_ctor_get(v___y_1478_, 5);
                v___x_1482_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1_spec__1(v_msg_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
                v_a_1483_ = crate::leanh::lean_ctor_get(v___x_1482_, 0);
                v_isSharedCheck_1491_ = (!crate::leanh::lean_is_exclusive(v___x_1482_)) as u8;
                if v_isSharedCheck_1491_ == 0 {
                    v___x_1485_ = v___x_1482_;
                    v_isShared_1486_ = v_isSharedCheck_1491_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1483_);
                    crate::leanh::lean_dec(v___x_1482_);
                    v___x_1485_ = crate::leanh::lean_box(0);
                    v_isShared_1486_ = v_isSharedCheck_1491_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_1481_);
                v___x_1487_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1487_, 0, v_ref_1481_);
                crate::leanh::lean_ctor_set(v___x_1487_, 1, v_a_1483_);
                if v_isShared_1486_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1485_, 1);
                    crate::leanh::lean_ctor_set(v___x_1485_, 0, v___x_1487_);
                    v___x_1489_ = v___x_1485_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1490_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1490_, 0, v___x_1487_);
                    v___x_1489_ = v_reuseFailAlloc_1490_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1489_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg___boxed(
    mut v_msg_1492_: *mut crate::leanh::LeanObject,
    mut v___y_1493_: *mut crate::leanh::LeanObject,
    mut v___y_1494_: *mut crate::leanh::LeanObject,
    mut v___y_1495_: *mut crate::leanh::LeanObject,
    mut v___y_1496_: *mut crate::leanh::LeanObject,
    mut v___y_1497_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1498_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v_msg_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_);
    crate::leanh::lean_dec(v___y_1496_);
    crate::leanh::lean_dec_ref(v___y_1495_);
    crate::leanh::lean_dec(v___y_1494_);
    crate::leanh::lean_dec_ref(v___y_1493_);
    return v_res_1498_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1500_ = l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__0;
    v___x_1501_ = l_Lean_stringToMessageData(v___x_1500_);
    return v___x_1501_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0(
    mut v_ctor_1502_: *mut crate::leanh::LeanObject,
    mut v_args_1503_: *mut crate::leanh::LeanObject,
    mut v___y_1504_: *mut crate::leanh::LeanObject,
    mut v___y_1505_: *mut crate::leanh::LeanObject,
    mut v___y_1506_: *mut crate::leanh::LeanObject,
    mut v___y_1507_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1510_: u8 = 0;
    let mut v___x_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: u8 = 0;
    let mut v___x_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: u8 = 0;
    let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: u8 = 0;
    let mut v___x_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: u8 = 0;
    let mut v___x_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: u8 = 0;
    let mut v___x_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: u8 = 0;
    let mut v___x_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1536_: u8 = 0;
    let mut v___x_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1540_: u8 = 0;
    let mut v___x_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: u8 = 0;
    let mut v___x_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1549_: u8 = 0;
    let mut v___x_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1553_: u8 = 0;
    let mut v___x_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: u8 = 0;
    let mut v___x_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1562_: u8 = 0;
    let mut v___x_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1566_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1521_ =
                    l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__0;
                v___x_1522_ = lean_string_dec_eq(v_ctor_1502_, v___x_1521_);
                if v___x_1522_ == 0 {
                    v___x_1523_ = l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__1;
                    v___x_1524_ = lean_string_dec_eq(v_ctor_1502_, v___x_1523_);
                    if v___x_1524_ == 0 {
                        v___x_1525_ = l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__2;
                        v___x_1526_ = lean_string_dec_eq(v_ctor_1502_, v___x_1525_);
                        if v___x_1526_ == 0 {
                            v___x_1527_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___redArg();
                            return v___x_1527_;
                        } else {
                            v___x_1528_ = lean_array_get_size(v_args_1503_);
                            v___x_1529_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_1530_ = lean_nat_dec_eq(v___x_1528_, v___x_1529_);
                            if v___x_1530_ == 0 {
                                v___x_1531_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once), _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
                                v___x_1532_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_1531_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
                                v_a_1533_ = crate::leanh::lean_ctor_get(v___x_1532_, 0);
                                v_isSharedCheck_1540_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1532_)) as u8;
                                if v_isSharedCheck_1540_ == 0 {
                                    v___x_1535_ = v___x_1532_;
                                    v_isShared_1536_ = v_isSharedCheck_1540_;
                                    state = 4;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1533_);
                                    crate::leanh::lean_dec(v___x_1532_);
                                    v___x_1535_ = crate::leanh::lean_box(0);
                                    v_isShared_1536_ = v_isSharedCheck_1540_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        v___x_1541_ = lean_array_get_size(v_args_1503_);
                        v___x_1542_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_1543_ = lean_nat_dec_eq(v___x_1541_, v___x_1542_);
                        if v___x_1543_ == 0 {
                            v___x_1544_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once), _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
                            v___x_1545_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_1544_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
                            v_a_1546_ = crate::leanh::lean_ctor_get(v___x_1545_, 0);
                            v_isSharedCheck_1553_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1545_)) as u8;
                            if v_isSharedCheck_1553_ == 0 {
                                v___x_1548_ = v___x_1545_;
                                v_isShared_1549_ = v_isSharedCheck_1553_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1546_);
                                crate::leanh::lean_dec(v___x_1545_);
                                v___x_1548_ = crate::leanh::lean_box(0);
                                v_isShared_1549_ = v_isSharedCheck_1553_;
                                state = 6;
                                continue;
                            }
                        } else {
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v___x_1554_ = lean_array_get_size(v_args_1503_);
                    v___x_1555_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1556_ = lean_nat_dec_eq(v___x_1554_, v___x_1555_);
                    if v___x_1556_ == 0 {
                        v___x_1557_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once), _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
                        v___x_1558_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_1557_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
                        v_a_1559_ = crate::leanh::lean_ctor_get(v___x_1558_, 0);
                        v_isSharedCheck_1566_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1558_)) as u8;
                        if v_isSharedCheck_1566_ == 0 {
                            v___x_1561_ = v___x_1558_;
                            v_isShared_1562_ = v_isSharedCheck_1566_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1559_);
                            crate::leanh::lean_dec(v___x_1558_);
                            v___x_1561_ = crate::leanh::lean_box(0);
                            v_isShared_1562_ = v_isSharedCheck_1566_;
                            state = 8;
                            continue;
                        }
                    } else {
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1510_ = 1;
                v___x_1511_ = crate::leanh::lean_box((v___x_1510_) as usize);
                v___x_1512_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1512_, 0, v___x_1511_);
                return v___x_1512_;
            }
            2 => {
                v___x_1514_ = 0;
                v___x_1515_ = crate::leanh::lean_box((v___x_1514_) as usize);
                v___x_1516_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1516_, 0, v___x_1515_);
                return v___x_1516_;
            }
            3 => {
                v___x_1518_ = 2;
                v___x_1519_ = crate::leanh::lean_box((v___x_1518_) as usize);
                v___x_1520_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1520_, 0, v___x_1519_);
                return v___x_1520_;
            }
            4 => {
                if v_isShared_1536_ == 0 {
                    v___x_1538_ = v___x_1535_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1539_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1539_, 0, v_a_1533_);
                    v___x_1538_ = v_reuseFailAlloc_1539_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1538_;
            }
            6 => {
                if v_isShared_1549_ == 0 {
                    v___x_1551_ = v___x_1548_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1552_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1552_, 0, v_a_1546_);
                    v___x_1551_ = v_reuseFailAlloc_1552_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1551_;
            }
            8 => {
                if v_isShared_1562_ == 0 {
                    v___x_1564_ = v___x_1561_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1565_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1565_, 0, v_a_1559_);
                    v___x_1564_ = v_reuseFailAlloc_1565_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1564_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___boxed(
    mut v_ctor_1567_: *mut crate::leanh::LeanObject,
    mut v_args_1568_: *mut crate::leanh::LeanObject,
    mut v___y_1569_: *mut crate::leanh::LeanObject,
    mut v___y_1570_: *mut crate::leanh::LeanObject,
    mut v___y_1571_: *mut crate::leanh::LeanObject,
    mut v___y_1572_: *mut crate::leanh::LeanObject,
    mut v___y_1573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1574_ = l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0(
        v_ctor_1567_,
        v_args_1568_,
        v___y_1569_,
        v___y_1570_,
        v___y_1571_,
        v___y_1572_,
    );
    crate::leanh::lean_dec(v___y_1572_);
    crate::leanh::lean_dec_ref(v___y_1571_);
    crate::leanh::lean_dec(v___y_1570_);
    crate::leanh::lean_dec_ref(v___y_1569_);
    crate::leanh::lean_dec_ref(v_args_1568_);
    crate::leanh::lean_dec_ref(v_ctor_1567_);
    return v_res_1574_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr(
    mut v_a_1576_: *mut crate::leanh::LeanObject,
    mut v_a_1577_: *mut crate::leanh::LeanObject,
    mut v_a_1578_: *mut crate::leanh::LeanObject,
    mut v_a_1579_: *mut crate::leanh::LeanObject,
    mut v_a_1580_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1582_ = l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___closed__0;
    v___x_1583_ = l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__4;
    v___x_1584_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(
        v___x_1583_,
        v___f_1582_,
        v_a_1576_,
        v_a_1577_,
        v_a_1578_,
        v_a_1579_,
        v_a_1580_,
    );
    return v___x_1584_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___boxed(
    mut v_a_1585_: *mut crate::leanh::LeanObject,
    mut v_a_1586_: *mut crate::leanh::LeanObject,
    mut v_a_1587_: *mut crate::leanh::LeanObject,
    mut v_a_1588_: *mut crate::leanh::LeanObject,
    mut v_a_1589_: *mut crate::leanh::LeanObject,
    mut v_a_1590_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1591_ = l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr(
        v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_,
    );
    crate::leanh::lean_dec(v_a_1589_);
    crate::leanh::lean_dec_ref(v_a_1588_);
    crate::leanh::lean_dec(v_a_1587_);
    crate::leanh::lean_dec_ref(v_a_1586_);
    return v_res_1591_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1(
    mut v_00_u03b1_1592_: *mut crate::leanh::LeanObject,
    mut v_msg_1593_: *mut crate::leanh::LeanObject,
    mut v___y_1594_: *mut crate::leanh::LeanObject,
    mut v___y_1595_: *mut crate::leanh::LeanObject,
    mut v___y_1596_: *mut crate::leanh::LeanObject,
    mut v___y_1597_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1599_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v_msg_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_);
    return v___x_1599_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___boxed(
    mut v_00_u03b1_1600_: *mut crate::leanh::LeanObject,
    mut v_msg_1601_: *mut crate::leanh::LeanObject,
    mut v___y_1602_: *mut crate::leanh::LeanObject,
    mut v___y_1603_: *mut crate::leanh::LeanObject,
    mut v___y_1604_: *mut crate::leanh::LeanObject,
    mut v___y_1605_: *mut crate::leanh::LeanObject,
    mut v___y_1606_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1607_ =
        l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1(
            v_00_u03b1_1600_,
            v_msg_1601_,
            v___y_1602_,
            v___y_1603_,
            v___y_1604_,
            v___y_1605_,
        );
    crate::leanh::lean_dec(v___y_1605_);
    crate::leanh::lean_dec_ref(v___y_1604_);
    crate::leanh::lean_dec(v___y_1603_);
    crate::leanh::lean_dec_ref(v___y_1602_);
    return v_res_1607_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1609_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__1_once),
        _init_l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__1,
    );
    v___x_1610_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1610_, 0, v___x_1609_);
    return v___x_1610_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1611_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals___closed__1_once),
        _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals___closed__1,
    );
    v___x_1612_ = l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals___closed__0;
    v___x_1613_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1613_, 0, v___x_1612_);
    crate::leanh::lean_ctor_set(v___x_1613_, 1, v___x_1611_);
    return v___x_1613_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1614_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals___closed__2_once),
        _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals___closed__2,
    );
    return v___x_1614_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___lam__0(
    mut v___x_1617_: *mut crate::leanh::LeanObject,
    mut v___x_1618_: *mut crate::leanh::LeanObject,
    mut v___x_1619_: *mut crate::leanh::LeanObject,
    mut v_ctor_1620_: *mut crate::leanh::LeanObject,
    mut v_args_1621_: *mut crate::leanh::LeanObject,
    mut v___y_1622_: *mut crate::leanh::LeanObject,
    mut v___y_1623_: *mut crate::leanh::LeanObject,
    mut v___y_1624_: *mut crate::leanh::LeanObject,
    mut v___y_1625_: *mut crate::leanh::LeanObject,
    mut v___y_1626_: *mut crate::leanh::LeanObject,
    mut v___y_1627_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: u8 = 0;
    let mut v___x_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: u8 = 0;
    let mut v___x_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: u8 = 0;
    let mut v___x_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1641_: u8 = 0;
    let mut v___x_1642_: u8 = 0;
    let mut v___x_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1650_: u8 = 0;
    let mut v_unused_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1655_: u8 = 0;
    let mut v___x_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1659_: u8 = 0;
    let mut v___x_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1665_: u8 = 0;
    let mut v___x_1666_: u8 = 0;
    let mut v___x_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1674_: u8 = 0;
    let mut v_unused_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1679_: u8 = 0;
    let mut v___x_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1683_: u8 = 0;
    let mut v___x_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1689_: u8 = 0;
    let mut v___x_1690_: u8 = 0;
    let mut v___x_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1698_: u8 = 0;
    let mut v_unused_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1703_: u8 = 0;
    let mut v___x_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1707_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1629_ =
                    l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__0;
                v___x_1630_ = lean_string_dec_eq(v_ctor_1620_, v___x_1629_);
                if v___x_1630_ == 0 {
                    v___x_1631_ = l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___lam__0___closed__0;
                    v___x_1632_ = lean_string_dec_eq(v_ctor_1620_, v___x_1631_);
                    if v___x_1632_ == 0 {
                        v___x_1633_ = l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___lam__0___closed__1;
                        v___x_1634_ = lean_string_dec_eq(v_ctor_1620_, v___x_1633_);
                        if v___x_1634_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_1619_);
                            crate::leanh::lean_dec_ref(v___x_1618_);
                            crate::leanh::lean_dec_ref(v___x_1617_);
                            v___x_1635_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___redArg();
                            return v___x_1635_;
                        } else {
                            v___x_1636_ = l_Lean_Name_mkStr4(
                                v___x_1617_,
                                v___x_1618_,
                                v___x_1619_,
                                v___x_1633_,
                            );
                            v___x_1637_ = crate::leanh::lean_unsigned_to_nat(0);
                            crate::leanh::lean_inc(v___x_1636_);
                            v___x_1638_ =
                                l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(
                                    v___x_1636_,
                                    v___x_1637_,
                                    v_args_1621_,
                                    v___y_1622_,
                                    v___y_1623_,
                                    v___y_1624_,
                                    v___y_1625_,
                                    v___y_1626_,
                                    v___y_1627_,
                                );
                            if crate::leanh::lean_obj_tag(v___x_1638_) == 0 {
                                v_isSharedCheck_1650_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1638_)) as u8;
                                if v_isSharedCheck_1650_ == 0 {
                                    v_unused_1651_ = crate::leanh::lean_ctor_get(v___x_1638_, 0);
                                    crate::leanh::lean_dec(v_unused_1651_);
                                    v___x_1640_ = v___x_1638_;
                                    v_isShared_1641_ = v_isSharedCheck_1650_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v___x_1638_);
                                    v___x_1640_ = crate::leanh::lean_box(0);
                                    v_isShared_1641_ = v_isSharedCheck_1650_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v___x_1636_);
                                v_a_1652_ = crate::leanh::lean_ctor_get(v___x_1638_, 0);
                                v_isSharedCheck_1659_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1638_)) as u8;
                                if v_isSharedCheck_1659_ == 0 {
                                    v___x_1654_ = v___x_1638_;
                                    v_isShared_1655_ = v_isSharedCheck_1659_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1652_);
                                    crate::leanh::lean_dec(v___x_1638_);
                                    v___x_1654_ = crate::leanh::lean_box(0);
                                    v_isShared_1655_ = v_isSharedCheck_1659_;
                                    state = 3;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v___x_1660_ =
                            l_Lean_Name_mkStr4(v___x_1617_, v___x_1618_, v___x_1619_, v___x_1631_);
                        v___x_1661_ = crate::leanh::lean_unsigned_to_nat(0);
                        crate::leanh::lean_inc(v___x_1660_);
                        v___x_1662_ =
                            l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(
                                v___x_1660_,
                                v___x_1661_,
                                v_args_1621_,
                                v___y_1622_,
                                v___y_1623_,
                                v___y_1624_,
                                v___y_1625_,
                                v___y_1626_,
                                v___y_1627_,
                            );
                        if crate::leanh::lean_obj_tag(v___x_1662_) == 0 {
                            v_isSharedCheck_1674_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1662_)) as u8;
                            if v_isSharedCheck_1674_ == 0 {
                                v_unused_1675_ = crate::leanh::lean_ctor_get(v___x_1662_, 0);
                                crate::leanh::lean_dec(v_unused_1675_);
                                v___x_1664_ = v___x_1662_;
                                v_isShared_1665_ = v_isSharedCheck_1674_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_1662_);
                                v___x_1664_ = crate::leanh::lean_box(0);
                                v_isShared_1665_ = v_isSharedCheck_1674_;
                                state = 5;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_1660_);
                            v_a_1676_ = crate::leanh::lean_ctor_get(v___x_1662_, 0);
                            v_isSharedCheck_1683_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1662_)) as u8;
                            if v_isSharedCheck_1683_ == 0 {
                                v___x_1678_ = v___x_1662_;
                                v_isShared_1679_ = v_isSharedCheck_1683_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1676_);
                                crate::leanh::lean_dec(v___x_1662_);
                                v___x_1678_ = crate::leanh::lean_box(0);
                                v_isShared_1679_ = v_isSharedCheck_1683_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                } else {
                    v___x_1684_ =
                        l_Lean_Name_mkStr4(v___x_1617_, v___x_1618_, v___x_1619_, v___x_1629_);
                    v___x_1685_ = crate::leanh::lean_unsigned_to_nat(0);
                    crate::leanh::lean_inc(v___x_1684_);
                    v___x_1686_ = l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(
                        v___x_1684_,
                        v___x_1685_,
                        v_args_1621_,
                        v___y_1622_,
                        v___y_1623_,
                        v___y_1624_,
                        v___y_1625_,
                        v___y_1626_,
                        v___y_1627_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1686_) == 0 {
                        v_isSharedCheck_1698_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1686_)) as u8;
                        if v_isSharedCheck_1698_ == 0 {
                            v_unused_1699_ = crate::leanh::lean_ctor_get(v___x_1686_, 0);
                            crate::leanh::lean_dec(v_unused_1699_);
                            v___x_1688_ = v___x_1686_;
                            v_isShared_1689_ = v_isSharedCheck_1698_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_1686_);
                            v___x_1688_ = crate::leanh::lean_box(0);
                            v_isShared_1689_ = v_isSharedCheck_1698_;
                            state = 9;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_1684_);
                        v_a_1700_ = crate::leanh::lean_ctor_get(v___x_1686_, 0);
                        v_isSharedCheck_1707_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1686_)) as u8;
                        if v_isSharedCheck_1707_ == 0 {
                            v___x_1702_ = v___x_1686_;
                            v_isShared_1703_ = v_isSharedCheck_1707_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1700_);
                            crate::leanh::lean_dec(v___x_1686_);
                            v___x_1702_ = crate::leanh::lean_box(0);
                            v_isShared_1703_ = v_isSharedCheck_1707_;
                            state = 11;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1642_ = 1;
                v___x_1643_ = crate::leanh::lean_box(0);
                v___x_1644_ = l_Lean_Expr_const___override(v___x_1636_, v___x_1643_);
                v___x_1645_ = crate::leanh::lean_box((v___x_1642_) as usize);
                v___x_1646_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1646_, 0, v___x_1645_);
                crate::leanh::lean_ctor_set(v___x_1646_, 1, v___x_1644_);
                if v_isShared_1641_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1640_, 0, v___x_1646_);
                    v___x_1648_ = v___x_1640_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1649_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1649_, 0, v___x_1646_);
                    v___x_1648_ = v_reuseFailAlloc_1649_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1648_;
            }
            3 => {
                if v_isShared_1655_ == 0 {
                    v___x_1657_ = v___x_1654_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1658_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_a_1652_);
                    v___x_1657_ = v_reuseFailAlloc_1658_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1657_;
            }
            5 => {
                v___x_1666_ = 2;
                v___x_1667_ = crate::leanh::lean_box(0);
                v___x_1668_ = l_Lean_Expr_const___override(v___x_1660_, v___x_1667_);
                v___x_1669_ = crate::leanh::lean_box((v___x_1666_) as usize);
                v___x_1670_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1670_, 0, v___x_1669_);
                crate::leanh::lean_ctor_set(v___x_1670_, 1, v___x_1668_);
                if v_isShared_1665_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1664_, 0, v___x_1670_);
                    v___x_1672_ = v___x_1664_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1673_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1673_, 0, v___x_1670_);
                    v___x_1672_ = v_reuseFailAlloc_1673_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1672_;
            }
            7 => {
                if v_isShared_1679_ == 0 {
                    v___x_1681_ = v___x_1678_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1682_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_a_1676_);
                    v___x_1681_ = v_reuseFailAlloc_1682_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1681_;
            }
            9 => {
                v___x_1690_ = 0;
                v___x_1691_ = crate::leanh::lean_box(0);
                v___x_1692_ = l_Lean_Expr_const___override(v___x_1684_, v___x_1691_);
                v___x_1693_ = crate::leanh::lean_box((v___x_1690_) as usize);
                v___x_1694_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1694_, 0, v___x_1693_);
                crate::leanh::lean_ctor_set(v___x_1694_, 1, v___x_1692_);
                if v_isShared_1689_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1688_, 0, v___x_1694_);
                    v___x_1696_ = v___x_1688_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1697_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1697_, 0, v___x_1694_);
                    v___x_1696_ = v_reuseFailAlloc_1697_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1696_;
            }
            11 => {
                if v_isShared_1703_ == 0 {
                    v___x_1705_ = v___x_1702_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1706_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1706_, 0, v_a_1700_);
                    v___x_1705_ = v_reuseFailAlloc_1706_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1705_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___lam__0___boxed(
    mut v___x_1708_: *mut crate::leanh::LeanObject,
    mut v___x_1709_: *mut crate::leanh::LeanObject,
    mut v___x_1710_: *mut crate::leanh::LeanObject,
    mut v_ctor_1711_: *mut crate::leanh::LeanObject,
    mut v_args_1712_: *mut crate::leanh::LeanObject,
    mut v___y_1713_: *mut crate::leanh::LeanObject,
    mut v___y_1714_: *mut crate::leanh::LeanObject,
    mut v___y_1715_: *mut crate::leanh::LeanObject,
    mut v___y_1716_: *mut crate::leanh::LeanObject,
    mut v___y_1717_: *mut crate::leanh::LeanObject,
    mut v___y_1718_: *mut crate::leanh::LeanObject,
    mut v___y_1719_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1720_ = l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___lam__0(
        v___x_1708_,
        v___x_1709_,
        v___x_1710_,
        v_ctor_1711_,
        v_args_1712_,
        v___y_1713_,
        v___y_1714_,
        v___y_1715_,
        v___y_1716_,
        v___y_1717_,
        v___y_1718_,
    );
    crate::leanh::lean_dec(v___y_1718_);
    crate::leanh::lean_dec_ref(v___y_1717_);
    crate::leanh::lean_dec(v___y_1716_);
    crate::leanh::lean_dec_ref(v___y_1715_);
    crate::leanh::lean_dec(v___y_1714_);
    crate::leanh::lean_dec_ref(v___y_1713_);
    crate::leanh::lean_dec_ref(v_args_1712_);
    crate::leanh::lean_dec_ref(v_ctor_1711_);
    return v_res_1720_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm(
    mut v_a_1730_: *mut crate::leanh::LeanObject,
    mut v_a_1731_: *mut crate::leanh::LeanObject,
    mut v_a_1732_: *mut crate::leanh::LeanObject,
    mut v_a_1733_: *mut crate::leanh::LeanObject,
    mut v_a_1734_: *mut crate::leanh::LeanObject,
    mut v_a_1735_: *mut crate::leanh::LeanObject,
    mut v_a_1736_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1738_ = l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___closed__1;
    v___x_1739_ = l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___closed__2;
    v___x_1740_ = l_Lean_Elab_ConfigEval_EvalTerm_withSimpleEvalStx___redArg(
        v___x_1739_,
        v___f_1738_,
        v_a_1730_,
        v_a_1731_,
        v_a_1732_,
        v_a_1733_,
        v_a_1734_,
        v_a_1735_,
        v_a_1736_,
    );
    return v___x_1740_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___boxed(
    mut v_a_1741_: *mut crate::leanh::LeanObject,
    mut v_a_1742_: *mut crate::leanh::LeanObject,
    mut v_a_1743_: *mut crate::leanh::LeanObject,
    mut v_a_1744_: *mut crate::leanh::LeanObject,
    mut v_a_1745_: *mut crate::leanh::LeanObject,
    mut v_a_1746_: *mut crate::leanh::LeanObject,
    mut v_a_1747_: *mut crate::leanh::LeanObject,
    mut v_a_1748_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1749_ = l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm(
        v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_,
    );
    crate::leanh::lean_dec(v_a_1747_);
    crate::leanh::lean_dec_ref(v_a_1746_);
    crate::leanh::lean_dec(v_a_1745_);
    crate::leanh::lean_dec_ref(v_a_1744_);
    crate::leanh::lean_dec(v_a_1743_);
    crate::leanh::lean_dec_ref(v_a_1742_);
    return v_res_1749_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1751_ = crate::leanh::lean_box(0);
    v___x_1752_ = l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___closed__2;
    v___x_1753_ = l_Lean_Expr_const___override(v___x_1752_, v___x_1751_);
    return v___x_1753_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1754_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__1_once),
        _init_l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__1,
    );
    v___x_1755_ = l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__0;
    v___x_1756_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1756_, 0, v___x_1755_);
    crate::leanh::lean_ctor_set(v___x_1756_, 1, v___x_1754_);
    return v___x_1756_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1757_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__2_once),
        _init_l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__2,
    );
    return v___x_1757_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode_evalExpr___lam__0(
    mut v_ctor_1758_: *mut crate::leanh::LeanObject,
    mut v_args_1759_: *mut crate::leanh::LeanObject,
    mut v___y_1760_: *mut crate::leanh::LeanObject,
    mut v___y_1761_: *mut crate::leanh::LeanObject,
    mut v___y_1762_: *mut crate::leanh::LeanObject,
    mut v___y_1763_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1766_: u8 = 0;
    let mut v___x_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: u8 = 0;
    let mut v___x_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: u8 = 0;
    let mut v___x_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: u8 = 0;
    let mut v___x_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: u8 = 0;
    let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: u8 = 0;
    let mut v___x_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: u8 = 0;
    let mut v___x_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1792_: u8 = 0;
    let mut v___x_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1796_: u8 = 0;
    let mut v___x_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: u8 = 0;
    let mut v___x_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1805_: u8 = 0;
    let mut v___x_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1809_: u8 = 0;
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: u8 = 0;
    let mut v___x_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1818_: u8 = 0;
    let mut v___x_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1822_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1777_ =
                    l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__0;
                v___x_1778_ = lean_string_dec_eq(v_ctor_1758_, v___x_1777_);
                if v___x_1778_ == 0 {
                    v___x_1779_ = l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___lam__0___closed__0;
                    v___x_1780_ = lean_string_dec_eq(v_ctor_1758_, v___x_1779_);
                    if v___x_1780_ == 0 {
                        v___x_1781_ = l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___lam__0___closed__1;
                        v___x_1782_ = lean_string_dec_eq(v_ctor_1758_, v___x_1781_);
                        if v___x_1782_ == 0 {
                            v___x_1783_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___redArg();
                            return v___x_1783_;
                        } else {
                            v___x_1784_ = lean_array_get_size(v_args_1759_);
                            v___x_1785_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_1786_ = lean_nat_dec_eq(v___x_1784_, v___x_1785_);
                            if v___x_1786_ == 0 {
                                v___x_1787_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once), _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
                                v___x_1788_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_1787_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_);
                                v_a_1789_ = crate::leanh::lean_ctor_get(v___x_1788_, 0);
                                v_isSharedCheck_1796_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1788_)) as u8;
                                if v_isSharedCheck_1796_ == 0 {
                                    v___x_1791_ = v___x_1788_;
                                    v_isShared_1792_ = v_isSharedCheck_1796_;
                                    state = 4;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1789_);
                                    crate::leanh::lean_dec(v___x_1788_);
                                    v___x_1791_ = crate::leanh::lean_box(0);
                                    v_isShared_1792_ = v_isSharedCheck_1796_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        v___x_1797_ = lean_array_get_size(v_args_1759_);
                        v___x_1798_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_1799_ = lean_nat_dec_eq(v___x_1797_, v___x_1798_);
                        if v___x_1799_ == 0 {
                            v___x_1800_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once), _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
                            v___x_1801_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_1800_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_);
                            v_a_1802_ = crate::leanh::lean_ctor_get(v___x_1801_, 0);
                            v_isSharedCheck_1809_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1801_)) as u8;
                            if v_isSharedCheck_1809_ == 0 {
                                v___x_1804_ = v___x_1801_;
                                v_isShared_1805_ = v_isSharedCheck_1809_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1802_);
                                crate::leanh::lean_dec(v___x_1801_);
                                v___x_1804_ = crate::leanh::lean_box(0);
                                v_isShared_1805_ = v_isSharedCheck_1809_;
                                state = 6;
                                continue;
                            }
                        } else {
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v___x_1810_ = lean_array_get_size(v_args_1759_);
                    v___x_1811_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1812_ = lean_nat_dec_eq(v___x_1810_, v___x_1811_);
                    if v___x_1812_ == 0 {
                        v___x_1813_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once), _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
                        v___x_1814_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_1813_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_);
                        v_a_1815_ = crate::leanh::lean_ctor_get(v___x_1814_, 0);
                        v_isSharedCheck_1822_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1814_)) as u8;
                        if v_isSharedCheck_1822_ == 0 {
                            v___x_1817_ = v___x_1814_;
                            v_isShared_1818_ = v_isSharedCheck_1822_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1815_);
                            crate::leanh::lean_dec(v___x_1814_);
                            v___x_1817_ = crate::leanh::lean_box(0);
                            v_isShared_1818_ = v_isSharedCheck_1822_;
                            state = 8;
                            continue;
                        }
                    } else {
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1766_ = 1;
                v___x_1767_ = crate::leanh::lean_box((v___x_1766_) as usize);
                v___x_1768_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1768_, 0, v___x_1767_);
                return v___x_1768_;
            }
            2 => {
                v___x_1770_ = 2;
                v___x_1771_ = crate::leanh::lean_box((v___x_1770_) as usize);
                v___x_1772_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1772_, 0, v___x_1771_);
                return v___x_1772_;
            }
            3 => {
                v___x_1774_ = 0;
                v___x_1775_ = crate::leanh::lean_box((v___x_1774_) as usize);
                v___x_1776_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1776_, 0, v___x_1775_);
                return v___x_1776_;
            }
            4 => {
                if v_isShared_1792_ == 0 {
                    v___x_1794_ = v___x_1791_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1795_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_a_1789_);
                    v___x_1794_ = v_reuseFailAlloc_1795_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1794_;
            }
            6 => {
                if v_isShared_1805_ == 0 {
                    v___x_1807_ = v___x_1804_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1808_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_a_1802_);
                    v___x_1807_ = v_reuseFailAlloc_1808_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1807_;
            }
            8 => {
                if v_isShared_1818_ == 0 {
                    v___x_1820_ = v___x_1817_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1821_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1821_, 0, v_a_1815_);
                    v___x_1820_ = v_reuseFailAlloc_1821_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1820_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode_evalExpr___lam__0___boxed(
    mut v_ctor_1823_: *mut crate::leanh::LeanObject,
    mut v_args_1824_: *mut crate::leanh::LeanObject,
    mut v___y_1825_: *mut crate::leanh::LeanObject,
    mut v___y_1826_: *mut crate::leanh::LeanObject,
    mut v___y_1827_: *mut crate::leanh::LeanObject,
    mut v___y_1828_: *mut crate::leanh::LeanObject,
    mut v___y_1829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1830_ = l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode_evalExpr___lam__0(
        v_ctor_1823_,
        v_args_1824_,
        v___y_1825_,
        v___y_1826_,
        v___y_1827_,
        v___y_1828_,
    );
    crate::leanh::lean_dec(v___y_1828_);
    crate::leanh::lean_dec_ref(v___y_1827_);
    crate::leanh::lean_dec(v___y_1826_);
    crate::leanh::lean_dec_ref(v___y_1825_);
    crate::leanh::lean_dec_ref(v_args_1824_);
    crate::leanh::lean_dec_ref(v_ctor_1823_);
    return v_res_1830_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode_evalExpr(
    mut v_a_1832_: *mut crate::leanh::LeanObject,
    mut v_a_1833_: *mut crate::leanh::LeanObject,
    mut v_a_1834_: *mut crate::leanh::LeanObject,
    mut v_a_1835_: *mut crate::leanh::LeanObject,
    mut v_a_1836_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1838_ = l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode_evalExpr___closed__0;
    v___x_1839_ = l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___closed__2;
    v___x_1840_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(
        v___x_1839_,
        v___f_1838_,
        v_a_1832_,
        v_a_1833_,
        v_a_1834_,
        v_a_1835_,
        v_a_1836_,
    );
    return v___x_1840_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode_evalExpr___boxed(
    mut v_a_1841_: *mut crate::leanh::LeanObject,
    mut v_a_1842_: *mut crate::leanh::LeanObject,
    mut v_a_1843_: *mut crate::leanh::LeanObject,
    mut v_a_1844_: *mut crate::leanh::LeanObject,
    mut v_a_1845_: *mut crate::leanh::LeanObject,
    mut v_a_1846_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1847_ = l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode_evalExpr(
        v_a_1841_, v_a_1842_, v_a_1843_, v_a_1844_, v_a_1845_,
    );
    crate::leanh::lean_dec(v_a_1845_);
    crate::leanh::lean_dec_ref(v_a_1844_);
    crate::leanh::lean_dec(v_a_1843_);
    crate::leanh::lean_dec_ref(v_a_1842_);
    return v_res_1847_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1849_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__1_once),
        _init_l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__1,
    );
    v___x_1850_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1850_, 0, v___x_1849_);
    return v___x_1850_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1851_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode___closed__1_once),
        _init_l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode___closed__1,
    );
    v___x_1852_ = l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode___closed__0;
    v___x_1853_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1853_, 0, v___x_1852_);
    crate::leanh::lean_ctor_set(v___x_1853_, 1, v___x_1851_);
    return v___x_1853_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1854_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode___closed__2_once),
        _init_l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode___closed__2,
    );
    return v___x_1854_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0(
    mut v___x_1858_: *mut crate::leanh::LeanObject,
    mut v___x_1859_: *mut crate::leanh::LeanObject,
    mut v___x_1860_: *mut crate::leanh::LeanObject,
    mut v_ctor_1861_: *mut crate::leanh::LeanObject,
    mut v_args_1862_: *mut crate::leanh::LeanObject,
    mut v___y_1863_: *mut crate::leanh::LeanObject,
    mut v___y_1864_: *mut crate::leanh::LeanObject,
    mut v___y_1865_: *mut crate::leanh::LeanObject,
    mut v___y_1866_: *mut crate::leanh::LeanObject,
    mut v___y_1867_: *mut crate::leanh::LeanObject,
    mut v___y_1868_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: u8 = 0;
    let mut v___x_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: u8 = 0;
    let mut v___x_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: u8 = 0;
    let mut v___x_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: u8 = 0;
    let mut v___x_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: u8 = 0;
    let mut v___x_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1886_: u8 = 0;
    let mut v___x_1887_: u8 = 0;
    let mut v___x_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1895_: u8 = 0;
    let mut v_unused_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1900_: u8 = 0;
    let mut v___x_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1904_: u8 = 0;
    let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1910_: u8 = 0;
    let mut v___x_1911_: u8 = 0;
    let mut v___x_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1919_: u8 = 0;
    let mut v_unused_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1924_: u8 = 0;
    let mut v___x_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1928_: u8 = 0;
    let mut v___x_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1934_: u8 = 0;
    let mut v___x_1935_: u8 = 0;
    let mut v___x_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1943_: u8 = 0;
    let mut v_unused_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1948_: u8 = 0;
    let mut v___x_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1952_: u8 = 0;
    let mut v___x_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1958_: u8 = 0;
    let mut v___x_1959_: u8 = 0;
    let mut v___x_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1967_: u8 = 0;
    let mut v_unused_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1972_: u8 = 0;
    let mut v___x_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1976_: u8 = 0;
    let mut v___x_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1982_: u8 = 0;
    let mut v___x_1983_: u8 = 0;
    let mut v___x_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1991_: u8 = 0;
    let mut v_unused_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1996_: u8 = 0;
    let mut v___x_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2000_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1870_ =
                    l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__0;
                v___x_1871_ = lean_string_dec_eq(v_ctor_1861_, v___x_1870_);
                if v___x_1871_ == 0 {
                    v___x_1872_ = l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__0;
                    v___x_1873_ = lean_string_dec_eq(v_ctor_1861_, v___x_1872_);
                    if v___x_1873_ == 0 {
                        v___x_1874_ = l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__1;
                        v___x_1875_ = lean_string_dec_eq(v_ctor_1861_, v___x_1874_);
                        if v___x_1875_ == 0 {
                            v___x_1876_ = l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___lam__0___closed__0;
                            v___x_1877_ = lean_string_dec_eq(v_ctor_1861_, v___x_1876_);
                            if v___x_1877_ == 0 {
                                v___x_1878_ = l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__2;
                                v___x_1879_ = lean_string_dec_eq(v_ctor_1861_, v___x_1878_);
                                if v___x_1879_ == 0 {
                                    crate::leanh::lean_dec_ref(v___x_1860_);
                                    crate::leanh::lean_dec_ref(v___x_1859_);
                                    crate::leanh::lean_dec_ref(v___x_1858_);
                                    v___x_1880_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___redArg();
                                    return v___x_1880_;
                                } else {
                                    v___x_1881_ = l_Lean_Name_mkStr4(
                                        v___x_1858_,
                                        v___x_1859_,
                                        v___x_1860_,
                                        v___x_1878_,
                                    );
                                    v___x_1882_ = crate::leanh::lean_unsigned_to_nat(0);
                                    crate::leanh::lean_inc(v___x_1881_);
                                    v___x_1883_ = l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(v___x_1881_, v___x_1882_, v_args_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_);
                                    if crate::leanh::lean_obj_tag(v___x_1883_) == 0 {
                                        v_isSharedCheck_1895_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_1883_)) as u8;
                                        if v_isSharedCheck_1895_ == 0 {
                                            v_unused_1896_ =
                                                crate::leanh::lean_ctor_get(v___x_1883_, 0);
                                            crate::leanh::lean_dec(v_unused_1896_);
                                            v___x_1885_ = v___x_1883_;
                                            v_isShared_1886_ = v_isSharedCheck_1895_;
                                            state = 1;
                                            continue;
                                        } else {
                                            crate::leanh::lean_dec(v___x_1883_);
                                            v___x_1885_ = crate::leanh::lean_box(0);
                                            v_isShared_1886_ = v_isSharedCheck_1895_;
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v___x_1881_);
                                        v_a_1897_ = crate::leanh::lean_ctor_get(v___x_1883_, 0);
                                        v_isSharedCheck_1904_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_1883_)) as u8;
                                        if v_isSharedCheck_1904_ == 0 {
                                            v___x_1899_ = v___x_1883_;
                                            v_isShared_1900_ = v_isSharedCheck_1904_;
                                            state = 3;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_1897_);
                                            crate::leanh::lean_dec(v___x_1883_);
                                            v___x_1899_ = crate::leanh::lean_box(0);
                                            v_isShared_1900_ = v_isSharedCheck_1904_;
                                            state = 3;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                v___x_1905_ = l_Lean_Name_mkStr4(
                                    v___x_1858_,
                                    v___x_1859_,
                                    v___x_1860_,
                                    v___x_1876_,
                                );
                                v___x_1906_ = crate::leanh::lean_unsigned_to_nat(0);
                                crate::leanh::lean_inc(v___x_1905_);
                                v___x_1907_ =
                                    l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(
                                        v___x_1905_,
                                        v___x_1906_,
                                        v_args_1862_,
                                        v___y_1863_,
                                        v___y_1864_,
                                        v___y_1865_,
                                        v___y_1866_,
                                        v___y_1867_,
                                        v___y_1868_,
                                    );
                                if crate::leanh::lean_obj_tag(v___x_1907_) == 0 {
                                    v_isSharedCheck_1919_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1907_)) as u8;
                                    if v_isSharedCheck_1919_ == 0 {
                                        v_unused_1920_ =
                                            crate::leanh::lean_ctor_get(v___x_1907_, 0);
                                        crate::leanh::lean_dec(v_unused_1920_);
                                        v___x_1909_ = v___x_1907_;
                                        v_isShared_1910_ = v_isSharedCheck_1919_;
                                        state = 5;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v___x_1907_);
                                        v___x_1909_ = crate::leanh::lean_box(0);
                                        v_isShared_1910_ = v_isSharedCheck_1919_;
                                        state = 5;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v___x_1905_);
                                    v_a_1921_ = crate::leanh::lean_ctor_get(v___x_1907_, 0);
                                    v_isSharedCheck_1928_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1907_)) as u8;
                                    if v_isSharedCheck_1928_ == 0 {
                                        v___x_1923_ = v___x_1907_;
                                        v_isShared_1924_ = v_isSharedCheck_1928_;
                                        state = 7;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_1921_);
                                        crate::leanh::lean_dec(v___x_1907_);
                                        v___x_1923_ = crate::leanh::lean_box(0);
                                        v_isShared_1924_ = v_isSharedCheck_1928_;
                                        state = 7;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            v___x_1929_ = l_Lean_Name_mkStr4(
                                v___x_1858_,
                                v___x_1859_,
                                v___x_1860_,
                                v___x_1874_,
                            );
                            v___x_1930_ = crate::leanh::lean_unsigned_to_nat(0);
                            crate::leanh::lean_inc(v___x_1929_);
                            v___x_1931_ =
                                l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(
                                    v___x_1929_,
                                    v___x_1930_,
                                    v_args_1862_,
                                    v___y_1863_,
                                    v___y_1864_,
                                    v___y_1865_,
                                    v___y_1866_,
                                    v___y_1867_,
                                    v___y_1868_,
                                );
                            if crate::leanh::lean_obj_tag(v___x_1931_) == 0 {
                                v_isSharedCheck_1943_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1931_)) as u8;
                                if v_isSharedCheck_1943_ == 0 {
                                    v_unused_1944_ = crate::leanh::lean_ctor_get(v___x_1931_, 0);
                                    crate::leanh::lean_dec(v_unused_1944_);
                                    v___x_1933_ = v___x_1931_;
                                    v_isShared_1934_ = v_isSharedCheck_1943_;
                                    state = 9;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v___x_1931_);
                                    v___x_1933_ = crate::leanh::lean_box(0);
                                    v_isShared_1934_ = v_isSharedCheck_1943_;
                                    state = 9;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v___x_1929_);
                                v_a_1945_ = crate::leanh::lean_ctor_get(v___x_1931_, 0);
                                v_isSharedCheck_1952_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1931_)) as u8;
                                if v_isSharedCheck_1952_ == 0 {
                                    v___x_1947_ = v___x_1931_;
                                    v_isShared_1948_ = v_isSharedCheck_1952_;
                                    state = 11;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1945_);
                                    crate::leanh::lean_dec(v___x_1931_);
                                    v___x_1947_ = crate::leanh::lean_box(0);
                                    v_isShared_1948_ = v_isSharedCheck_1952_;
                                    state = 11;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v___x_1953_ =
                            l_Lean_Name_mkStr4(v___x_1858_, v___x_1859_, v___x_1860_, v___x_1872_);
                        v___x_1954_ = crate::leanh::lean_unsigned_to_nat(0);
                        crate::leanh::lean_inc(v___x_1953_);
                        v___x_1955_ =
                            l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(
                                v___x_1953_,
                                v___x_1954_,
                                v_args_1862_,
                                v___y_1863_,
                                v___y_1864_,
                                v___y_1865_,
                                v___y_1866_,
                                v___y_1867_,
                                v___y_1868_,
                            );
                        if crate::leanh::lean_obj_tag(v___x_1955_) == 0 {
                            v_isSharedCheck_1967_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1955_)) as u8;
                            if v_isSharedCheck_1967_ == 0 {
                                v_unused_1968_ = crate::leanh::lean_ctor_get(v___x_1955_, 0);
                                crate::leanh::lean_dec(v_unused_1968_);
                                v___x_1957_ = v___x_1955_;
                                v_isShared_1958_ = v_isSharedCheck_1967_;
                                state = 13;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_1955_);
                                v___x_1957_ = crate::leanh::lean_box(0);
                                v_isShared_1958_ = v_isSharedCheck_1967_;
                                state = 13;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_1953_);
                            v_a_1969_ = crate::leanh::lean_ctor_get(v___x_1955_, 0);
                            v_isSharedCheck_1976_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1955_)) as u8;
                            if v_isSharedCheck_1976_ == 0 {
                                v___x_1971_ = v___x_1955_;
                                v_isShared_1972_ = v_isSharedCheck_1976_;
                                state = 15;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1969_);
                                crate::leanh::lean_dec(v___x_1955_);
                                v___x_1971_ = crate::leanh::lean_box(0);
                                v_isShared_1972_ = v_isSharedCheck_1976_;
                                state = 15;
                                continue;
                            }
                        }
                    }
                } else {
                    v___x_1977_ =
                        l_Lean_Name_mkStr4(v___x_1858_, v___x_1859_, v___x_1860_, v___x_1870_);
                    v___x_1978_ = crate::leanh::lean_unsigned_to_nat(0);
                    crate::leanh::lean_inc(v___x_1977_);
                    v___x_1979_ = l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(
                        v___x_1977_,
                        v___x_1978_,
                        v_args_1862_,
                        v___y_1863_,
                        v___y_1864_,
                        v___y_1865_,
                        v___y_1866_,
                        v___y_1867_,
                        v___y_1868_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1979_) == 0 {
                        v_isSharedCheck_1991_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1979_)) as u8;
                        if v_isSharedCheck_1991_ == 0 {
                            v_unused_1992_ = crate::leanh::lean_ctor_get(v___x_1979_, 0);
                            crate::leanh::lean_dec(v_unused_1992_);
                            v___x_1981_ = v___x_1979_;
                            v_isShared_1982_ = v_isSharedCheck_1991_;
                            state = 17;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_1979_);
                            v___x_1981_ = crate::leanh::lean_box(0);
                            v_isShared_1982_ = v_isSharedCheck_1991_;
                            state = 17;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_1977_);
                        v_a_1993_ = crate::leanh::lean_ctor_get(v___x_1979_, 0);
                        v_isSharedCheck_2000_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1979_)) as u8;
                        if v_isSharedCheck_2000_ == 0 {
                            v___x_1995_ = v___x_1979_;
                            v_isShared_1996_ = v_isSharedCheck_2000_;
                            state = 19;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1993_);
                            crate::leanh::lean_dec(v___x_1979_);
                            v___x_1995_ = crate::leanh::lean_box(0);
                            v_isShared_1996_ = v_isSharedCheck_2000_;
                            state = 19;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1887_ = 2;
                v___x_1888_ = crate::leanh::lean_box(0);
                v___x_1889_ = l_Lean_Expr_const___override(v___x_1881_, v___x_1888_);
                v___x_1890_ = crate::leanh::lean_box((v___x_1887_) as usize);
                v___x_1891_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1891_, 0, v___x_1890_);
                crate::leanh::lean_ctor_set(v___x_1891_, 1, v___x_1889_);
                if v_isShared_1886_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1885_, 0, v___x_1891_);
                    v___x_1893_ = v___x_1885_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1894_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1894_, 0, v___x_1891_);
                    v___x_1893_ = v_reuseFailAlloc_1894_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1893_;
            }
            3 => {
                if v_isShared_1900_ == 0 {
                    v___x_1902_ = v___x_1899_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1903_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1903_, 0, v_a_1897_);
                    v___x_1902_ = v_reuseFailAlloc_1903_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1902_;
            }
            5 => {
                v___x_1911_ = 4;
                v___x_1912_ = crate::leanh::lean_box(0);
                v___x_1913_ = l_Lean_Expr_const___override(v___x_1905_, v___x_1912_);
                v___x_1914_ = crate::leanh::lean_box((v___x_1911_) as usize);
                v___x_1915_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1915_, 0, v___x_1914_);
                crate::leanh::lean_ctor_set(v___x_1915_, 1, v___x_1913_);
                if v_isShared_1910_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1909_, 0, v___x_1915_);
                    v___x_1917_ = v___x_1909_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1918_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1918_, 0, v___x_1915_);
                    v___x_1917_ = v_reuseFailAlloc_1918_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1917_;
            }
            7 => {
                if v_isShared_1924_ == 0 {
                    v___x_1926_ = v___x_1923_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1927_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_a_1921_);
                    v___x_1926_ = v_reuseFailAlloc_1927_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1926_;
            }
            9 => {
                v___x_1935_ = 3;
                v___x_1936_ = crate::leanh::lean_box(0);
                v___x_1937_ = l_Lean_Expr_const___override(v___x_1929_, v___x_1936_);
                v___x_1938_ = crate::leanh::lean_box((v___x_1935_) as usize);
                v___x_1939_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1939_, 0, v___x_1938_);
                crate::leanh::lean_ctor_set(v___x_1939_, 1, v___x_1937_);
                if v_isShared_1934_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1933_, 0, v___x_1939_);
                    v___x_1941_ = v___x_1933_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1942_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1942_, 0, v___x_1939_);
                    v___x_1941_ = v_reuseFailAlloc_1942_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1941_;
            }
            11 => {
                if v_isShared_1948_ == 0 {
                    v___x_1950_ = v___x_1947_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1951_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_a_1945_);
                    v___x_1950_ = v_reuseFailAlloc_1951_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1950_;
            }
            13 => {
                v___x_1959_ = 1;
                v___x_1960_ = crate::leanh::lean_box(0);
                v___x_1961_ = l_Lean_Expr_const___override(v___x_1953_, v___x_1960_);
                v___x_1962_ = crate::leanh::lean_box((v___x_1959_) as usize);
                v___x_1963_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1963_, 0, v___x_1962_);
                crate::leanh::lean_ctor_set(v___x_1963_, 1, v___x_1961_);
                if v_isShared_1958_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1957_, 0, v___x_1963_);
                    v___x_1965_ = v___x_1957_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1966_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1966_, 0, v___x_1963_);
                    v___x_1965_ = v_reuseFailAlloc_1966_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_1965_;
            }
            15 => {
                if v_isShared_1972_ == 0 {
                    v___x_1974_ = v___x_1971_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1975_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1975_, 0, v_a_1969_);
                    v___x_1974_ = v_reuseFailAlloc_1975_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1974_;
            }
            17 => {
                v___x_1983_ = 0;
                v___x_1984_ = crate::leanh::lean_box(0);
                v___x_1985_ = l_Lean_Expr_const___override(v___x_1977_, v___x_1984_);
                v___x_1986_ = crate::leanh::lean_box((v___x_1983_) as usize);
                v___x_1987_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1987_, 0, v___x_1986_);
                crate::leanh::lean_ctor_set(v___x_1987_, 1, v___x_1985_);
                if v_isShared_1982_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1981_, 0, v___x_1987_);
                    v___x_1989_ = v___x_1981_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1990_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1990_, 0, v___x_1987_);
                    v___x_1989_ = v_reuseFailAlloc_1990_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_1989_;
            }
            19 => {
                if v_isShared_1996_ == 0 {
                    v___x_1998_ = v___x_1995_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1999_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1999_, 0, v_a_1993_);
                    v___x_1998_ = v_reuseFailAlloc_1999_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_1998_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___boxed(
    mut v___x_2001_: *mut crate::leanh::LeanObject,
    mut v___x_2002_: *mut crate::leanh::LeanObject,
    mut v___x_2003_: *mut crate::leanh::LeanObject,
    mut v_ctor_2004_: *mut crate::leanh::LeanObject,
    mut v_args_2005_: *mut crate::leanh::LeanObject,
    mut v___y_2006_: *mut crate::leanh::LeanObject,
    mut v___y_2007_: *mut crate::leanh::LeanObject,
    mut v___y_2008_: *mut crate::leanh::LeanObject,
    mut v___y_2009_: *mut crate::leanh::LeanObject,
    mut v___y_2010_: *mut crate::leanh::LeanObject,
    mut v___y_2011_: *mut crate::leanh::LeanObject,
    mut v___y_2012_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2013_ = l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0(
        v___x_2001_,
        v___x_2002_,
        v___x_2003_,
        v_ctor_2004_,
        v_args_2005_,
        v___y_2006_,
        v___y_2007_,
        v___y_2008_,
        v___y_2009_,
        v___y_2010_,
        v___y_2011_,
    );
    crate::leanh::lean_dec(v___y_2011_);
    crate::leanh::lean_dec_ref(v___y_2010_);
    crate::leanh::lean_dec(v___y_2009_);
    crate::leanh::lean_dec_ref(v___y_2008_);
    crate::leanh::lean_dec(v___y_2007_);
    crate::leanh::lean_dec_ref(v___y_2006_);
    crate::leanh::lean_dec_ref(v_args_2005_);
    crate::leanh::lean_dec_ref(v_ctor_2004_);
    return v_res_2013_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm(
    mut v_a_2023_: *mut crate::leanh::LeanObject,
    mut v_a_2024_: *mut crate::leanh::LeanObject,
    mut v_a_2025_: *mut crate::leanh::LeanObject,
    mut v_a_2026_: *mut crate::leanh::LeanObject,
    mut v_a_2027_: *mut crate::leanh::LeanObject,
    mut v_a_2028_: *mut crate::leanh::LeanObject,
    mut v_a_2029_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2031_ = l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___closed__1;
    v___x_2032_ = l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___closed__2;
    v___x_2033_ = l_Lean_Elab_ConfigEval_EvalTerm_withSimpleEvalStx___redArg(
        v___x_2032_,
        v___f_2031_,
        v_a_2023_,
        v_a_2024_,
        v_a_2025_,
        v_a_2026_,
        v_a_2027_,
        v_a_2028_,
        v_a_2029_,
    );
    return v___x_2033_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___boxed(
    mut v_a_2034_: *mut crate::leanh::LeanObject,
    mut v_a_2035_: *mut crate::leanh::LeanObject,
    mut v_a_2036_: *mut crate::leanh::LeanObject,
    mut v_a_2037_: *mut crate::leanh::LeanObject,
    mut v_a_2038_: *mut crate::leanh::LeanObject,
    mut v_a_2039_: *mut crate::leanh::LeanObject,
    mut v_a_2040_: *mut crate::leanh::LeanObject,
    mut v_a_2041_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2042_ = l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm(
        v_a_2034_, v_a_2035_, v_a_2036_, v_a_2037_, v_a_2038_, v_a_2039_, v_a_2040_,
    );
    crate::leanh::lean_dec(v_a_2040_);
    crate::leanh::lean_dec_ref(v_a_2039_);
    crate::leanh::lean_dec(v_a_2038_);
    crate::leanh::lean_dec_ref(v_a_2037_);
    crate::leanh::lean_dec(v_a_2036_);
    crate::leanh::lean_dec_ref(v_a_2035_);
    return v_res_2042_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2044_ = crate::leanh::lean_box(0);
    v___x_2045_ = l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___closed__2;
    v___x_2046_ = l_Lean_Expr_const___override(v___x_2045_, v___x_2044_);
    return v___x_2046_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2047_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__1_once
        ),
        _init_l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__1,
    );
    v___x_2048_ = l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__0;
    v___x_2049_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2049_, 0, v___x_2048_);
    crate::leanh::lean_ctor_set(v___x_2049_, 1, v___x_2047_);
    return v___x_2049_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2050_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__2),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__2_once
        ),
        _init_l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__2,
    );
    return v___x_2050_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr___lam__0(
    mut v_ctor_2051_: *mut crate::leanh::LeanObject,
    mut v_args_2052_: *mut crate::leanh::LeanObject,
    mut v___y_2053_: *mut crate::leanh::LeanObject,
    mut v___y_2054_: *mut crate::leanh::LeanObject,
    mut v___y_2055_: *mut crate::leanh::LeanObject,
    mut v___y_2056_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2059_: u8 = 0;
    let mut v___x_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: u8 = 0;
    let mut v___x_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: u8 = 0;
    let mut v___x_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: u8 = 0;
    let mut v___x_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: u8 = 0;
    let mut v___x_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: u8 = 0;
    let mut v___x_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: u8 = 0;
    let mut v___x_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: u8 = 0;
    let mut v___x_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: u8 = 0;
    let mut v___x_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: u8 = 0;
    let mut v___x_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: u8 = 0;
    let mut v___x_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2097_: u8 = 0;
    let mut v___x_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2101_: u8 = 0;
    let mut v___x_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: u8 = 0;
    let mut v___x_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2110_: u8 = 0;
    let mut v___x_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2114_: u8 = 0;
    let mut v___x_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: u8 = 0;
    let mut v___x_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2123_: u8 = 0;
    let mut v___x_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2127_: u8 = 0;
    let mut v___x_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: u8 = 0;
    let mut v___x_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2136_: u8 = 0;
    let mut v___x_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2140_: u8 = 0;
    let mut v___x_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: u8 = 0;
    let mut v___x_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2149_: u8 = 0;
    let mut v___x_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2153_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2078_ =
                    l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__0;
                v___x_2079_ = lean_string_dec_eq(v_ctor_2051_, v___x_2078_);
                if v___x_2079_ == 0 {
                    v___x_2080_ = l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__0;
                    v___x_2081_ = lean_string_dec_eq(v_ctor_2051_, v___x_2080_);
                    if v___x_2081_ == 0 {
                        v___x_2082_ = l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__1;
                        v___x_2083_ = lean_string_dec_eq(v_ctor_2051_, v___x_2082_);
                        if v___x_2083_ == 0 {
                            v___x_2084_ = l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___lam__0___closed__0;
                            v___x_2085_ = lean_string_dec_eq(v_ctor_2051_, v___x_2084_);
                            if v___x_2085_ == 0 {
                                v___x_2086_ = l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__2;
                                v___x_2087_ = lean_string_dec_eq(v_ctor_2051_, v___x_2086_);
                                if v___x_2087_ == 0 {
                                    v___x_2088_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___redArg();
                                    return v___x_2088_;
                                } else {
                                    v___x_2089_ = lean_array_get_size(v_args_2052_);
                                    v___x_2090_ = crate::leanh::lean_unsigned_to_nat(0);
                                    v___x_2091_ = lean_nat_dec_eq(v___x_2089_, v___x_2090_);
                                    if v___x_2091_ == 0 {
                                        v___x_2092_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once), _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
                                        v___x_2093_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_2092_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_);
                                        v_a_2094_ = crate::leanh::lean_ctor_get(v___x_2093_, 0);
                                        v_isSharedCheck_2101_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2093_)) as u8;
                                        if v_isSharedCheck_2101_ == 0 {
                                            v___x_2096_ = v___x_2093_;
                                            v_isShared_2097_ = v_isSharedCheck_2101_;
                                            state = 6;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_2094_);
                                            crate::leanh::lean_dec(v___x_2093_);
                                            v___x_2096_ = crate::leanh::lean_box(0);
                                            v_isShared_2097_ = v_isSharedCheck_2101_;
                                            state = 6;
                                            continue;
                                        }
                                    } else {
                                        state = 1;
                                        continue;
                                    }
                                }
                            } else {
                                v___x_2102_ = lean_array_get_size(v_args_2052_);
                                v___x_2103_ = crate::leanh::lean_unsigned_to_nat(0);
                                v___x_2104_ = lean_nat_dec_eq(v___x_2102_, v___x_2103_);
                                if v___x_2104_ == 0 {
                                    v___x_2105_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once), _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
                                    v___x_2106_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_2105_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_);
                                    v_a_2107_ = crate::leanh::lean_ctor_get(v___x_2106_, 0);
                                    v_isSharedCheck_2114_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2106_)) as u8;
                                    if v_isSharedCheck_2114_ == 0 {
                                        v___x_2109_ = v___x_2106_;
                                        v_isShared_2110_ = v_isSharedCheck_2114_;
                                        state = 8;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2107_);
                                        crate::leanh::lean_dec(v___x_2106_);
                                        v___x_2109_ = crate::leanh::lean_box(0);
                                        v_isShared_2110_ = v_isSharedCheck_2114_;
                                        state = 8;
                                        continue;
                                    }
                                } else {
                                    state = 2;
                                    continue;
                                }
                            }
                        } else {
                            v___x_2115_ = lean_array_get_size(v_args_2052_);
                            v___x_2116_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_2117_ = lean_nat_dec_eq(v___x_2115_, v___x_2116_);
                            if v___x_2117_ == 0 {
                                v___x_2118_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once), _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
                                v___x_2119_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_2118_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_);
                                v_a_2120_ = crate::leanh::lean_ctor_get(v___x_2119_, 0);
                                v_isSharedCheck_2127_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2119_)) as u8;
                                if v_isSharedCheck_2127_ == 0 {
                                    v___x_2122_ = v___x_2119_;
                                    v_isShared_2123_ = v_isSharedCheck_2127_;
                                    state = 10;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2120_);
                                    crate::leanh::lean_dec(v___x_2119_);
                                    v___x_2122_ = crate::leanh::lean_box(0);
                                    v_isShared_2123_ = v_isSharedCheck_2127_;
                                    state = 10;
                                    continue;
                                }
                            } else {
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        v___x_2128_ = lean_array_get_size(v_args_2052_);
                        v___x_2129_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_2130_ = lean_nat_dec_eq(v___x_2128_, v___x_2129_);
                        if v___x_2130_ == 0 {
                            v___x_2131_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once), _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
                            v___x_2132_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_2131_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_);
                            v_a_2133_ = crate::leanh::lean_ctor_get(v___x_2132_, 0);
                            v_isSharedCheck_2140_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2132_)) as u8;
                            if v_isSharedCheck_2140_ == 0 {
                                v___x_2135_ = v___x_2132_;
                                v_isShared_2136_ = v_isSharedCheck_2140_;
                                state = 12;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2133_);
                                crate::leanh::lean_dec(v___x_2132_);
                                v___x_2135_ = crate::leanh::lean_box(0);
                                v_isShared_2136_ = v_isSharedCheck_2140_;
                                state = 12;
                                continue;
                            }
                        } else {
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v___x_2141_ = lean_array_get_size(v_args_2052_);
                    v___x_2142_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2143_ = lean_nat_dec_eq(v___x_2141_, v___x_2142_);
                    if v___x_2143_ == 0 {
                        v___x_2144_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once), _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
                        v___x_2145_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_2144_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_);
                        v_a_2146_ = crate::leanh::lean_ctor_get(v___x_2145_, 0);
                        v_isSharedCheck_2153_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2145_)) as u8;
                        if v_isSharedCheck_2153_ == 0 {
                            v___x_2148_ = v___x_2145_;
                            v_isShared_2149_ = v_isSharedCheck_2153_;
                            state = 14;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2146_);
                            crate::leanh::lean_dec(v___x_2145_);
                            v___x_2148_ = crate::leanh::lean_box(0);
                            v_isShared_2149_ = v_isSharedCheck_2153_;
                            state = 14;
                            continue;
                        }
                    } else {
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2059_ = 2;
                v___x_2060_ = crate::leanh::lean_box((v___x_2059_) as usize);
                v___x_2061_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2061_, 0, v___x_2060_);
                return v___x_2061_;
            }
            2 => {
                v___x_2063_ = 4;
                v___x_2064_ = crate::leanh::lean_box((v___x_2063_) as usize);
                v___x_2065_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2065_, 0, v___x_2064_);
                return v___x_2065_;
            }
            3 => {
                v___x_2067_ = 3;
                v___x_2068_ = crate::leanh::lean_box((v___x_2067_) as usize);
                v___x_2069_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2069_, 0, v___x_2068_);
                return v___x_2069_;
            }
            4 => {
                v___x_2071_ = 1;
                v___x_2072_ = crate::leanh::lean_box((v___x_2071_) as usize);
                v___x_2073_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2073_, 0, v___x_2072_);
                return v___x_2073_;
            }
            5 => {
                v___x_2075_ = 0;
                v___x_2076_ = crate::leanh::lean_box((v___x_2075_) as usize);
                v___x_2077_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2077_, 0, v___x_2076_);
                return v___x_2077_;
            }
            6 => {
                if v_isShared_2097_ == 0 {
                    v___x_2099_ = v___x_2096_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2100_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2100_, 0, v_a_2094_);
                    v___x_2099_ = v_reuseFailAlloc_2100_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2099_;
            }
            8 => {
                if v_isShared_2110_ == 0 {
                    v___x_2112_ = v___x_2109_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2113_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2113_, 0, v_a_2107_);
                    v___x_2112_ = v_reuseFailAlloc_2113_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2112_;
            }
            10 => {
                if v_isShared_2123_ == 0 {
                    v___x_2125_ = v___x_2122_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2126_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_a_2120_);
                    v___x_2125_ = v_reuseFailAlloc_2126_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2125_;
            }
            12 => {
                if v_isShared_2136_ == 0 {
                    v___x_2138_ = v___x_2135_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2139_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_a_2133_);
                    v___x_2138_ = v_reuseFailAlloc_2139_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2138_;
            }
            14 => {
                if v_isShared_2149_ == 0 {
                    v___x_2151_ = v___x_2148_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2152_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_a_2146_);
                    v___x_2151_ = v_reuseFailAlloc_2152_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2151_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr___lam__0___boxed(
    mut v_ctor_2154_: *mut crate::leanh::LeanObject,
    mut v_args_2155_: *mut crate::leanh::LeanObject,
    mut v___y_2156_: *mut crate::leanh::LeanObject,
    mut v___y_2157_: *mut crate::leanh::LeanObject,
    mut v___y_2158_: *mut crate::leanh::LeanObject,
    mut v___y_2159_: *mut crate::leanh::LeanObject,
    mut v___y_2160_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2161_ = l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr___lam__0(
        v_ctor_2154_,
        v_args_2155_,
        v___y_2156_,
        v___y_2157_,
        v___y_2158_,
        v___y_2159_,
    );
    crate::leanh::lean_dec(v___y_2159_);
    crate::leanh::lean_dec_ref(v___y_2158_);
    crate::leanh::lean_dec(v___y_2157_);
    crate::leanh::lean_dec_ref(v___y_2156_);
    crate::leanh::lean_dec_ref(v_args_2155_);
    crate::leanh::lean_dec_ref(v_ctor_2154_);
    return v_res_2161_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr(
    mut v_a_2163_: *mut crate::leanh::LeanObject,
    mut v_a_2164_: *mut crate::leanh::LeanObject,
    mut v_a_2165_: *mut crate::leanh::LeanObject,
    mut v_a_2166_: *mut crate::leanh::LeanObject,
    mut v_a_2167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2169_ = l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr___closed__0;
    v___x_2170_ = l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___closed__2;
    v___x_2171_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(
        v___x_2170_,
        v___f_2169_,
        v_a_2163_,
        v_a_2164_,
        v_a_2165_,
        v_a_2166_,
        v_a_2167_,
    );
    return v___x_2171_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr___boxed(
    mut v_a_2172_: *mut crate::leanh::LeanObject,
    mut v_a_2173_: *mut crate::leanh::LeanObject,
    mut v_a_2174_: *mut crate::leanh::LeanObject,
    mut v_a_2175_: *mut crate::leanh::LeanObject,
    mut v_a_2176_: *mut crate::leanh::LeanObject,
    mut v_a_2177_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2178_ = l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr(
        v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_,
    );
    crate::leanh::lean_dec(v_a_2176_);
    crate::leanh::lean_dec_ref(v_a_2175_);
    crate::leanh::lean_dec(v_a_2174_);
    crate::leanh::lean_dec_ref(v_a_2173_);
    return v_res_2178_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2180_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__1_once
        ),
        _init_l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__1,
    );
    v___x_2181_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2181_, 0, v___x_2180_);
    return v___x_2181_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2182_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__1_once
        ),
        _init_l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__1,
    );
    v___x_2183_ = l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__0;
    v___x_2184_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2184_, 0, v___x_2183_);
    crate::leanh::lean_ctor_set(v___x_2184_, 1, v___x_2182_);
    return v___x_2184_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2185_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__2),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__2_once
        ),
        _init_l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__2,
    );
    return v___x_2185_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2191_ = crate::leanh::lean_box(0);
    v___x_2192_ = l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__3;
    v___x_2193_ = l_Lean_mkConst(v___x_2192_, v___x_2191_);
    return v___x_2193_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0(
    mut v___x_2195_: *mut crate::leanh::LeanObject,
    mut v___x_2196_: *mut crate::leanh::LeanObject,
    mut v___x_2197_: *mut crate::leanh::LeanObject,
    mut v_ctor_2198_: *mut crate::leanh::LeanObject,
    mut v_args_2199_: *mut crate::leanh::LeanObject,
    mut v___y_2200_: *mut crate::leanh::LeanObject,
    mut v___y_2201_: *mut crate::leanh::LeanObject,
    mut v___y_2202_: *mut crate::leanh::LeanObject,
    mut v___y_2203_: *mut crate::leanh::LeanObject,
    mut v___y_2204_: *mut crate::leanh::LeanObject,
    mut v___y_2205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: u8 = 0;
    let mut v___x_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: u8 = 0;
    let mut v___x_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: u8 = 0;
    let mut v___x_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2227_: u8 = 0;
    let mut v_fst_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2232_: u8 = 0;
    let mut v___x_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2242_: u8 = 0;
    let mut v_isSharedCheck_2243_: u8 = 0;
    let mut v_a_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2247_: u8 = 0;
    let mut v___x_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2251_: u8 = 0;
    let mut v_a_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2255_: u8 = 0;
    let mut v___x_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2259_: u8 = 0;
    let mut v___x_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2273_: u8 = 0;
    let mut v_fst_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2278_: u8 = 0;
    let mut v___x_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2288_: u8 = 0;
    let mut v_isSharedCheck_2289_: u8 = 0;
    let mut v_a_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2293_: u8 = 0;
    let mut v___x_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2297_: u8 = 0;
    let mut v_a_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2301_: u8 = 0;
    let mut v___x_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2305_: u8 = 0;
    let mut v___x_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2311_: u8 = 0;
    let mut v___x_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2319_: u8 = 0;
    let mut v_unused_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2324_: u8 = 0;
    let mut v___x_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2328_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2207_ =
                    l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__0;
                v___x_2208_ = lean_string_dec_eq(v_ctor_2198_, v___x_2207_);
                if v___x_2208_ == 0 {
                    v___x_2209_ = l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__0;
                    v___x_2210_ = lean_string_dec_eq(v_ctor_2198_, v___x_2209_);
                    if v___x_2210_ == 0 {
                        v___x_2211_ = l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__1;
                        v___x_2212_ = lean_string_dec_eq(v_ctor_2198_, v___x_2211_);
                        if v___x_2212_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_2197_);
                            crate::leanh::lean_dec_ref(v___x_2196_);
                            crate::leanh::lean_dec_ref(v___x_2195_);
                            v___x_2213_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___redArg();
                            return v___x_2213_;
                        } else {
                            v___x_2214_ = l_Lean_Name_mkStr4(
                                v___x_2195_,
                                v___x_2196_,
                                v___x_2197_,
                                v___x_2211_,
                            );
                            v___x_2215_ = crate::leanh::lean_unsigned_to_nat(1);
                            crate::leanh::lean_inc(v___x_2214_);
                            v___x_2216_ =
                                l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(
                                    v___x_2214_,
                                    v___x_2215_,
                                    v_args_2199_,
                                    v___y_2200_,
                                    v___y_2201_,
                                    v___y_2202_,
                                    v___y_2203_,
                                    v___y_2204_,
                                    v___y_2205_,
                                );
                            if crate::leanh::lean_obj_tag(v___x_2216_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_2216_, 1);
                                v___x_2217_ = crate::leanh::lean_box(0);
                                v___x_2218_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__4), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__4_once), _init_l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__4);
                                v___x_2219_ = l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__5;
                                v___x_2220_ = crate::leanh::lean_box(0);
                                v___x_2221_ = crate::leanh::lean_unsigned_to_nat(0);
                                v___x_2222_ =
                                    lean_array_get_borrowed(v___x_2220_, v_args_2199_, v___x_2221_);
                                crate::leanh::lean_inc(v___x_2222_);
                                v___x_2223_ = l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg(
                                    v___x_2218_,
                                    v___x_2219_,
                                    v___x_2222_,
                                    v___y_2200_,
                                    v___y_2201_,
                                    v___y_2202_,
                                    v___y_2203_,
                                    v___y_2204_,
                                    v___y_2205_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_2223_) == 0 {
                                    v_a_2224_ = crate::leanh::lean_ctor_get(v___x_2223_, 0);
                                    v_isSharedCheck_2243_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2223_)) as u8;
                                    if v_isSharedCheck_2243_ == 0 {
                                        v___x_2226_ = v___x_2223_;
                                        v_isShared_2227_ = v_isSharedCheck_2243_;
                                        state = 1;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2224_);
                                        crate::leanh::lean_dec(v___x_2223_);
                                        v___x_2226_ = crate::leanh::lean_box(0);
                                        v_isShared_2227_ = v_isSharedCheck_2243_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v___x_2214_);
                                    v_a_2244_ = crate::leanh::lean_ctor_get(v___x_2223_, 0);
                                    v_isSharedCheck_2251_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2223_)) as u8;
                                    if v_isSharedCheck_2251_ == 0 {
                                        v___x_2246_ = v___x_2223_;
                                        v_isShared_2247_ = v_isSharedCheck_2251_;
                                        state = 5;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2244_);
                                        crate::leanh::lean_dec(v___x_2223_);
                                        v___x_2246_ = crate::leanh::lean_box(0);
                                        v_isShared_2247_ = v_isSharedCheck_2251_;
                                        state = 5;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v___x_2214_);
                                v_a_2252_ = crate::leanh::lean_ctor_get(v___x_2216_, 0);
                                v_isSharedCheck_2259_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2216_)) as u8;
                                if v_isSharedCheck_2259_ == 0 {
                                    v___x_2254_ = v___x_2216_;
                                    v_isShared_2255_ = v_isSharedCheck_2259_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2252_);
                                    crate::leanh::lean_dec(v___x_2216_);
                                    v___x_2254_ = crate::leanh::lean_box(0);
                                    v_isShared_2255_ = v_isSharedCheck_2259_;
                                    state = 7;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v___x_2260_ =
                            l_Lean_Name_mkStr4(v___x_2195_, v___x_2196_, v___x_2197_, v___x_2209_);
                        v___x_2261_ = crate::leanh::lean_unsigned_to_nat(1);
                        crate::leanh::lean_inc(v___x_2260_);
                        v___x_2262_ =
                            l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(
                                v___x_2260_,
                                v___x_2261_,
                                v_args_2199_,
                                v___y_2200_,
                                v___y_2201_,
                                v___y_2202_,
                                v___y_2203_,
                                v___y_2204_,
                                v___y_2205_,
                            );
                        if crate::leanh::lean_obj_tag(v___x_2262_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_2262_, 1);
                            v___x_2263_ = crate::leanh::lean_box(0);
                            v___x_2264_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__4), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__4_once), _init_l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__4);
                            v___x_2265_ = l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__5;
                            v___x_2266_ = crate::leanh::lean_box(0);
                            v___x_2267_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_2268_ =
                                lean_array_get_borrowed(v___x_2266_, v_args_2199_, v___x_2267_);
                            crate::leanh::lean_inc(v___x_2268_);
                            v___x_2269_ = l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg(
                                v___x_2264_,
                                v___x_2265_,
                                v___x_2268_,
                                v___y_2200_,
                                v___y_2201_,
                                v___y_2202_,
                                v___y_2203_,
                                v___y_2204_,
                                v___y_2205_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_2269_) == 0 {
                                v_a_2270_ = crate::leanh::lean_ctor_get(v___x_2269_, 0);
                                v_isSharedCheck_2289_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2269_)) as u8;
                                if v_isSharedCheck_2289_ == 0 {
                                    v___x_2272_ = v___x_2269_;
                                    v_isShared_2273_ = v_isSharedCheck_2289_;
                                    state = 9;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2270_);
                                    crate::leanh::lean_dec(v___x_2269_);
                                    v___x_2272_ = crate::leanh::lean_box(0);
                                    v_isShared_2273_ = v_isSharedCheck_2289_;
                                    state = 9;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v___x_2260_);
                                v_a_2290_ = crate::leanh::lean_ctor_get(v___x_2269_, 0);
                                v_isSharedCheck_2297_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2269_)) as u8;
                                if v_isSharedCheck_2297_ == 0 {
                                    v___x_2292_ = v___x_2269_;
                                    v_isShared_2293_ = v_isSharedCheck_2297_;
                                    state = 13;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2290_);
                                    crate::leanh::lean_dec(v___x_2269_);
                                    v___x_2292_ = crate::leanh::lean_box(0);
                                    v_isShared_2293_ = v_isSharedCheck_2297_;
                                    state = 13;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_2260_);
                            v_a_2298_ = crate::leanh::lean_ctor_get(v___x_2262_, 0);
                            v_isSharedCheck_2305_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2262_)) as u8;
                            if v_isSharedCheck_2305_ == 0 {
                                v___x_2300_ = v___x_2262_;
                                v_isShared_2301_ = v_isSharedCheck_2305_;
                                state = 15;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2298_);
                                crate::leanh::lean_dec(v___x_2262_);
                                v___x_2300_ = crate::leanh::lean_box(0);
                                v_isShared_2301_ = v_isSharedCheck_2305_;
                                state = 15;
                                continue;
                            }
                        }
                    }
                } else {
                    v___x_2306_ =
                        l_Lean_Name_mkStr4(v___x_2195_, v___x_2196_, v___x_2197_, v___x_2207_);
                    v___x_2307_ = crate::leanh::lean_unsigned_to_nat(0);
                    crate::leanh::lean_inc(v___x_2306_);
                    v___x_2308_ = l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(
                        v___x_2306_,
                        v___x_2307_,
                        v_args_2199_,
                        v___y_2200_,
                        v___y_2201_,
                        v___y_2202_,
                        v___y_2203_,
                        v___y_2204_,
                        v___y_2205_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2308_) == 0 {
                        v_isSharedCheck_2319_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2308_)) as u8;
                        if v_isSharedCheck_2319_ == 0 {
                            v_unused_2320_ = crate::leanh::lean_ctor_get(v___x_2308_, 0);
                            crate::leanh::lean_dec(v_unused_2320_);
                            v___x_2310_ = v___x_2308_;
                            v_isShared_2311_ = v_isSharedCheck_2319_;
                            state = 17;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_2308_);
                            v___x_2310_ = crate::leanh::lean_box(0);
                            v_isShared_2311_ = v_isSharedCheck_2319_;
                            state = 17;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_2306_);
                        v_a_2321_ = crate::leanh::lean_ctor_get(v___x_2308_, 0);
                        v_isSharedCheck_2328_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2308_)) as u8;
                        if v_isSharedCheck_2328_ == 0 {
                            v___x_2323_ = v___x_2308_;
                            v_isShared_2324_ = v_isSharedCheck_2328_;
                            state = 19;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2321_);
                            crate::leanh::lean_dec(v___x_2308_);
                            v___x_2323_ = crate::leanh::lean_box(0);
                            v_isShared_2324_ = v_isSharedCheck_2328_;
                            state = 19;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_2228_ = crate::leanh::lean_ctor_get(v_a_2224_, 0);
                v_snd_2229_ = crate::leanh::lean_ctor_get(v_a_2224_, 1);
                v_isSharedCheck_2242_ = (!crate::leanh::lean_is_exclusive(v_a_2224_)) as u8;
                if v_isSharedCheck_2242_ == 0 {
                    v___x_2231_ = v_a_2224_;
                    v_isShared_2232_ = v_isSharedCheck_2242_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2229_);
                    crate::leanh::lean_inc(v_fst_2228_);
                    crate::leanh::lean_dec(v_a_2224_);
                    v___x_2231_ = crate::leanh::lean_box(0);
                    v_isShared_2232_ = v_isSharedCheck_2242_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2233_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2233_, 0, v_fst_2228_);
                v___x_2234_ = l_Lean_Expr_const___override(v___x_2214_, v___x_2217_);
                v___x_2235_ = l_Lean_Expr_app___override(v___x_2234_, v_snd_2229_);
                if v_isShared_2232_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2231_, 1, v___x_2235_);
                    crate::leanh::lean_ctor_set(v___x_2231_, 0, v___x_2233_);
                    v___x_2237_ = v___x_2231_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2241_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2241_, 0, v___x_2233_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2241_, 1, v___x_2235_);
                    v___x_2237_ = v_reuseFailAlloc_2241_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2227_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2226_, 0, v___x_2237_);
                    v___x_2239_ = v___x_2226_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2240_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2240_, 0, v___x_2237_);
                    v___x_2239_ = v_reuseFailAlloc_2240_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2239_;
            }
            5 => {
                if v_isShared_2247_ == 0 {
                    v___x_2249_ = v___x_2246_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2250_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2250_, 0, v_a_2244_);
                    v___x_2249_ = v_reuseFailAlloc_2250_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2249_;
            }
            7 => {
                if v_isShared_2255_ == 0 {
                    v___x_2257_ = v___x_2254_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2258_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2258_, 0, v_a_2252_);
                    v___x_2257_ = v_reuseFailAlloc_2258_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2257_;
            }
            9 => {
                v_fst_2274_ = crate::leanh::lean_ctor_get(v_a_2270_, 0);
                v_snd_2275_ = crate::leanh::lean_ctor_get(v_a_2270_, 1);
                v_isSharedCheck_2288_ = (!crate::leanh::lean_is_exclusive(v_a_2270_)) as u8;
                if v_isSharedCheck_2288_ == 0 {
                    v___x_2277_ = v_a_2270_;
                    v_isShared_2278_ = v_isSharedCheck_2288_;
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2275_);
                    crate::leanh::lean_inc(v_fst_2274_);
                    crate::leanh::lean_dec(v_a_2270_);
                    v___x_2277_ = crate::leanh::lean_box(0);
                    v_isShared_2278_ = v_isSharedCheck_2288_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_2279_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2279_, 0, v_fst_2274_);
                v___x_2280_ = l_Lean_Expr_const___override(v___x_2260_, v___x_2263_);
                v___x_2281_ = l_Lean_Expr_app___override(v___x_2280_, v_snd_2275_);
                if v_isShared_2278_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2277_, 1, v___x_2281_);
                    crate::leanh::lean_ctor_set(v___x_2277_, 0, v___x_2279_);
                    v___x_2283_ = v___x_2277_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2287_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2287_, 0, v___x_2279_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2287_, 1, v___x_2281_);
                    v___x_2283_ = v_reuseFailAlloc_2287_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_2273_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2272_, 0, v___x_2283_);
                    v___x_2285_ = v___x_2272_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2286_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2286_, 0, v___x_2283_);
                    v___x_2285_ = v_reuseFailAlloc_2286_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2285_;
            }
            13 => {
                if v_isShared_2293_ == 0 {
                    v___x_2295_ = v___x_2292_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2296_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2296_, 0, v_a_2290_);
                    v___x_2295_ = v_reuseFailAlloc_2296_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2295_;
            }
            15 => {
                if v_isShared_2301_ == 0 {
                    v___x_2303_ = v___x_2300_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2304_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2304_, 0, v_a_2298_);
                    v___x_2303_ = v_reuseFailAlloc_2304_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2303_;
            }
            17 => {
                v___x_2312_ = crate::leanh::lean_box(0);
                v___x_2313_ = crate::leanh::lean_box(0);
                v___x_2314_ = l_Lean_Expr_const___override(v___x_2306_, v___x_2313_);
                v___x_2315_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2315_, 0, v___x_2312_);
                crate::leanh::lean_ctor_set(v___x_2315_, 1, v___x_2314_);
                if v_isShared_2311_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2310_, 0, v___x_2315_);
                    v___x_2317_ = v___x_2310_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2318_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2318_, 0, v___x_2315_);
                    v___x_2317_ = v_reuseFailAlloc_2318_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_2317_;
            }
            19 => {
                if v_isShared_2324_ == 0 {
                    v___x_2326_ = v___x_2323_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2327_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_a_2321_);
                    v___x_2326_ = v_reuseFailAlloc_2327_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_2326_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___boxed(
    mut v___x_2329_: *mut crate::leanh::LeanObject,
    mut v___x_2330_: *mut crate::leanh::LeanObject,
    mut v___x_2331_: *mut crate::leanh::LeanObject,
    mut v_ctor_2332_: *mut crate::leanh::LeanObject,
    mut v_args_2333_: *mut crate::leanh::LeanObject,
    mut v___y_2334_: *mut crate::leanh::LeanObject,
    mut v___y_2335_: *mut crate::leanh::LeanObject,
    mut v___y_2336_: *mut crate::leanh::LeanObject,
    mut v___y_2337_: *mut crate::leanh::LeanObject,
    mut v___y_2338_: *mut crate::leanh::LeanObject,
    mut v___y_2339_: *mut crate::leanh::LeanObject,
    mut v___y_2340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2341_ = l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0(
        v___x_2329_,
        v___x_2330_,
        v___x_2331_,
        v_ctor_2332_,
        v_args_2333_,
        v___y_2334_,
        v___y_2335_,
        v___y_2336_,
        v___y_2337_,
        v___y_2338_,
        v___y_2339_,
    );
    crate::leanh::lean_dec(v___y_2339_);
    crate::leanh::lean_dec_ref(v___y_2338_);
    crate::leanh::lean_dec(v___y_2337_);
    crate::leanh::lean_dec_ref(v___y_2336_);
    crate::leanh::lean_dec(v___y_2335_);
    crate::leanh::lean_dec_ref(v___y_2334_);
    crate::leanh::lean_dec_ref(v_args_2333_);
    crate::leanh::lean_dec_ref(v_ctor_2332_);
    return v_res_2341_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm(
    mut v_a_2351_: *mut crate::leanh::LeanObject,
    mut v_a_2352_: *mut crate::leanh::LeanObject,
    mut v_a_2353_: *mut crate::leanh::LeanObject,
    mut v_a_2354_: *mut crate::leanh::LeanObject,
    mut v_a_2355_: *mut crate::leanh::LeanObject,
    mut v_a_2356_: *mut crate::leanh::LeanObject,
    mut v_a_2357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2359_ = l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___closed__1;
    v___x_2360_ = l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___closed__2;
    v___x_2361_ = l_Lean_Elab_ConfigEval_EvalTerm_withSimpleEvalStx___redArg(
        v___x_2360_,
        v___f_2359_,
        v_a_2351_,
        v_a_2352_,
        v_a_2353_,
        v_a_2354_,
        v_a_2355_,
        v_a_2356_,
        v_a_2357_,
    );
    return v___x_2361_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___boxed(
    mut v_a_2362_: *mut crate::leanh::LeanObject,
    mut v_a_2363_: *mut crate::leanh::LeanObject,
    mut v_a_2364_: *mut crate::leanh::LeanObject,
    mut v_a_2365_: *mut crate::leanh::LeanObject,
    mut v_a_2366_: *mut crate::leanh::LeanObject,
    mut v_a_2367_: *mut crate::leanh::LeanObject,
    mut v_a_2368_: *mut crate::leanh::LeanObject,
    mut v_a_2369_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2370_ = l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm(
        v_a_2362_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_,
    );
    crate::leanh::lean_dec(v_a_2368_);
    crate::leanh::lean_dec_ref(v_a_2367_);
    crate::leanh::lean_dec(v_a_2366_);
    crate::leanh::lean_dec_ref(v_a_2365_);
    crate::leanh::lean_dec(v_a_2364_);
    crate::leanh::lean_dec_ref(v_a_2363_);
    return v_res_2370_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2372_ = crate::leanh::lean_box(0);
    v___x_2373_ = l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___closed__2;
    v___x_2374_ = l_Lean_Expr_const___override(v___x_2373_, v___x_2372_);
    return v___x_2374_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2375_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__1_once),
        _init_l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__1,
    );
    v___x_2376_ = l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__0;
    v___x_2377_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2377_, 0, v___x_2376_);
    crate::leanh::lean_ctor_set(v___x_2377_, 1, v___x_2375_);
    return v___x_2377_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_instEvalTermOccurrences() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2378_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__2_once),
        _init_l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__2,
    );
    return v___x_2378_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___lam__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2379_ = l_Lean_Elab_ConfigEval_EvalExpr_instNat;
    v___x_2380_ = l_Lean_Elab_ConfigEval_EvalExpr_instList___redArg(v___x_2379_);
    return v___x_2380_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___lam__0(
    mut v_ctor_2381_: *mut crate::leanh::LeanObject,
    mut v_args_2382_: *mut crate::leanh::LeanObject,
    mut v___y_2383_: *mut crate::leanh::LeanObject,
    mut v___y_2384_: *mut crate::leanh::LeanObject,
    mut v___y_2385_: *mut crate::leanh::LeanObject,
    mut v___y_2386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_evalExpr_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2398_: u8 = 0;
    let mut v___x_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2403_: u8 = 0;
    let mut v_a_2404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2407_: u8 = 0;
    let mut v___x_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2411_: u8 = 0;
    let mut v___x_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_evalExpr_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2422_: u8 = 0;
    let mut v___x_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2427_: u8 = 0;
    let mut v_a_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2431_: u8 = 0;
    let mut v___x_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2435_: u8 = 0;
    let mut v___x_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: u8 = 0;
    let mut v___x_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: u8 = 0;
    let mut v___x_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: u8 = 0;
    let mut v___x_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: u8 = 0;
    let mut v___x_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2454_: u8 = 0;
    let mut v___x_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2458_: u8 = 0;
    let mut v___x_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: u8 = 0;
    let mut v___x_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2467_: u8 = 0;
    let mut v___x_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2471_: u8 = 0;
    let mut v___x_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: u8 = 0;
    let mut v___x_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2480_: u8 = 0;
    let mut v___x_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2484_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2439_ =
                    l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__0;
                v___x_2440_ = lean_string_dec_eq(v_ctor_2381_, v___x_2439_);
                if v___x_2440_ == 0 {
                    v___x_2441_ = l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__0;
                    v___x_2442_ = lean_string_dec_eq(v_ctor_2381_, v___x_2441_);
                    if v___x_2442_ == 0 {
                        v___x_2443_ = l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__1;
                        v___x_2444_ = lean_string_dec_eq(v_ctor_2381_, v___x_2443_);
                        if v___x_2444_ == 0 {
                            v___x_2445_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___redArg();
                            return v___x_2445_;
                        } else {
                            v___x_2446_ = lean_array_get_size(v_args_2382_);
                            v___x_2447_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_2448_ = lean_nat_dec_eq(v___x_2446_, v___x_2447_);
                            if v___x_2448_ == 0 {
                                v___x_2449_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once), _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
                                v___x_2450_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_2449_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
                                v_a_2451_ = crate::leanh::lean_ctor_get(v___x_2450_, 0);
                                v_isSharedCheck_2458_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2450_)) as u8;
                                if v_isSharedCheck_2458_ == 0 {
                                    v___x_2453_ = v___x_2450_;
                                    v_isShared_2454_ = v_isSharedCheck_2458_;
                                    state = 12;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2451_);
                                    crate::leanh::lean_dec(v___x_2450_);
                                    v___x_2453_ = crate::leanh::lean_box(0);
                                    v_isShared_2454_ = v_isSharedCheck_2458_;
                                    state = 12;
                                    continue;
                                }
                            } else {
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        v___x_2459_ = lean_array_get_size(v_args_2382_);
                        v___x_2460_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2461_ = lean_nat_dec_eq(v___x_2459_, v___x_2460_);
                        if v___x_2461_ == 0 {
                            v___x_2462_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once), _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
                            v___x_2463_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_2462_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
                            v_a_2464_ = crate::leanh::lean_ctor_get(v___x_2463_, 0);
                            v_isSharedCheck_2471_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2463_)) as u8;
                            if v_isSharedCheck_2471_ == 0 {
                                v___x_2466_ = v___x_2463_;
                                v_isShared_2467_ = v_isSharedCheck_2471_;
                                state = 14;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2464_);
                                crate::leanh::lean_dec(v___x_2463_);
                                v___x_2466_ = crate::leanh::lean_box(0);
                                v_isShared_2467_ = v_isSharedCheck_2471_;
                                state = 14;
                                continue;
                            }
                        } else {
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    v___x_2472_ = lean_array_get_size(v_args_2382_);
                    v___x_2473_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2474_ = lean_nat_dec_eq(v___x_2472_, v___x_2473_);
                    if v___x_2474_ == 0 {
                        v___x_2475_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once), _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
                        v___x_2476_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_2475_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
                        v_a_2477_ = crate::leanh::lean_ctor_get(v___x_2476_, 0);
                        v_isSharedCheck_2484_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2476_)) as u8;
                        if v_isSharedCheck_2484_ == 0 {
                            v___x_2479_ = v___x_2476_;
                            v_isShared_2480_ = v_isSharedCheck_2484_;
                            state = 16;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2477_);
                            crate::leanh::lean_dec(v___x_2476_);
                            v___x_2479_ = crate::leanh::lean_box(0);
                            v_isShared_2480_ = v_isSharedCheck_2484_;
                            state = 16;
                            continue;
                        }
                    } else {
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2389_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___lam__0___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___lam__0___closed__0_once), _init_l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___lam__0___closed__0);
                v_evalExpr_2390_ = crate::leanh::lean_ctor_get(v___x_2389_, 0);
                v___x_2391_ = l_Lean_instInhabitedExpr;
                v___x_2392_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2393_ = lean_array_get_borrowed(v___x_2391_, v_args_2382_, v___x_2392_);
                crate::leanh::lean_inc_ref(v_evalExpr_2390_);
                crate::leanh::lean_inc(v___y_2386_);
                crate::leanh::lean_inc_ref(v___y_2385_);
                crate::leanh::lean_inc(v___y_2384_);
                crate::leanh::lean_inc_ref(v___y_2383_);
                crate::leanh::lean_inc(v___x_2393_);
                v___x_2394_ = crate::leanh::lean_apply_6(
                    v_evalExpr_2390_,
                    v___x_2393_,
                    v___y_2383_,
                    v___y_2384_,
                    v___y_2385_,
                    v___y_2386_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_2394_) == 0 {
                    v_a_2395_ = crate::leanh::lean_ctor_get(v___x_2394_, 0);
                    v_isSharedCheck_2403_ = (!crate::leanh::lean_is_exclusive(v___x_2394_)) as u8;
                    if v_isSharedCheck_2403_ == 0 {
                        v___x_2397_ = v___x_2394_;
                        v_isShared_2398_ = v_isSharedCheck_2403_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2395_);
                        crate::leanh::lean_dec(v___x_2394_);
                        v___x_2397_ = crate::leanh::lean_box(0);
                        v_isShared_2398_ = v_isSharedCheck_2403_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_2404_ = crate::leanh::lean_ctor_get(v___x_2394_, 0);
                    v_isSharedCheck_2411_ = (!crate::leanh::lean_is_exclusive(v___x_2394_)) as u8;
                    if v_isSharedCheck_2411_ == 0 {
                        v___x_2406_ = v___x_2394_;
                        v_isShared_2407_ = v_isSharedCheck_2411_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2404_);
                        crate::leanh::lean_dec(v___x_2394_);
                        v___x_2406_ = crate::leanh::lean_box(0);
                        v_isShared_2407_ = v_isSharedCheck_2411_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2399_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2399_, 0, v_a_2395_);
                if v_isShared_2398_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2397_, 0, v___x_2399_);
                    v___x_2401_ = v___x_2397_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2402_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2402_, 0, v___x_2399_);
                    v___x_2401_ = v_reuseFailAlloc_2402_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2401_;
            }
            4 => {
                if v_isShared_2407_ == 0 {
                    v___x_2409_ = v___x_2406_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2410_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2410_, 0, v_a_2404_);
                    v___x_2409_ = v_reuseFailAlloc_2410_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2409_;
            }
            6 => {
                v___x_2413_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___lam__0___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___lam__0___closed__0_once), _init_l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___lam__0___closed__0);
                v_evalExpr_2414_ = crate::leanh::lean_ctor_get(v___x_2413_, 0);
                v___x_2415_ = l_Lean_instInhabitedExpr;
                v___x_2416_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2417_ = lean_array_get_borrowed(v___x_2415_, v_args_2382_, v___x_2416_);
                crate::leanh::lean_inc_ref(v_evalExpr_2414_);
                crate::leanh::lean_inc(v___y_2386_);
                crate::leanh::lean_inc_ref(v___y_2385_);
                crate::leanh::lean_inc(v___y_2384_);
                crate::leanh::lean_inc_ref(v___y_2383_);
                crate::leanh::lean_inc(v___x_2417_);
                v___x_2418_ = crate::leanh::lean_apply_6(
                    v_evalExpr_2414_,
                    v___x_2417_,
                    v___y_2383_,
                    v___y_2384_,
                    v___y_2385_,
                    v___y_2386_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_2418_) == 0 {
                    v_a_2419_ = crate::leanh::lean_ctor_get(v___x_2418_, 0);
                    v_isSharedCheck_2427_ = (!crate::leanh::lean_is_exclusive(v___x_2418_)) as u8;
                    if v_isSharedCheck_2427_ == 0 {
                        v___x_2421_ = v___x_2418_;
                        v_isShared_2422_ = v_isSharedCheck_2427_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2419_);
                        crate::leanh::lean_dec(v___x_2418_);
                        v___x_2421_ = crate::leanh::lean_box(0);
                        v_isShared_2422_ = v_isSharedCheck_2427_;
                        state = 7;
                        continue;
                    }
                } else {
                    v_a_2428_ = crate::leanh::lean_ctor_get(v___x_2418_, 0);
                    v_isSharedCheck_2435_ = (!crate::leanh::lean_is_exclusive(v___x_2418_)) as u8;
                    if v_isSharedCheck_2435_ == 0 {
                        v___x_2430_ = v___x_2418_;
                        v_isShared_2431_ = v_isSharedCheck_2435_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2428_);
                        crate::leanh::lean_dec(v___x_2418_);
                        v___x_2430_ = crate::leanh::lean_box(0);
                        v_isShared_2431_ = v_isSharedCheck_2435_;
                        state = 9;
                        continue;
                    }
                }
            }
            7 => {
                v___x_2423_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2423_, 0, v_a_2419_);
                if v_isShared_2422_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2421_, 0, v___x_2423_);
                    v___x_2425_ = v___x_2421_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2426_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2426_, 0, v___x_2423_);
                    v___x_2425_ = v_reuseFailAlloc_2426_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2425_;
            }
            9 => {
                if v_isShared_2431_ == 0 {
                    v___x_2433_ = v___x_2430_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2434_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2434_, 0, v_a_2428_);
                    v___x_2433_ = v_reuseFailAlloc_2434_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2433_;
            }
            11 => {
                v___x_2437_ = crate::leanh::lean_box(0);
                v___x_2438_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2438_, 0, v___x_2437_);
                return v___x_2438_;
            }
            12 => {
                if v_isShared_2454_ == 0 {
                    v___x_2456_ = v___x_2453_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2457_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_a_2451_);
                    v___x_2456_ = v_reuseFailAlloc_2457_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2456_;
            }
            14 => {
                if v_isShared_2467_ == 0 {
                    v___x_2469_ = v___x_2466_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2470_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2470_, 0, v_a_2464_);
                    v___x_2469_ = v_reuseFailAlloc_2470_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2469_;
            }
            16 => {
                if v_isShared_2480_ == 0 {
                    v___x_2482_ = v___x_2479_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_2483_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_a_2477_);
                    v___x_2482_ = v_reuseFailAlloc_2483_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_2482_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___lam__0___boxed(
    mut v_ctor_2485_: *mut crate::leanh::LeanObject,
    mut v_args_2486_: *mut crate::leanh::LeanObject,
    mut v___y_2487_: *mut crate::leanh::LeanObject,
    mut v___y_2488_: *mut crate::leanh::LeanObject,
    mut v___y_2489_: *mut crate::leanh::LeanObject,
    mut v___y_2490_: *mut crate::leanh::LeanObject,
    mut v___y_2491_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2492_ = l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___lam__0(
        v_ctor_2485_,
        v_args_2486_,
        v___y_2487_,
        v___y_2488_,
        v___y_2489_,
        v___y_2490_,
    );
    crate::leanh::lean_dec(v___y_2490_);
    crate::leanh::lean_dec_ref(v___y_2489_);
    crate::leanh::lean_dec(v___y_2488_);
    crate::leanh::lean_dec_ref(v___y_2487_);
    crate::leanh::lean_dec_ref(v_args_2486_);
    crate::leanh::lean_dec_ref(v_ctor_2485_);
    return v_res_2492_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr(
    mut v_a_2494_: *mut crate::leanh::LeanObject,
    mut v_a_2495_: *mut crate::leanh::LeanObject,
    mut v_a_2496_: *mut crate::leanh::LeanObject,
    mut v_a_2497_: *mut crate::leanh::LeanObject,
    mut v_a_2498_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2500_ = l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___closed__0;
    v___x_2501_ = l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___closed__2;
    v___x_2502_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(
        v___x_2501_,
        v___f_2500_,
        v_a_2494_,
        v_a_2495_,
        v_a_2496_,
        v_a_2497_,
        v_a_2498_,
    );
    return v___x_2502_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___boxed(
    mut v_a_2503_: *mut crate::leanh::LeanObject,
    mut v_a_2504_: *mut crate::leanh::LeanObject,
    mut v_a_2505_: *mut crate::leanh::LeanObject,
    mut v_a_2506_: *mut crate::leanh::LeanObject,
    mut v_a_2507_: *mut crate::leanh::LeanObject,
    mut v_a_2508_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2509_ = l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr(
        v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_,
    );
    crate::leanh::lean_dec(v_a_2507_);
    crate::leanh::lean_dec_ref(v_a_2506_);
    crate::leanh::lean_dec(v_a_2505_);
    crate::leanh::lean_dec_ref(v_a_2504_);
    return v_res_2509_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2511_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__1_once),
        _init_l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__1,
    );
    v___x_2512_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2512_, 0, v___x_2511_);
    return v___x_2512_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2513_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__1_once),
        _init_l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__1,
    );
    v___x_2514_ = l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__0;
    v___x_2515_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2515_, 0, v___x_2514_);
    crate::leanh::lean_ctor_set(v___x_2515_, 1, v___x_2513_);
    return v___x_2515_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_instEvalExprOccurrences() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2516_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__2_once),
        _init_l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__2,
    );
    return v___x_2516_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_ConfigEval_MetaInstances(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_ConfigEval_Commands(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_ConfigEval_Instances(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_ConfigEval_DeriveEvalTerm(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_ConfigEval_DeriveEvalExpr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals =
        _init_l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals();
    crate::leanh::lean_mark_persistent(l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals);
    l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals =
        _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals();
    crate::leanh::lean_mark_persistent(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals);
    l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode =
        _init_l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode();
    crate::leanh::lean_mark_persistent(l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode);
    l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode =
        _init_l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode();
    crate::leanh::lean_mark_persistent(l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode);
    l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode =
        _init_l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode();
    crate::leanh::lean_mark_persistent(l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode);
    l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode =
        _init_l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode();
    crate::leanh::lean_mark_persistent(l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode);
    l_Lean_Elab_ConfigEval_instEvalTermOccurrences =
        _init_l_Lean_Elab_ConfigEval_instEvalTermOccurrences();
    crate::leanh::lean_mark_persistent(l_Lean_Elab_ConfigEval_instEvalTermOccurrences);
    l_Lean_Elab_ConfigEval_instEvalExprOccurrences =
        _init_l_Lean_Elab_ConfigEval_instEvalExprOccurrences();
    crate::leanh::lean_mark_persistent(l_Lean_Elab_ConfigEval_instEvalExprOccurrences);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_ConfigEval_MetaInstances(
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
pub unsafe fn initialize_Lean_Elab_ConfigEval_MetaInstances(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_ConfigEval_Commands(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_ConfigEval_Instances(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_ConfigEval_DeriveEvalTerm(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_ConfigEval_DeriveEvalExpr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_ConfigEval_MetaInstances(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_ConfigEval_MetaInstances(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_ConfigEval_MetaInstances(builtin);
}
