// Lean compiler output
// Module: Lean.Elab.ConfigEval.MetaInstances
// Imports: Lean.Elab.ConfigEval.Commands Lean.Elab.ConfigEval.Instances Lean.Elab.ConfigEval.DeriveEvalTerm Lean.Elab.ConfigEval.DeriveEvalExpr
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr3, l_Lean_Name_mkStr4};
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
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_borrowed, lean_array_get_size, lean_nat_dec_eq, lean_string_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_6, lean_box, lean_ctor_get,
    lean_ctor_set, lean_ctor_set_tag, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc,
    lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_unsigned_to_nat,
};
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__0_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__1_value:
    LeanStringObject<18> = LeanStringObject {
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
        110, 111, 110, 68, 101, 112, 101, 110, 100, 101, 110, 116, 70, 105, 114, 115, 116, 0,
    ],
};
static mut l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__1_value
) as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__2_value:
    LeanStringObject<17> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0___closed__2_value
) as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__0_value:
    LeanStringObject<5> = LeanStringObject {
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
static mut l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__1_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__2_value:
    LeanStringObject<14> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__3_value:
    LeanClosureObject<3> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 3) as u16,
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
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__1_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__2_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__3_value)
        as *mut LeanObject;
static l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__4_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__4_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
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
            l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__4_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__1_value
        ) as *mut LeanObject,
        15449383196166861506 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__4_value:
    LeanCtorObject<3> = LeanCtorObject {
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
            l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__4_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__2_value
        ) as *mut LeanObject,
        1913141712249469064 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__0_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___boxed
        as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__0_value:
    LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__0_value
) as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___closed__0_value:
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
    m_fun: l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals___closed__0_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___boxed
        as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___lam__0___closed__0_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___lam__0___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___lam__0___closed__1_value:
    LeanStringObject<11> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___lam__0___closed__1_value
) as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___closed__0_value:
    LeanStringObject<14> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___closed__1_value:
    LeanClosureObject<3> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 3) as u16,
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
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__1_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___closed__0_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___closed__1_value)
        as *mut LeanObject;
static l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___closed__2_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___closed__2_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
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
            l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___closed__2_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__1_value
        ) as *mut LeanObject,
        15449383196166861506 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___closed__2_value:
    LeanCtorObject<3> = LeanCtorObject {
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
            l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___closed__2_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___closed__0_value
        ) as *mut LeanObject,
        10917271421258176470 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__0_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___boxed
        as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode_evalExpr___closed__0_value:
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
    m_fun: l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode_evalExpr___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode_evalExpr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode_evalExpr___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode___closed__0_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode_evalExpr___boxed
        as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__0_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [100, 101, 102, 97, 117, 108, 116, 0]};
static mut l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__1_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [105, 110, 115, 116, 97, 110, 99, 101, 115, 0]};
static mut l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__1_value
) as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__2_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [114, 101, 100, 117, 99, 105, 98, 108, 101, 0]};
static mut l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0___closed__2_value
) as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___closed__0_value:
    LeanStringObject<17> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___closed__1_value:
    LeanClosureObject<3> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 3) as u16,
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
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__1_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___closed__0_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___closed__1_value
) as *mut LeanObject;
static l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___closed__2_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___closed__2_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
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
            l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___closed__2_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__1_value
        ) as *mut LeanObject,
        15449383196166861506 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___closed__2_value:
    LeanCtorObject<3> = LeanCtorObject {
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
            l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___closed__2_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___closed__0_value
        ) as *mut LeanObject,
        7920553410559161077 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___closed__2_value
) as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__0_value:
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
    m_fun: l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___boxed
        as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr___closed__0_value:
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
    m_fun: l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__0_value:
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
    m_fun: l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr___boxed
        as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__0_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__1_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__1_value
) as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__2_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__2_value
) as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__3_value:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__2_value
        ) as *mut LeanObject,
        11442535297760353691 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__3_value
) as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__4_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__4:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__5_value:
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
    m_fun: l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___boxed as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__5_value
) as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___closed__0_value:
    LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___closed__1_value:
    LeanClosureObject<3> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 3) as u16,
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
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__1_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___closed__0_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___closed__1_value)
        as *mut LeanObject;
static l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___closed__2_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___closed__2_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
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
            l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___closed__2_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__1_value
        ) as *mut LeanObject,
        15449383196166861506 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___closed__2_value:
    LeanCtorObject<3> = LeanCtorObject {
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
            l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___closed__2_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___closed__0_value
        ) as *mut LeanObject,
        10189614426786410228 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___boxed
            as *const core::ffi::c_void,
        m_arity: 8,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_ConfigEval_instEvalTermOccurrences: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___lam__0___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___lam__0___closed__0:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___closed__0_value:
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
    m_fun: l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___boxed
            as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_ConfigEval_instEvalExprOccurrences: *mut LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_1259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut LeanObject = core::ptr::null_mut();
    v___x_1259_ = lean_box(0);
    v___x_1260_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_1261_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1261_, 0, v___x_1260_);
    lean_ctor_set(v___x_1261_, 1, v___x_1259_);
    return v___x_1261_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___redArg()
-> *mut LeanObject {
    let mut v___x_1263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut LeanObject = core::ptr::null_mut();
    v___x_1263_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___redArg___closed__0);
    v___x_1264_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1264_, 0, v___x_1263_);
    return v___x_1264_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___redArg___boxed(
    mut v___y_1265_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1266_: *mut LeanObject = core::ptr::null_mut();
    v_res_1266_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___redArg();
    return v_res_1266_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0(
    mut v_00_u03b1_1267_: *mut LeanObject,
    mut v___y_1268_: *mut LeanObject,
    mut v___y_1269_: *mut LeanObject,
    mut v___y_1270_: *mut LeanObject,
    mut v___y_1271_: *mut LeanObject,
    mut v___y_1272_: *mut LeanObject,
    mut v___y_1273_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1275_: *mut LeanObject = core::ptr::null_mut();
    v___x_1275_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___redArg();
    return v___x_1275_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___boxed(
    mut v_00_u03b1_1276_: *mut LeanObject,
    mut v___y_1277_: *mut LeanObject,
    mut v___y_1278_: *mut LeanObject,
    mut v___y_1279_: *mut LeanObject,
    mut v___y_1280_: *mut LeanObject,
    mut v___y_1281_: *mut LeanObject,
    mut v___y_1282_: *mut LeanObject,
    mut v___y_1283_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1284_: *mut LeanObject = core::ptr::null_mut();
    v_res_1284_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0(v_00_u03b1_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_);
    lean_dec(v___y_1282_);
    lean_dec_ref(v___y_1281_);
    lean_dec(v___y_1280_);
    lean_dec_ref(v___y_1279_);
    lean_dec(v___y_1278_);
    lean_dec_ref(v___y_1277_);
    return v_res_1284_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___lam__0(
    mut v___x_1288_: *mut LeanObject,
    mut v___x_1289_: *mut LeanObject,
    mut v___x_1290_: *mut LeanObject,
    mut v_ctor_1291_: *mut LeanObject,
    mut v_args_1292_: *mut LeanObject,
    mut v___y_1293_: *mut LeanObject,
    mut v___y_1294_: *mut LeanObject,
    mut v___y_1295_: *mut LeanObject,
    mut v___y_1296_: *mut LeanObject,
    mut v___y_1297_: *mut LeanObject,
    mut v___y_1298_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: u8 = 0;
    let mut v___x_1302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: u8 = 0;
    let mut v___x_1304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: u8 = 0;
    let mut v___x_1306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1312_: u8 = 0;
    let mut v___x_1313_: u8 = 0;
    let mut v___x_1314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1321_: u8 = 0;
    let mut v_unused_1322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1326_: u8 = 0;
    let mut v___x_1328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1330_: u8 = 0;
    let mut v___x_1331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1336_: u8 = 0;
    let mut v___x_1337_: u8 = 0;
    let mut v___x_1338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1345_: u8 = 0;
    let mut v_unused_1346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1350_: u8 = 0;
    let mut v___x_1352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1354_: u8 = 0;
    let mut v___x_1355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1360_: u8 = 0;
    let mut v___x_1361_: u8 = 0;
    let mut v___x_1362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1369_: u8 = 0;
    let mut v_unused_1370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1374_: u8 = 0;
    let mut v___x_1376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1377_: *mut LeanObject = core::ptr::null_mut();
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
                            lean_dec_ref(v___x_1290_);
                            lean_dec_ref(v___x_1289_);
                            lean_dec_ref(v___x_1288_);
                            v___x_1306_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___redArg();
                            return v___x_1306_;
                        } else {
                            v___x_1307_ = l_Lean_Name_mkStr4(
                                v___x_1288_,
                                v___x_1289_,
                                v___x_1290_,
                                v___x_1304_,
                            );
                            v___x_1308_ = lean_unsigned_to_nat(0);
                            lean_inc(v___x_1307_);
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
                            if lean_obj_tag(v___x_1309_) == 0 {
                                v_isSharedCheck_1321_ = (!lean_is_exclusive(v___x_1309_)) as u8;
                                if v_isSharedCheck_1321_ == 0 {
                                    v_unused_1322_ = lean_ctor_get(v___x_1309_, 0);
                                    lean_dec(v_unused_1322_);
                                    v___x_1311_ = v___x_1309_;
                                    v_isShared_1312_ = v_isSharedCheck_1321_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_dec(v___x_1309_);
                                    v___x_1311_ = lean_box(0);
                                    v_isShared_1312_ = v_isSharedCheck_1321_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec(v___x_1307_);
                                v_a_1323_ = lean_ctor_get(v___x_1309_, 0);
                                v_isSharedCheck_1330_ = (!lean_is_exclusive(v___x_1309_)) as u8;
                                if v_isSharedCheck_1330_ == 0 {
                                    v___x_1325_ = v___x_1309_;
                                    v_isShared_1326_ = v_isSharedCheck_1330_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_inc(v_a_1323_);
                                    lean_dec(v___x_1309_);
                                    v___x_1325_ = lean_box(0);
                                    v_isShared_1326_ = v_isSharedCheck_1330_;
                                    state = 3;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v___x_1331_ =
                            l_Lean_Name_mkStr4(v___x_1288_, v___x_1289_, v___x_1290_, v___x_1302_);
                        v___x_1332_ = lean_unsigned_to_nat(0);
                        lean_inc(v___x_1331_);
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
                        if lean_obj_tag(v___x_1333_) == 0 {
                            v_isSharedCheck_1345_ = (!lean_is_exclusive(v___x_1333_)) as u8;
                            if v_isSharedCheck_1345_ == 0 {
                                v_unused_1346_ = lean_ctor_get(v___x_1333_, 0);
                                lean_dec(v_unused_1346_);
                                v___x_1335_ = v___x_1333_;
                                v_isShared_1336_ = v_isSharedCheck_1345_;
                                state = 5;
                                continue;
                            } else {
                                lean_dec(v___x_1333_);
                                v___x_1335_ = lean_box(0);
                                v_isShared_1336_ = v_isSharedCheck_1345_;
                                state = 5;
                                continue;
                            }
                        } else {
                            lean_dec(v___x_1331_);
                            v_a_1347_ = lean_ctor_get(v___x_1333_, 0);
                            v_isSharedCheck_1354_ = (!lean_is_exclusive(v___x_1333_)) as u8;
                            if v_isSharedCheck_1354_ == 0 {
                                v___x_1349_ = v___x_1333_;
                                v_isShared_1350_ = v_isSharedCheck_1354_;
                                state = 7;
                                continue;
                            } else {
                                lean_inc(v_a_1347_);
                                lean_dec(v___x_1333_);
                                v___x_1349_ = lean_box(0);
                                v_isShared_1350_ = v_isSharedCheck_1354_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                } else {
                    v___x_1355_ =
                        l_Lean_Name_mkStr4(v___x_1288_, v___x_1289_, v___x_1290_, v___x_1300_);
                    v___x_1356_ = lean_unsigned_to_nat(0);
                    lean_inc(v___x_1355_);
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
                    if lean_obj_tag(v___x_1357_) == 0 {
                        v_isSharedCheck_1369_ = (!lean_is_exclusive(v___x_1357_)) as u8;
                        if v_isSharedCheck_1369_ == 0 {
                            v_unused_1370_ = lean_ctor_get(v___x_1357_, 0);
                            lean_dec(v_unused_1370_);
                            v___x_1359_ = v___x_1357_;
                            v_isShared_1360_ = v_isSharedCheck_1369_;
                            state = 9;
                            continue;
                        } else {
                            lean_dec(v___x_1357_);
                            v___x_1359_ = lean_box(0);
                            v_isShared_1360_ = v_isSharedCheck_1369_;
                            state = 9;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_1355_);
                        v_a_1371_ = lean_ctor_get(v___x_1357_, 0);
                        v_isSharedCheck_1378_ = (!lean_is_exclusive(v___x_1357_)) as u8;
                        if v_isSharedCheck_1378_ == 0 {
                            v___x_1373_ = v___x_1357_;
                            v_isShared_1374_ = v_isSharedCheck_1378_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_a_1371_);
                            lean_dec(v___x_1357_);
                            v___x_1373_ = lean_box(0);
                            v_isShared_1374_ = v_isSharedCheck_1378_;
                            state = 11;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1313_ = 1;
                v___x_1314_ = lean_box(0);
                v___x_1315_ = l_Lean_Expr_const___override(v___x_1307_, v___x_1314_);
                v___x_1316_ = lean_box((v___x_1313_) as usize);
                v___x_1317_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1317_, 0, v___x_1316_);
                lean_ctor_set(v___x_1317_, 1, v___x_1315_);
                if v_isShared_1312_ == 0 {
                    lean_ctor_set(v___x_1311_, 0, v___x_1317_);
                    v___x_1319_ = v___x_1311_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1320_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1320_, 0, v___x_1317_);
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
                    v_reuseFailAlloc_1329_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1329_, 0, v_a_1323_);
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
                v___x_1338_ = lean_box(0);
                v___x_1339_ = l_Lean_Expr_const___override(v___x_1331_, v___x_1338_);
                v___x_1340_ = lean_box((v___x_1337_) as usize);
                v___x_1341_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1341_, 0, v___x_1340_);
                lean_ctor_set(v___x_1341_, 1, v___x_1339_);
                if v_isShared_1336_ == 0 {
                    lean_ctor_set(v___x_1335_, 0, v___x_1341_);
                    v___x_1343_ = v___x_1335_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1344_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1344_, 0, v___x_1341_);
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
                    v_reuseFailAlloc_1353_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1353_, 0, v_a_1347_);
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
                v___x_1362_ = lean_box(0);
                v___x_1363_ = l_Lean_Expr_const___override(v___x_1355_, v___x_1362_);
                v___x_1364_ = lean_box((v___x_1361_) as usize);
                v___x_1365_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1365_, 0, v___x_1364_);
                lean_ctor_set(v___x_1365_, 1, v___x_1363_);
                if v_isShared_1360_ == 0 {
                    lean_ctor_set(v___x_1359_, 0, v___x_1365_);
                    v___x_1367_ = v___x_1359_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1368_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1368_, 0, v___x_1365_);
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
                    v_reuseFailAlloc_1377_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_a_1371_);
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
    mut v___x_1379_: *mut LeanObject,
    mut v___x_1380_: *mut LeanObject,
    mut v___x_1381_: *mut LeanObject,
    mut v_ctor_1382_: *mut LeanObject,
    mut v_args_1383_: *mut LeanObject,
    mut v___y_1384_: *mut LeanObject,
    mut v___y_1385_: *mut LeanObject,
    mut v___y_1386_: *mut LeanObject,
    mut v___y_1387_: *mut LeanObject,
    mut v___y_1388_: *mut LeanObject,
    mut v___y_1389_: *mut LeanObject,
    mut v___y_1390_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1391_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_1389_);
    lean_dec_ref(v___y_1388_);
    lean_dec(v___y_1387_);
    lean_dec_ref(v___y_1386_);
    lean_dec(v___y_1385_);
    lean_dec_ref(v___y_1384_);
    lean_dec_ref(v_args_1383_);
    lean_dec_ref(v_ctor_1382_);
    return v_res_1391_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm(
    mut v_a_1403_: *mut LeanObject,
    mut v_a_1404_: *mut LeanObject,
    mut v_a_1405_: *mut LeanObject,
    mut v_a_1406_: *mut LeanObject,
    mut v_a_1407_: *mut LeanObject,
    mut v_a_1408_: *mut LeanObject,
    mut v_a_1409_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_1414_: *mut LeanObject,
    mut v_a_1415_: *mut LeanObject,
    mut v_a_1416_: *mut LeanObject,
    mut v_a_1417_: *mut LeanObject,
    mut v_a_1418_: *mut LeanObject,
    mut v_a_1419_: *mut LeanObject,
    mut v_a_1420_: *mut LeanObject,
    mut v_a_1421_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1422_: *mut LeanObject = core::ptr::null_mut();
    v_res_1422_ = l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm(
        v_a_1414_, v_a_1415_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_,
    );
    lean_dec(v_a_1420_);
    lean_dec_ref(v_a_1419_);
    lean_dec(v_a_1418_);
    lean_dec_ref(v_a_1417_);
    lean_dec(v_a_1416_);
    lean_dec_ref(v_a_1415_);
    return v_res_1422_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__1() -> *mut LeanObject
{
    let mut v___x_1424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut LeanObject = core::ptr::null_mut();
    v___x_1424_ = lean_box(0);
    v___x_1425_ = l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm___closed__4;
    v___x_1426_ = l_Lean_Expr_const___override(v___x_1425_, v___x_1424_);
    return v___x_1426_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__2() -> *mut LeanObject
{
    let mut v___x_1427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut LeanObject = core::ptr::null_mut();
    v___x_1427_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__1_once),
        _init_l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__1,
    );
    v___x_1428_ = l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__0;
    v___x_1429_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1429_, 0, v___x_1428_);
    lean_ctor_set(v___x_1429_, 1, v___x_1427_);
    return v___x_1429_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals() -> *mut LeanObject {
    let mut v___x_1430_: *mut LeanObject = core::ptr::null_mut();
    v___x_1430_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__2_once),
        _init_l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__2,
    );
    return v___x_1430_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_1431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut LeanObject = core::ptr::null_mut();
    v___x_1431_ = lean_box(0);
    v___x_1432_ = l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
    v___x_1433_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1433_, 0, v___x_1432_);
    lean_ctor_set(v___x_1433_, 1, v___x_1431_);
    return v___x_1433_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___redArg()
-> *mut LeanObject {
    let mut v___x_1435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut LeanObject = core::ptr::null_mut();
    v___x_1435_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___redArg___closed__0);
    v___x_1436_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1436_, 0, v___x_1435_);
    return v___x_1436_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___redArg___boxed(
    mut v___y_1437_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1438_: *mut LeanObject = core::ptr::null_mut();
    v_res_1438_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___redArg();
    return v_res_1438_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0(
    mut v_00_u03b1_1439_: *mut LeanObject,
    mut v___y_1440_: *mut LeanObject,
    mut v___y_1441_: *mut LeanObject,
    mut v___y_1442_: *mut LeanObject,
    mut v___y_1443_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1445_: *mut LeanObject = core::ptr::null_mut();
    v___x_1445_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___redArg();
    return v___x_1445_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0___boxed(
    mut v_00_u03b1_1446_: *mut LeanObject,
    mut v___y_1447_: *mut LeanObject,
    mut v___y_1448_: *mut LeanObject,
    mut v___y_1449_: *mut LeanObject,
    mut v___y_1450_: *mut LeanObject,
    mut v___y_1451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1452_: *mut LeanObject = core::ptr::null_mut();
    v_res_1452_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__0(v_00_u03b1_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
    lean_dec(v___y_1450_);
    lean_dec_ref(v___y_1449_);
    lean_dec(v___y_1448_);
    lean_dec_ref(v___y_1447_);
    return v_res_1452_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1_spec__1(
    mut v_msgData_1453_: *mut LeanObject,
    mut v___y_1454_: *mut LeanObject,
    mut v___y_1455_: *mut LeanObject,
    mut v___y_1456_: *mut LeanObject,
    mut v___y_1457_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_1463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut LeanObject = core::ptr::null_mut();
    v___x_1459_ = lean_st_ref_get(v___y_1457_);
    v_env_1460_ = lean_ctor_get(v___x_1459_, 0);
    lean_inc_ref(v_env_1460_);
    lean_dec(v___x_1459_);
    v___x_1461_ = lean_st_ref_get(v___y_1455_);
    v_mctx_1462_ = lean_ctor_get(v___x_1461_, 0);
    lean_inc_ref(v_mctx_1462_);
    lean_dec(v___x_1461_);
    v_lctx_1463_ = lean_ctor_get(v___y_1454_, 2);
    v_options_1464_ = lean_ctor_get(v___y_1456_, 2);
    lean_inc_ref(v_options_1464_);
    lean_inc_ref(v_lctx_1463_);
    v___x_1465_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1465_, 0, v_env_1460_);
    lean_ctor_set(v___x_1465_, 1, v_mctx_1462_);
    lean_ctor_set(v___x_1465_, 2, v_lctx_1463_);
    lean_ctor_set(v___x_1465_, 3, v_options_1464_);
    v___x_1466_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1466_, 0, v___x_1465_);
    lean_ctor_set(v___x_1466_, 1, v_msgData_1453_);
    v___x_1467_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1467_, 0, v___x_1466_);
    return v___x_1467_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1_spec__1___boxed(
    mut v_msgData_1468_: *mut LeanObject,
    mut v___y_1469_: *mut LeanObject,
    mut v___y_1470_: *mut LeanObject,
    mut v___y_1471_: *mut LeanObject,
    mut v___y_1472_: *mut LeanObject,
    mut v___y_1473_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1474_: *mut LeanObject = core::ptr::null_mut();
    v_res_1474_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1_spec__1(v_msgData_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_);
    lean_dec(v___y_1472_);
    lean_dec_ref(v___y_1471_);
    lean_dec(v___y_1470_);
    lean_dec_ref(v___y_1469_);
    return v_res_1474_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(
    mut v_msg_1475_: *mut LeanObject,
    mut v___y_1476_: *mut LeanObject,
    mut v___y_1477_: *mut LeanObject,
    mut v___y_1478_: *mut LeanObject,
    mut v___y_1479_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1486_: u8 = 0;
    let mut v___x_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1491_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1481_ = lean_ctor_get(v___y_1478_, 5);
                v___x_1482_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1_spec__1(v_msg_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
                v_a_1483_ = lean_ctor_get(v___x_1482_, 0);
                v_isSharedCheck_1491_ = (!lean_is_exclusive(v___x_1482_)) as u8;
                if v_isSharedCheck_1491_ == 0 {
                    v___x_1485_ = v___x_1482_;
                    v_isShared_1486_ = v_isSharedCheck_1491_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1483_);
                    lean_dec(v___x_1482_);
                    v___x_1485_ = lean_box(0);
                    v_isShared_1486_ = v_isSharedCheck_1491_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_1481_);
                v___x_1487_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1487_, 0, v_ref_1481_);
                lean_ctor_set(v___x_1487_, 1, v_a_1483_);
                if v_isShared_1486_ == 0 {
                    lean_ctor_set_tag(v___x_1485_, 1);
                    lean_ctor_set(v___x_1485_, 0, v___x_1487_);
                    v___x_1489_ = v___x_1485_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1490_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1490_, 0, v___x_1487_);
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
    mut v_msg_1492_: *mut LeanObject,
    mut v___y_1493_: *mut LeanObject,
    mut v___y_1494_: *mut LeanObject,
    mut v___y_1495_: *mut LeanObject,
    mut v___y_1496_: *mut LeanObject,
    mut v___y_1497_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1498_: *mut LeanObject = core::ptr::null_mut();
    v_res_1498_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v_msg_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_);
    lean_dec(v___y_1496_);
    lean_dec_ref(v___y_1495_);
    lean_dec(v___y_1494_);
    lean_dec_ref(v___y_1493_);
    return v_res_1498_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_1500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut LeanObject = core::ptr::null_mut();
    v___x_1500_ = l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__0;
    v___x_1501_ = l_Lean_stringToMessageData(v___x_1500_);
    return v___x_1501_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0(
    mut v_ctor_1502_: *mut LeanObject,
    mut v_args_1503_: *mut LeanObject,
    mut v___y_1504_: *mut LeanObject,
    mut v___y_1505_: *mut LeanObject,
    mut v___y_1506_: *mut LeanObject,
    mut v___y_1507_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1510_: u8 = 0;
    let mut v___x_1511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: u8 = 0;
    let mut v___x_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: u8 = 0;
    let mut v___x_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: u8 = 0;
    let mut v___x_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: u8 = 0;
    let mut v___x_1525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: u8 = 0;
    let mut v___x_1527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: u8 = 0;
    let mut v___x_1531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1536_: u8 = 0;
    let mut v___x_1538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1540_: u8 = 0;
    let mut v___x_1541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: u8 = 0;
    let mut v___x_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1549_: u8 = 0;
    let mut v___x_1551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1553_: u8 = 0;
    let mut v___x_1554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: u8 = 0;
    let mut v___x_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1562_: u8 = 0;
    let mut v___x_1564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1565_: *mut LeanObject = core::ptr::null_mut();
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
                            v___x_1529_ = lean_unsigned_to_nat(0);
                            v___x_1530_ = lean_nat_dec_eq(v___x_1528_, v___x_1529_);
                            if v___x_1530_ == 0 {
                                v___x_1531_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once), _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
                                v___x_1532_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_1531_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
                                v_a_1533_ = lean_ctor_get(v___x_1532_, 0);
                                v_isSharedCheck_1540_ = (!lean_is_exclusive(v___x_1532_)) as u8;
                                if v_isSharedCheck_1540_ == 0 {
                                    v___x_1535_ = v___x_1532_;
                                    v_isShared_1536_ = v_isSharedCheck_1540_;
                                    state = 4;
                                    continue;
                                } else {
                                    lean_inc(v_a_1533_);
                                    lean_dec(v___x_1532_);
                                    v___x_1535_ = lean_box(0);
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
                        v___x_1542_ = lean_unsigned_to_nat(0);
                        v___x_1543_ = lean_nat_dec_eq(v___x_1541_, v___x_1542_);
                        if v___x_1543_ == 0 {
                            v___x_1544_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once), _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
                            v___x_1545_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_1544_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
                            v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
                            v_isSharedCheck_1553_ = (!lean_is_exclusive(v___x_1545_)) as u8;
                            if v_isSharedCheck_1553_ == 0 {
                                v___x_1548_ = v___x_1545_;
                                v_isShared_1549_ = v_isSharedCheck_1553_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_1546_);
                                lean_dec(v___x_1545_);
                                v___x_1548_ = lean_box(0);
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
                    v___x_1555_ = lean_unsigned_to_nat(0);
                    v___x_1556_ = lean_nat_dec_eq(v___x_1554_, v___x_1555_);
                    if v___x_1556_ == 0 {
                        v___x_1557_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once), _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
                        v___x_1558_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_1557_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
                        v_a_1559_ = lean_ctor_get(v___x_1558_, 0);
                        v_isSharedCheck_1566_ = (!lean_is_exclusive(v___x_1558_)) as u8;
                        if v_isSharedCheck_1566_ == 0 {
                            v___x_1561_ = v___x_1558_;
                            v_isShared_1562_ = v_isSharedCheck_1566_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_1559_);
                            lean_dec(v___x_1558_);
                            v___x_1561_ = lean_box(0);
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
                v___x_1511_ = lean_box((v___x_1510_) as usize);
                v___x_1512_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1512_, 0, v___x_1511_);
                return v___x_1512_;
            }
            2 => {
                v___x_1514_ = 0;
                v___x_1515_ = lean_box((v___x_1514_) as usize);
                v___x_1516_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1516_, 0, v___x_1515_);
                return v___x_1516_;
            }
            3 => {
                v___x_1518_ = 2;
                v___x_1519_ = lean_box((v___x_1518_) as usize);
                v___x_1520_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1520_, 0, v___x_1519_);
                return v___x_1520_;
            }
            4 => {
                if v_isShared_1536_ == 0 {
                    v___x_1538_ = v___x_1535_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1539_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1539_, 0, v_a_1533_);
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
                    v_reuseFailAlloc_1552_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1552_, 0, v_a_1546_);
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
                    v_reuseFailAlloc_1565_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1565_, 0, v_a_1559_);
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
    mut v_ctor_1567_: *mut LeanObject,
    mut v_args_1568_: *mut LeanObject,
    mut v___y_1569_: *mut LeanObject,
    mut v___y_1570_: *mut LeanObject,
    mut v___y_1571_: *mut LeanObject,
    mut v___y_1572_: *mut LeanObject,
    mut v___y_1573_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1574_: *mut LeanObject = core::ptr::null_mut();
    v_res_1574_ = l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0(
        v_ctor_1567_,
        v_args_1568_,
        v___y_1569_,
        v___y_1570_,
        v___y_1571_,
        v___y_1572_,
    );
    lean_dec(v___y_1572_);
    lean_dec_ref(v___y_1571_);
    lean_dec(v___y_1570_);
    lean_dec_ref(v___y_1569_);
    lean_dec_ref(v_args_1568_);
    lean_dec_ref(v_ctor_1567_);
    return v_res_1574_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr(
    mut v_a_1576_: *mut LeanObject,
    mut v_a_1577_: *mut LeanObject,
    mut v_a_1578_: *mut LeanObject,
    mut v_a_1579_: *mut LeanObject,
    mut v_a_1580_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_1585_: *mut LeanObject,
    mut v_a_1586_: *mut LeanObject,
    mut v_a_1587_: *mut LeanObject,
    mut v_a_1588_: *mut LeanObject,
    mut v_a_1589_: *mut LeanObject,
    mut v_a_1590_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1591_: *mut LeanObject = core::ptr::null_mut();
    v_res_1591_ = l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr(
        v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_,
    );
    lean_dec(v_a_1589_);
    lean_dec_ref(v_a_1588_);
    lean_dec(v_a_1587_);
    lean_dec_ref(v_a_1586_);
    return v_res_1591_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1(
    mut v_00_u03b1_1592_: *mut LeanObject,
    mut v_msg_1593_: *mut LeanObject,
    mut v___y_1594_: *mut LeanObject,
    mut v___y_1595_: *mut LeanObject,
    mut v___y_1596_: *mut LeanObject,
    mut v___y_1597_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1599_: *mut LeanObject = core::ptr::null_mut();
    v___x_1599_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v_msg_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_);
    return v___x_1599_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___boxed(
    mut v_00_u03b1_1600_: *mut LeanObject,
    mut v_msg_1601_: *mut LeanObject,
    mut v___y_1602_: *mut LeanObject,
    mut v___y_1603_: *mut LeanObject,
    mut v___y_1604_: *mut LeanObject,
    mut v___y_1605_: *mut LeanObject,
    mut v___y_1606_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1607_: *mut LeanObject = core::ptr::null_mut();
    v_res_1607_ =
        l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1(
            v_00_u03b1_1600_,
            v_msg_1601_,
            v___y_1602_,
            v___y_1603_,
            v___y_1604_,
            v___y_1605_,
        );
    lean_dec(v___y_1605_);
    lean_dec_ref(v___y_1604_);
    lean_dec(v___y_1603_);
    lean_dec_ref(v___y_1602_);
    return v_res_1607_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals___closed__1() -> *mut LeanObject
{
    let mut v___x_1609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut LeanObject = core::ptr::null_mut();
    v___x_1609_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__1_once),
        _init_l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals___closed__1,
    );
    v___x_1610_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1610_, 0, v___x_1609_);
    return v___x_1610_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals___closed__2() -> *mut LeanObject
{
    let mut v___x_1611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut LeanObject = core::ptr::null_mut();
    v___x_1611_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals___closed__1_once),
        _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals___closed__1,
    );
    v___x_1612_ = l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals___closed__0;
    v___x_1613_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1613_, 0, v___x_1612_);
    lean_ctor_set(v___x_1613_, 1, v___x_1611_);
    return v___x_1613_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals() -> *mut LeanObject {
    let mut v___x_1614_: *mut LeanObject = core::ptr::null_mut();
    v___x_1614_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals___closed__2_once),
        _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals___closed__2,
    );
    return v___x_1614_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___lam__0(
    mut v___x_1617_: *mut LeanObject,
    mut v___x_1618_: *mut LeanObject,
    mut v___x_1619_: *mut LeanObject,
    mut v_ctor_1620_: *mut LeanObject,
    mut v_args_1621_: *mut LeanObject,
    mut v___y_1622_: *mut LeanObject,
    mut v___y_1623_: *mut LeanObject,
    mut v___y_1624_: *mut LeanObject,
    mut v___y_1625_: *mut LeanObject,
    mut v___y_1626_: *mut LeanObject,
    mut v___y_1627_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: u8 = 0;
    let mut v___x_1631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: u8 = 0;
    let mut v___x_1633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: u8 = 0;
    let mut v___x_1635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1641_: u8 = 0;
    let mut v___x_1642_: u8 = 0;
    let mut v___x_1643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1650_: u8 = 0;
    let mut v_unused_1651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1655_: u8 = 0;
    let mut v___x_1657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1659_: u8 = 0;
    let mut v___x_1660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1665_: u8 = 0;
    let mut v___x_1666_: u8 = 0;
    let mut v___x_1667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1674_: u8 = 0;
    let mut v_unused_1675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1679_: u8 = 0;
    let mut v___x_1681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1683_: u8 = 0;
    let mut v___x_1684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1689_: u8 = 0;
    let mut v___x_1690_: u8 = 0;
    let mut v___x_1691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1698_: u8 = 0;
    let mut v_unused_1699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1703_: u8 = 0;
    let mut v___x_1705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1706_: *mut LeanObject = core::ptr::null_mut();
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
                            lean_dec_ref(v___x_1619_);
                            lean_dec_ref(v___x_1618_);
                            lean_dec_ref(v___x_1617_);
                            v___x_1635_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___redArg();
                            return v___x_1635_;
                        } else {
                            v___x_1636_ = l_Lean_Name_mkStr4(
                                v___x_1617_,
                                v___x_1618_,
                                v___x_1619_,
                                v___x_1633_,
                            );
                            v___x_1637_ = lean_unsigned_to_nat(0);
                            lean_inc(v___x_1636_);
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
                            if lean_obj_tag(v___x_1638_) == 0 {
                                v_isSharedCheck_1650_ = (!lean_is_exclusive(v___x_1638_)) as u8;
                                if v_isSharedCheck_1650_ == 0 {
                                    v_unused_1651_ = lean_ctor_get(v___x_1638_, 0);
                                    lean_dec(v_unused_1651_);
                                    v___x_1640_ = v___x_1638_;
                                    v_isShared_1641_ = v_isSharedCheck_1650_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_dec(v___x_1638_);
                                    v___x_1640_ = lean_box(0);
                                    v_isShared_1641_ = v_isSharedCheck_1650_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec(v___x_1636_);
                                v_a_1652_ = lean_ctor_get(v___x_1638_, 0);
                                v_isSharedCheck_1659_ = (!lean_is_exclusive(v___x_1638_)) as u8;
                                if v_isSharedCheck_1659_ == 0 {
                                    v___x_1654_ = v___x_1638_;
                                    v_isShared_1655_ = v_isSharedCheck_1659_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_inc(v_a_1652_);
                                    lean_dec(v___x_1638_);
                                    v___x_1654_ = lean_box(0);
                                    v_isShared_1655_ = v_isSharedCheck_1659_;
                                    state = 3;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v___x_1660_ =
                            l_Lean_Name_mkStr4(v___x_1617_, v___x_1618_, v___x_1619_, v___x_1631_);
                        v___x_1661_ = lean_unsigned_to_nat(0);
                        lean_inc(v___x_1660_);
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
                        if lean_obj_tag(v___x_1662_) == 0 {
                            v_isSharedCheck_1674_ = (!lean_is_exclusive(v___x_1662_)) as u8;
                            if v_isSharedCheck_1674_ == 0 {
                                v_unused_1675_ = lean_ctor_get(v___x_1662_, 0);
                                lean_dec(v_unused_1675_);
                                v___x_1664_ = v___x_1662_;
                                v_isShared_1665_ = v_isSharedCheck_1674_;
                                state = 5;
                                continue;
                            } else {
                                lean_dec(v___x_1662_);
                                v___x_1664_ = lean_box(0);
                                v_isShared_1665_ = v_isSharedCheck_1674_;
                                state = 5;
                                continue;
                            }
                        } else {
                            lean_dec(v___x_1660_);
                            v_a_1676_ = lean_ctor_get(v___x_1662_, 0);
                            v_isSharedCheck_1683_ = (!lean_is_exclusive(v___x_1662_)) as u8;
                            if v_isSharedCheck_1683_ == 0 {
                                v___x_1678_ = v___x_1662_;
                                v_isShared_1679_ = v_isSharedCheck_1683_;
                                state = 7;
                                continue;
                            } else {
                                lean_inc(v_a_1676_);
                                lean_dec(v___x_1662_);
                                v___x_1678_ = lean_box(0);
                                v_isShared_1679_ = v_isSharedCheck_1683_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                } else {
                    v___x_1684_ =
                        l_Lean_Name_mkStr4(v___x_1617_, v___x_1618_, v___x_1619_, v___x_1629_);
                    v___x_1685_ = lean_unsigned_to_nat(0);
                    lean_inc(v___x_1684_);
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
                    if lean_obj_tag(v___x_1686_) == 0 {
                        v_isSharedCheck_1698_ = (!lean_is_exclusive(v___x_1686_)) as u8;
                        if v_isSharedCheck_1698_ == 0 {
                            v_unused_1699_ = lean_ctor_get(v___x_1686_, 0);
                            lean_dec(v_unused_1699_);
                            v___x_1688_ = v___x_1686_;
                            v_isShared_1689_ = v_isSharedCheck_1698_;
                            state = 9;
                            continue;
                        } else {
                            lean_dec(v___x_1686_);
                            v___x_1688_ = lean_box(0);
                            v_isShared_1689_ = v_isSharedCheck_1698_;
                            state = 9;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_1684_);
                        v_a_1700_ = lean_ctor_get(v___x_1686_, 0);
                        v_isSharedCheck_1707_ = (!lean_is_exclusive(v___x_1686_)) as u8;
                        if v_isSharedCheck_1707_ == 0 {
                            v___x_1702_ = v___x_1686_;
                            v_isShared_1703_ = v_isSharedCheck_1707_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_a_1700_);
                            lean_dec(v___x_1686_);
                            v___x_1702_ = lean_box(0);
                            v_isShared_1703_ = v_isSharedCheck_1707_;
                            state = 11;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1642_ = 1;
                v___x_1643_ = lean_box(0);
                v___x_1644_ = l_Lean_Expr_const___override(v___x_1636_, v___x_1643_);
                v___x_1645_ = lean_box((v___x_1642_) as usize);
                v___x_1646_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1646_, 0, v___x_1645_);
                lean_ctor_set(v___x_1646_, 1, v___x_1644_);
                if v_isShared_1641_ == 0 {
                    lean_ctor_set(v___x_1640_, 0, v___x_1646_);
                    v___x_1648_ = v___x_1640_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1649_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1649_, 0, v___x_1646_);
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
                    v_reuseFailAlloc_1658_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_a_1652_);
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
                v___x_1667_ = lean_box(0);
                v___x_1668_ = l_Lean_Expr_const___override(v___x_1660_, v___x_1667_);
                v___x_1669_ = lean_box((v___x_1666_) as usize);
                v___x_1670_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1670_, 0, v___x_1669_);
                lean_ctor_set(v___x_1670_, 1, v___x_1668_);
                if v_isShared_1665_ == 0 {
                    lean_ctor_set(v___x_1664_, 0, v___x_1670_);
                    v___x_1672_ = v___x_1664_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1673_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1673_, 0, v___x_1670_);
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
                    v_reuseFailAlloc_1682_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_a_1676_);
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
                v___x_1691_ = lean_box(0);
                v___x_1692_ = l_Lean_Expr_const___override(v___x_1684_, v___x_1691_);
                v___x_1693_ = lean_box((v___x_1690_) as usize);
                v___x_1694_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1694_, 0, v___x_1693_);
                lean_ctor_set(v___x_1694_, 1, v___x_1692_);
                if v_isShared_1689_ == 0 {
                    lean_ctor_set(v___x_1688_, 0, v___x_1694_);
                    v___x_1696_ = v___x_1688_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1697_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1697_, 0, v___x_1694_);
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
                    v_reuseFailAlloc_1706_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1706_, 0, v_a_1700_);
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
    mut v___x_1708_: *mut LeanObject,
    mut v___x_1709_: *mut LeanObject,
    mut v___x_1710_: *mut LeanObject,
    mut v_ctor_1711_: *mut LeanObject,
    mut v_args_1712_: *mut LeanObject,
    mut v___y_1713_: *mut LeanObject,
    mut v___y_1714_: *mut LeanObject,
    mut v___y_1715_: *mut LeanObject,
    mut v___y_1716_: *mut LeanObject,
    mut v___y_1717_: *mut LeanObject,
    mut v___y_1718_: *mut LeanObject,
    mut v___y_1719_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1720_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_1718_);
    lean_dec_ref(v___y_1717_);
    lean_dec(v___y_1716_);
    lean_dec_ref(v___y_1715_);
    lean_dec(v___y_1714_);
    lean_dec_ref(v___y_1713_);
    lean_dec_ref(v_args_1712_);
    lean_dec_ref(v_ctor_1711_);
    return v_res_1720_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm(
    mut v_a_1730_: *mut LeanObject,
    mut v_a_1731_: *mut LeanObject,
    mut v_a_1732_: *mut LeanObject,
    mut v_a_1733_: *mut LeanObject,
    mut v_a_1734_: *mut LeanObject,
    mut v_a_1735_: *mut LeanObject,
    mut v_a_1736_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_1741_: *mut LeanObject,
    mut v_a_1742_: *mut LeanObject,
    mut v_a_1743_: *mut LeanObject,
    mut v_a_1744_: *mut LeanObject,
    mut v_a_1745_: *mut LeanObject,
    mut v_a_1746_: *mut LeanObject,
    mut v_a_1747_: *mut LeanObject,
    mut v_a_1748_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1749_: *mut LeanObject = core::ptr::null_mut();
    v_res_1749_ = l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm(
        v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_,
    );
    lean_dec(v_a_1747_);
    lean_dec_ref(v_a_1746_);
    lean_dec(v_a_1745_);
    lean_dec_ref(v_a_1744_);
    lean_dec(v_a_1743_);
    lean_dec_ref(v_a_1742_);
    return v_res_1749_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__1() -> *mut LeanObject
{
    let mut v___x_1751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut LeanObject = core::ptr::null_mut();
    v___x_1751_ = lean_box(0);
    v___x_1752_ = l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode_evalTerm___closed__2;
    v___x_1753_ = l_Lean_Expr_const___override(v___x_1752_, v___x_1751_);
    return v___x_1753_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__2() -> *mut LeanObject
{
    let mut v___x_1754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut LeanObject = core::ptr::null_mut();
    v___x_1754_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__1_once),
        _init_l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__1,
    );
    v___x_1755_ = l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__0;
    v___x_1756_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1756_, 0, v___x_1755_);
    lean_ctor_set(v___x_1756_, 1, v___x_1754_);
    return v___x_1756_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode() -> *mut LeanObject {
    let mut v___x_1757_: *mut LeanObject = core::ptr::null_mut();
    v___x_1757_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__2_once),
        _init_l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__2,
    );
    return v___x_1757_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode_evalExpr___lam__0(
    mut v_ctor_1758_: *mut LeanObject,
    mut v_args_1759_: *mut LeanObject,
    mut v___y_1760_: *mut LeanObject,
    mut v___y_1761_: *mut LeanObject,
    mut v___y_1762_: *mut LeanObject,
    mut v___y_1763_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1766_: u8 = 0;
    let mut v___x_1767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: u8 = 0;
    let mut v___x_1771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: u8 = 0;
    let mut v___x_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: u8 = 0;
    let mut v___x_1779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: u8 = 0;
    let mut v___x_1781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: u8 = 0;
    let mut v___x_1783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: u8 = 0;
    let mut v___x_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1792_: u8 = 0;
    let mut v___x_1794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1796_: u8 = 0;
    let mut v___x_1797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: u8 = 0;
    let mut v___x_1800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1805_: u8 = 0;
    let mut v___x_1807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1809_: u8 = 0;
    let mut v___x_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: u8 = 0;
    let mut v___x_1813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1818_: u8 = 0;
    let mut v___x_1820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1821_: *mut LeanObject = core::ptr::null_mut();
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
                            v___x_1785_ = lean_unsigned_to_nat(0);
                            v___x_1786_ = lean_nat_dec_eq(v___x_1784_, v___x_1785_);
                            if v___x_1786_ == 0 {
                                v___x_1787_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once), _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
                                v___x_1788_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_1787_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_);
                                v_a_1789_ = lean_ctor_get(v___x_1788_, 0);
                                v_isSharedCheck_1796_ = (!lean_is_exclusive(v___x_1788_)) as u8;
                                if v_isSharedCheck_1796_ == 0 {
                                    v___x_1791_ = v___x_1788_;
                                    v_isShared_1792_ = v_isSharedCheck_1796_;
                                    state = 4;
                                    continue;
                                } else {
                                    lean_inc(v_a_1789_);
                                    lean_dec(v___x_1788_);
                                    v___x_1791_ = lean_box(0);
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
                        v___x_1798_ = lean_unsigned_to_nat(0);
                        v___x_1799_ = lean_nat_dec_eq(v___x_1797_, v___x_1798_);
                        if v___x_1799_ == 0 {
                            v___x_1800_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once), _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
                            v___x_1801_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_1800_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_);
                            v_a_1802_ = lean_ctor_get(v___x_1801_, 0);
                            v_isSharedCheck_1809_ = (!lean_is_exclusive(v___x_1801_)) as u8;
                            if v_isSharedCheck_1809_ == 0 {
                                v___x_1804_ = v___x_1801_;
                                v_isShared_1805_ = v_isSharedCheck_1809_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_1802_);
                                lean_dec(v___x_1801_);
                                v___x_1804_ = lean_box(0);
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
                    v___x_1811_ = lean_unsigned_to_nat(0);
                    v___x_1812_ = lean_nat_dec_eq(v___x_1810_, v___x_1811_);
                    if v___x_1812_ == 0 {
                        v___x_1813_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once), _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
                        v___x_1814_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_1813_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_);
                        v_a_1815_ = lean_ctor_get(v___x_1814_, 0);
                        v_isSharedCheck_1822_ = (!lean_is_exclusive(v___x_1814_)) as u8;
                        if v_isSharedCheck_1822_ == 0 {
                            v___x_1817_ = v___x_1814_;
                            v_isShared_1818_ = v_isSharedCheck_1822_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_1815_);
                            lean_dec(v___x_1814_);
                            v___x_1817_ = lean_box(0);
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
                v___x_1767_ = lean_box((v___x_1766_) as usize);
                v___x_1768_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1768_, 0, v___x_1767_);
                return v___x_1768_;
            }
            2 => {
                v___x_1770_ = 2;
                v___x_1771_ = lean_box((v___x_1770_) as usize);
                v___x_1772_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1772_, 0, v___x_1771_);
                return v___x_1772_;
            }
            3 => {
                v___x_1774_ = 0;
                v___x_1775_ = lean_box((v___x_1774_) as usize);
                v___x_1776_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1776_, 0, v___x_1775_);
                return v___x_1776_;
            }
            4 => {
                if v_isShared_1792_ == 0 {
                    v___x_1794_ = v___x_1791_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1795_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_a_1789_);
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
                    v_reuseFailAlloc_1808_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_a_1802_);
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
                    v_reuseFailAlloc_1821_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1821_, 0, v_a_1815_);
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
    mut v_ctor_1823_: *mut LeanObject,
    mut v_args_1824_: *mut LeanObject,
    mut v___y_1825_: *mut LeanObject,
    mut v___y_1826_: *mut LeanObject,
    mut v___y_1827_: *mut LeanObject,
    mut v___y_1828_: *mut LeanObject,
    mut v___y_1829_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1830_: *mut LeanObject = core::ptr::null_mut();
    v_res_1830_ = l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode_evalExpr___lam__0(
        v_ctor_1823_,
        v_args_1824_,
        v___y_1825_,
        v___y_1826_,
        v___y_1827_,
        v___y_1828_,
    );
    lean_dec(v___y_1828_);
    lean_dec_ref(v___y_1827_);
    lean_dec(v___y_1826_);
    lean_dec_ref(v___y_1825_);
    lean_dec_ref(v_args_1824_);
    lean_dec_ref(v_ctor_1823_);
    return v_res_1830_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode_evalExpr(
    mut v_a_1832_: *mut LeanObject,
    mut v_a_1833_: *mut LeanObject,
    mut v_a_1834_: *mut LeanObject,
    mut v_a_1835_: *mut LeanObject,
    mut v_a_1836_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_1841_: *mut LeanObject,
    mut v_a_1842_: *mut LeanObject,
    mut v_a_1843_: *mut LeanObject,
    mut v_a_1844_: *mut LeanObject,
    mut v_a_1845_: *mut LeanObject,
    mut v_a_1846_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1847_: *mut LeanObject = core::ptr::null_mut();
    v_res_1847_ = l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode_evalExpr(
        v_a_1841_, v_a_1842_, v_a_1843_, v_a_1844_, v_a_1845_,
    );
    lean_dec(v_a_1845_);
    lean_dec_ref(v_a_1844_);
    lean_dec(v_a_1843_);
    lean_dec_ref(v_a_1842_);
    return v_res_1847_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode___closed__1() -> *mut LeanObject
{
    let mut v___x_1849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut LeanObject = core::ptr::null_mut();
    v___x_1849_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__1_once),
        _init_l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode___closed__1,
    );
    v___x_1850_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1850_, 0, v___x_1849_);
    return v___x_1850_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode___closed__2() -> *mut LeanObject
{
    let mut v___x_1851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut LeanObject = core::ptr::null_mut();
    v___x_1851_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode___closed__1_once),
        _init_l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode___closed__1,
    );
    v___x_1852_ = l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode___closed__0;
    v___x_1853_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1853_, 0, v___x_1852_);
    lean_ctor_set(v___x_1853_, 1, v___x_1851_);
    return v___x_1853_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode() -> *mut LeanObject {
    let mut v___x_1854_: *mut LeanObject = core::ptr::null_mut();
    v___x_1854_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode___closed__2_once),
        _init_l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode___closed__2,
    );
    return v___x_1854_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___lam__0(
    mut v___x_1858_: *mut LeanObject,
    mut v___x_1859_: *mut LeanObject,
    mut v___x_1860_: *mut LeanObject,
    mut v_ctor_1861_: *mut LeanObject,
    mut v_args_1862_: *mut LeanObject,
    mut v___y_1863_: *mut LeanObject,
    mut v___y_1864_: *mut LeanObject,
    mut v___y_1865_: *mut LeanObject,
    mut v___y_1866_: *mut LeanObject,
    mut v___y_1867_: *mut LeanObject,
    mut v___y_1868_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: u8 = 0;
    let mut v___x_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: u8 = 0;
    let mut v___x_1874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: u8 = 0;
    let mut v___x_1876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: u8 = 0;
    let mut v___x_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: u8 = 0;
    let mut v___x_1880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1886_: u8 = 0;
    let mut v___x_1887_: u8 = 0;
    let mut v___x_1888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1895_: u8 = 0;
    let mut v_unused_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1900_: u8 = 0;
    let mut v___x_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1904_: u8 = 0;
    let mut v___x_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1910_: u8 = 0;
    let mut v___x_1911_: u8 = 0;
    let mut v___x_1912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1919_: u8 = 0;
    let mut v_unused_1920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1924_: u8 = 0;
    let mut v___x_1926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1928_: u8 = 0;
    let mut v___x_1929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1934_: u8 = 0;
    let mut v___x_1935_: u8 = 0;
    let mut v___x_1936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1943_: u8 = 0;
    let mut v_unused_1944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1948_: u8 = 0;
    let mut v___x_1950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1952_: u8 = 0;
    let mut v___x_1953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1958_: u8 = 0;
    let mut v___x_1959_: u8 = 0;
    let mut v___x_1960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1967_: u8 = 0;
    let mut v_unused_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1972_: u8 = 0;
    let mut v___x_1974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1976_: u8 = 0;
    let mut v___x_1977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1982_: u8 = 0;
    let mut v___x_1983_: u8 = 0;
    let mut v___x_1984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1991_: u8 = 0;
    let mut v_unused_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1996_: u8 = 0;
    let mut v___x_1998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1999_: *mut LeanObject = core::ptr::null_mut();
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
                                    lean_dec_ref(v___x_1860_);
                                    lean_dec_ref(v___x_1859_);
                                    lean_dec_ref(v___x_1858_);
                                    v___x_1880_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___redArg();
                                    return v___x_1880_;
                                } else {
                                    v___x_1881_ = l_Lean_Name_mkStr4(
                                        v___x_1858_,
                                        v___x_1859_,
                                        v___x_1860_,
                                        v___x_1878_,
                                    );
                                    v___x_1882_ = lean_unsigned_to_nat(0);
                                    lean_inc(v___x_1881_);
                                    v___x_1883_ = l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(v___x_1881_, v___x_1882_, v_args_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_);
                                    if lean_obj_tag(v___x_1883_) == 0 {
                                        v_isSharedCheck_1895_ =
                                            (!lean_is_exclusive(v___x_1883_)) as u8;
                                        if v_isSharedCheck_1895_ == 0 {
                                            v_unused_1896_ = lean_ctor_get(v___x_1883_, 0);
                                            lean_dec(v_unused_1896_);
                                            v___x_1885_ = v___x_1883_;
                                            v_isShared_1886_ = v_isSharedCheck_1895_;
                                            state = 1;
                                            continue;
                                        } else {
                                            lean_dec(v___x_1883_);
                                            v___x_1885_ = lean_box(0);
                                            v_isShared_1886_ = v_isSharedCheck_1895_;
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        lean_dec(v___x_1881_);
                                        v_a_1897_ = lean_ctor_get(v___x_1883_, 0);
                                        v_isSharedCheck_1904_ =
                                            (!lean_is_exclusive(v___x_1883_)) as u8;
                                        if v_isSharedCheck_1904_ == 0 {
                                            v___x_1899_ = v___x_1883_;
                                            v_isShared_1900_ = v_isSharedCheck_1904_;
                                            state = 3;
                                            continue;
                                        } else {
                                            lean_inc(v_a_1897_);
                                            lean_dec(v___x_1883_);
                                            v___x_1899_ = lean_box(0);
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
                                v___x_1906_ = lean_unsigned_to_nat(0);
                                lean_inc(v___x_1905_);
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
                                if lean_obj_tag(v___x_1907_) == 0 {
                                    v_isSharedCheck_1919_ = (!lean_is_exclusive(v___x_1907_)) as u8;
                                    if v_isSharedCheck_1919_ == 0 {
                                        v_unused_1920_ = lean_ctor_get(v___x_1907_, 0);
                                        lean_dec(v_unused_1920_);
                                        v___x_1909_ = v___x_1907_;
                                        v_isShared_1910_ = v_isSharedCheck_1919_;
                                        state = 5;
                                        continue;
                                    } else {
                                        lean_dec(v___x_1907_);
                                        v___x_1909_ = lean_box(0);
                                        v_isShared_1910_ = v_isSharedCheck_1919_;
                                        state = 5;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v___x_1905_);
                                    v_a_1921_ = lean_ctor_get(v___x_1907_, 0);
                                    v_isSharedCheck_1928_ = (!lean_is_exclusive(v___x_1907_)) as u8;
                                    if v_isSharedCheck_1928_ == 0 {
                                        v___x_1923_ = v___x_1907_;
                                        v_isShared_1924_ = v_isSharedCheck_1928_;
                                        state = 7;
                                        continue;
                                    } else {
                                        lean_inc(v_a_1921_);
                                        lean_dec(v___x_1907_);
                                        v___x_1923_ = lean_box(0);
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
                            v___x_1930_ = lean_unsigned_to_nat(0);
                            lean_inc(v___x_1929_);
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
                            if lean_obj_tag(v___x_1931_) == 0 {
                                v_isSharedCheck_1943_ = (!lean_is_exclusive(v___x_1931_)) as u8;
                                if v_isSharedCheck_1943_ == 0 {
                                    v_unused_1944_ = lean_ctor_get(v___x_1931_, 0);
                                    lean_dec(v_unused_1944_);
                                    v___x_1933_ = v___x_1931_;
                                    v_isShared_1934_ = v_isSharedCheck_1943_;
                                    state = 9;
                                    continue;
                                } else {
                                    lean_dec(v___x_1931_);
                                    v___x_1933_ = lean_box(0);
                                    v_isShared_1934_ = v_isSharedCheck_1943_;
                                    state = 9;
                                    continue;
                                }
                            } else {
                                lean_dec(v___x_1929_);
                                v_a_1945_ = lean_ctor_get(v___x_1931_, 0);
                                v_isSharedCheck_1952_ = (!lean_is_exclusive(v___x_1931_)) as u8;
                                if v_isSharedCheck_1952_ == 0 {
                                    v___x_1947_ = v___x_1931_;
                                    v_isShared_1948_ = v_isSharedCheck_1952_;
                                    state = 11;
                                    continue;
                                } else {
                                    lean_inc(v_a_1945_);
                                    lean_dec(v___x_1931_);
                                    v___x_1947_ = lean_box(0);
                                    v_isShared_1948_ = v_isSharedCheck_1952_;
                                    state = 11;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v___x_1953_ =
                            l_Lean_Name_mkStr4(v___x_1858_, v___x_1859_, v___x_1860_, v___x_1872_);
                        v___x_1954_ = lean_unsigned_to_nat(0);
                        lean_inc(v___x_1953_);
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
                        if lean_obj_tag(v___x_1955_) == 0 {
                            v_isSharedCheck_1967_ = (!lean_is_exclusive(v___x_1955_)) as u8;
                            if v_isSharedCheck_1967_ == 0 {
                                v_unused_1968_ = lean_ctor_get(v___x_1955_, 0);
                                lean_dec(v_unused_1968_);
                                v___x_1957_ = v___x_1955_;
                                v_isShared_1958_ = v_isSharedCheck_1967_;
                                state = 13;
                                continue;
                            } else {
                                lean_dec(v___x_1955_);
                                v___x_1957_ = lean_box(0);
                                v_isShared_1958_ = v_isSharedCheck_1967_;
                                state = 13;
                                continue;
                            }
                        } else {
                            lean_dec(v___x_1953_);
                            v_a_1969_ = lean_ctor_get(v___x_1955_, 0);
                            v_isSharedCheck_1976_ = (!lean_is_exclusive(v___x_1955_)) as u8;
                            if v_isSharedCheck_1976_ == 0 {
                                v___x_1971_ = v___x_1955_;
                                v_isShared_1972_ = v_isSharedCheck_1976_;
                                state = 15;
                                continue;
                            } else {
                                lean_inc(v_a_1969_);
                                lean_dec(v___x_1955_);
                                v___x_1971_ = lean_box(0);
                                v_isShared_1972_ = v_isSharedCheck_1976_;
                                state = 15;
                                continue;
                            }
                        }
                    }
                } else {
                    v___x_1977_ =
                        l_Lean_Name_mkStr4(v___x_1858_, v___x_1859_, v___x_1860_, v___x_1870_);
                    v___x_1978_ = lean_unsigned_to_nat(0);
                    lean_inc(v___x_1977_);
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
                    if lean_obj_tag(v___x_1979_) == 0 {
                        v_isSharedCheck_1991_ = (!lean_is_exclusive(v___x_1979_)) as u8;
                        if v_isSharedCheck_1991_ == 0 {
                            v_unused_1992_ = lean_ctor_get(v___x_1979_, 0);
                            lean_dec(v_unused_1992_);
                            v___x_1981_ = v___x_1979_;
                            v_isShared_1982_ = v_isSharedCheck_1991_;
                            state = 17;
                            continue;
                        } else {
                            lean_dec(v___x_1979_);
                            v___x_1981_ = lean_box(0);
                            v_isShared_1982_ = v_isSharedCheck_1991_;
                            state = 17;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_1977_);
                        v_a_1993_ = lean_ctor_get(v___x_1979_, 0);
                        v_isSharedCheck_2000_ = (!lean_is_exclusive(v___x_1979_)) as u8;
                        if v_isSharedCheck_2000_ == 0 {
                            v___x_1995_ = v___x_1979_;
                            v_isShared_1996_ = v_isSharedCheck_2000_;
                            state = 19;
                            continue;
                        } else {
                            lean_inc(v_a_1993_);
                            lean_dec(v___x_1979_);
                            v___x_1995_ = lean_box(0);
                            v_isShared_1996_ = v_isSharedCheck_2000_;
                            state = 19;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1887_ = 2;
                v___x_1888_ = lean_box(0);
                v___x_1889_ = l_Lean_Expr_const___override(v___x_1881_, v___x_1888_);
                v___x_1890_ = lean_box((v___x_1887_) as usize);
                v___x_1891_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1891_, 0, v___x_1890_);
                lean_ctor_set(v___x_1891_, 1, v___x_1889_);
                if v_isShared_1886_ == 0 {
                    lean_ctor_set(v___x_1885_, 0, v___x_1891_);
                    v___x_1893_ = v___x_1885_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1894_, 0, v___x_1891_);
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
                    v_reuseFailAlloc_1903_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1903_, 0, v_a_1897_);
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
                v___x_1912_ = lean_box(0);
                v___x_1913_ = l_Lean_Expr_const___override(v___x_1905_, v___x_1912_);
                v___x_1914_ = lean_box((v___x_1911_) as usize);
                v___x_1915_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1915_, 0, v___x_1914_);
                lean_ctor_set(v___x_1915_, 1, v___x_1913_);
                if v_isShared_1910_ == 0 {
                    lean_ctor_set(v___x_1909_, 0, v___x_1915_);
                    v___x_1917_ = v___x_1909_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1918_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1918_, 0, v___x_1915_);
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
                    v_reuseFailAlloc_1927_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_a_1921_);
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
                v___x_1936_ = lean_box(0);
                v___x_1937_ = l_Lean_Expr_const___override(v___x_1929_, v___x_1936_);
                v___x_1938_ = lean_box((v___x_1935_) as usize);
                v___x_1939_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1939_, 0, v___x_1938_);
                lean_ctor_set(v___x_1939_, 1, v___x_1937_);
                if v_isShared_1934_ == 0 {
                    lean_ctor_set(v___x_1933_, 0, v___x_1939_);
                    v___x_1941_ = v___x_1933_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1942_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1942_, 0, v___x_1939_);
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
                    v_reuseFailAlloc_1951_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_a_1945_);
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
                v___x_1960_ = lean_box(0);
                v___x_1961_ = l_Lean_Expr_const___override(v___x_1953_, v___x_1960_);
                v___x_1962_ = lean_box((v___x_1959_) as usize);
                v___x_1963_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1963_, 0, v___x_1962_);
                lean_ctor_set(v___x_1963_, 1, v___x_1961_);
                if v_isShared_1958_ == 0 {
                    lean_ctor_set(v___x_1957_, 0, v___x_1963_);
                    v___x_1965_ = v___x_1957_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1966_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1966_, 0, v___x_1963_);
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
                    v_reuseFailAlloc_1975_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1975_, 0, v_a_1969_);
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
                v___x_1984_ = lean_box(0);
                v___x_1985_ = l_Lean_Expr_const___override(v___x_1977_, v___x_1984_);
                v___x_1986_ = lean_box((v___x_1983_) as usize);
                v___x_1987_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1987_, 0, v___x_1986_);
                lean_ctor_set(v___x_1987_, 1, v___x_1985_);
                if v_isShared_1982_ == 0 {
                    lean_ctor_set(v___x_1981_, 0, v___x_1987_);
                    v___x_1989_ = v___x_1981_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1990_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1990_, 0, v___x_1987_);
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
                    v_reuseFailAlloc_1999_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1999_, 0, v_a_1993_);
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
    mut v___x_2001_: *mut LeanObject,
    mut v___x_2002_: *mut LeanObject,
    mut v___x_2003_: *mut LeanObject,
    mut v_ctor_2004_: *mut LeanObject,
    mut v_args_2005_: *mut LeanObject,
    mut v___y_2006_: *mut LeanObject,
    mut v___y_2007_: *mut LeanObject,
    mut v___y_2008_: *mut LeanObject,
    mut v___y_2009_: *mut LeanObject,
    mut v___y_2010_: *mut LeanObject,
    mut v___y_2011_: *mut LeanObject,
    mut v___y_2012_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2013_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_2011_);
    lean_dec_ref(v___y_2010_);
    lean_dec(v___y_2009_);
    lean_dec_ref(v___y_2008_);
    lean_dec(v___y_2007_);
    lean_dec_ref(v___y_2006_);
    lean_dec_ref(v_args_2005_);
    lean_dec_ref(v_ctor_2004_);
    return v_res_2013_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm(
    mut v_a_2023_: *mut LeanObject,
    mut v_a_2024_: *mut LeanObject,
    mut v_a_2025_: *mut LeanObject,
    mut v_a_2026_: *mut LeanObject,
    mut v_a_2027_: *mut LeanObject,
    mut v_a_2028_: *mut LeanObject,
    mut v_a_2029_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_2034_: *mut LeanObject,
    mut v_a_2035_: *mut LeanObject,
    mut v_a_2036_: *mut LeanObject,
    mut v_a_2037_: *mut LeanObject,
    mut v_a_2038_: *mut LeanObject,
    mut v_a_2039_: *mut LeanObject,
    mut v_a_2040_: *mut LeanObject,
    mut v_a_2041_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2042_: *mut LeanObject = core::ptr::null_mut();
    v_res_2042_ = l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm(
        v_a_2034_, v_a_2035_, v_a_2036_, v_a_2037_, v_a_2038_, v_a_2039_, v_a_2040_,
    );
    lean_dec(v_a_2040_);
    lean_dec_ref(v_a_2039_);
    lean_dec(v_a_2038_);
    lean_dec_ref(v_a_2037_);
    lean_dec(v_a_2036_);
    lean_dec_ref(v_a_2035_);
    return v_res_2042_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__1()
-> *mut LeanObject {
    let mut v___x_2044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut LeanObject = core::ptr::null_mut();
    v___x_2044_ = lean_box(0);
    v___x_2045_ = l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm___closed__2;
    v___x_2046_ = l_Lean_Expr_const___override(v___x_2045_, v___x_2044_);
    return v___x_2046_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__2()
-> *mut LeanObject {
    let mut v___x_2047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut LeanObject = core::ptr::null_mut();
    v___x_2047_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__1_once
        ),
        _init_l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__1,
    );
    v___x_2048_ = l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__0;
    v___x_2049_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2049_, 0, v___x_2048_);
    lean_ctor_set(v___x_2049_, 1, v___x_2047_);
    return v___x_2049_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode() -> *mut LeanObject {
    let mut v___x_2050_: *mut LeanObject = core::ptr::null_mut();
    v___x_2050_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__2),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__2_once
        ),
        _init_l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__2,
    );
    return v___x_2050_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr___lam__0(
    mut v_ctor_2051_: *mut LeanObject,
    mut v_args_2052_: *mut LeanObject,
    mut v___y_2053_: *mut LeanObject,
    mut v___y_2054_: *mut LeanObject,
    mut v___y_2055_: *mut LeanObject,
    mut v___y_2056_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2059_: u8 = 0;
    let mut v___x_2060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: u8 = 0;
    let mut v___x_2064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: u8 = 0;
    let mut v___x_2068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: u8 = 0;
    let mut v___x_2072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: u8 = 0;
    let mut v___x_2076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: u8 = 0;
    let mut v___x_2080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: u8 = 0;
    let mut v___x_2082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: u8 = 0;
    let mut v___x_2084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: u8 = 0;
    let mut v___x_2086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: u8 = 0;
    let mut v___x_2088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: u8 = 0;
    let mut v___x_2092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2097_: u8 = 0;
    let mut v___x_2099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2101_: u8 = 0;
    let mut v___x_2102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: u8 = 0;
    let mut v___x_2105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2110_: u8 = 0;
    let mut v___x_2112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2114_: u8 = 0;
    let mut v___x_2115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: u8 = 0;
    let mut v___x_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2123_: u8 = 0;
    let mut v___x_2125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2127_: u8 = 0;
    let mut v___x_2128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: u8 = 0;
    let mut v___x_2131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2136_: u8 = 0;
    let mut v___x_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2140_: u8 = 0;
    let mut v___x_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: u8 = 0;
    let mut v___x_2144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2149_: u8 = 0;
    let mut v___x_2151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2152_: *mut LeanObject = core::ptr::null_mut();
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
                                    v___x_2090_ = lean_unsigned_to_nat(0);
                                    v___x_2091_ = lean_nat_dec_eq(v___x_2089_, v___x_2090_);
                                    if v___x_2091_ == 0 {
                                        v___x_2092_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once), _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
                                        v___x_2093_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_2092_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_);
                                        v_a_2094_ = lean_ctor_get(v___x_2093_, 0);
                                        v_isSharedCheck_2101_ =
                                            (!lean_is_exclusive(v___x_2093_)) as u8;
                                        if v_isSharedCheck_2101_ == 0 {
                                            v___x_2096_ = v___x_2093_;
                                            v_isShared_2097_ = v_isSharedCheck_2101_;
                                            state = 6;
                                            continue;
                                        } else {
                                            lean_inc(v_a_2094_);
                                            lean_dec(v___x_2093_);
                                            v___x_2096_ = lean_box(0);
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
                                v___x_2103_ = lean_unsigned_to_nat(0);
                                v___x_2104_ = lean_nat_dec_eq(v___x_2102_, v___x_2103_);
                                if v___x_2104_ == 0 {
                                    v___x_2105_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once), _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
                                    v___x_2106_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_2105_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_);
                                    v_a_2107_ = lean_ctor_get(v___x_2106_, 0);
                                    v_isSharedCheck_2114_ = (!lean_is_exclusive(v___x_2106_)) as u8;
                                    if v_isSharedCheck_2114_ == 0 {
                                        v___x_2109_ = v___x_2106_;
                                        v_isShared_2110_ = v_isSharedCheck_2114_;
                                        state = 8;
                                        continue;
                                    } else {
                                        lean_inc(v_a_2107_);
                                        lean_dec(v___x_2106_);
                                        v___x_2109_ = lean_box(0);
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
                            v___x_2116_ = lean_unsigned_to_nat(0);
                            v___x_2117_ = lean_nat_dec_eq(v___x_2115_, v___x_2116_);
                            if v___x_2117_ == 0 {
                                v___x_2118_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once), _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
                                v___x_2119_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_2118_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_);
                                v_a_2120_ = lean_ctor_get(v___x_2119_, 0);
                                v_isSharedCheck_2127_ = (!lean_is_exclusive(v___x_2119_)) as u8;
                                if v_isSharedCheck_2127_ == 0 {
                                    v___x_2122_ = v___x_2119_;
                                    v_isShared_2123_ = v_isSharedCheck_2127_;
                                    state = 10;
                                    continue;
                                } else {
                                    lean_inc(v_a_2120_);
                                    lean_dec(v___x_2119_);
                                    v___x_2122_ = lean_box(0);
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
                        v___x_2129_ = lean_unsigned_to_nat(0);
                        v___x_2130_ = lean_nat_dec_eq(v___x_2128_, v___x_2129_);
                        if v___x_2130_ == 0 {
                            v___x_2131_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once), _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
                            v___x_2132_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_2131_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_);
                            v_a_2133_ = lean_ctor_get(v___x_2132_, 0);
                            v_isSharedCheck_2140_ = (!lean_is_exclusive(v___x_2132_)) as u8;
                            if v_isSharedCheck_2140_ == 0 {
                                v___x_2135_ = v___x_2132_;
                                v_isShared_2136_ = v_isSharedCheck_2140_;
                                state = 12;
                                continue;
                            } else {
                                lean_inc(v_a_2133_);
                                lean_dec(v___x_2132_);
                                v___x_2135_ = lean_box(0);
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
                    v___x_2142_ = lean_unsigned_to_nat(0);
                    v___x_2143_ = lean_nat_dec_eq(v___x_2141_, v___x_2142_);
                    if v___x_2143_ == 0 {
                        v___x_2144_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once), _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
                        v___x_2145_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_2144_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_);
                        v_a_2146_ = lean_ctor_get(v___x_2145_, 0);
                        v_isSharedCheck_2153_ = (!lean_is_exclusive(v___x_2145_)) as u8;
                        if v_isSharedCheck_2153_ == 0 {
                            v___x_2148_ = v___x_2145_;
                            v_isShared_2149_ = v_isSharedCheck_2153_;
                            state = 14;
                            continue;
                        } else {
                            lean_inc(v_a_2146_);
                            lean_dec(v___x_2145_);
                            v___x_2148_ = lean_box(0);
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
                v___x_2060_ = lean_box((v___x_2059_) as usize);
                v___x_2061_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2061_, 0, v___x_2060_);
                return v___x_2061_;
            }
            2 => {
                v___x_2063_ = 4;
                v___x_2064_ = lean_box((v___x_2063_) as usize);
                v___x_2065_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2065_, 0, v___x_2064_);
                return v___x_2065_;
            }
            3 => {
                v___x_2067_ = 3;
                v___x_2068_ = lean_box((v___x_2067_) as usize);
                v___x_2069_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2069_, 0, v___x_2068_);
                return v___x_2069_;
            }
            4 => {
                v___x_2071_ = 1;
                v___x_2072_ = lean_box((v___x_2071_) as usize);
                v___x_2073_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2073_, 0, v___x_2072_);
                return v___x_2073_;
            }
            5 => {
                v___x_2075_ = 0;
                v___x_2076_ = lean_box((v___x_2075_) as usize);
                v___x_2077_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2077_, 0, v___x_2076_);
                return v___x_2077_;
            }
            6 => {
                if v_isShared_2097_ == 0 {
                    v___x_2099_ = v___x_2096_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2100_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2100_, 0, v_a_2094_);
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
                    v_reuseFailAlloc_2113_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2113_, 0, v_a_2107_);
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
                    v_reuseFailAlloc_2126_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_a_2120_);
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
                    v_reuseFailAlloc_2139_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_a_2133_);
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
                    v_reuseFailAlloc_2152_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_a_2146_);
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
    mut v_ctor_2154_: *mut LeanObject,
    mut v_args_2155_: *mut LeanObject,
    mut v___y_2156_: *mut LeanObject,
    mut v___y_2157_: *mut LeanObject,
    mut v___y_2158_: *mut LeanObject,
    mut v___y_2159_: *mut LeanObject,
    mut v___y_2160_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2161_: *mut LeanObject = core::ptr::null_mut();
    v_res_2161_ = l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr___lam__0(
        v_ctor_2154_,
        v_args_2155_,
        v___y_2156_,
        v___y_2157_,
        v___y_2158_,
        v___y_2159_,
    );
    lean_dec(v___y_2159_);
    lean_dec_ref(v___y_2158_);
    lean_dec(v___y_2157_);
    lean_dec_ref(v___y_2156_);
    lean_dec_ref(v_args_2155_);
    lean_dec_ref(v_ctor_2154_);
    return v_res_2161_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr(
    mut v_a_2163_: *mut LeanObject,
    mut v_a_2164_: *mut LeanObject,
    mut v_a_2165_: *mut LeanObject,
    mut v_a_2166_: *mut LeanObject,
    mut v_a_2167_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_2172_: *mut LeanObject,
    mut v_a_2173_: *mut LeanObject,
    mut v_a_2174_: *mut LeanObject,
    mut v_a_2175_: *mut LeanObject,
    mut v_a_2176_: *mut LeanObject,
    mut v_a_2177_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2178_: *mut LeanObject = core::ptr::null_mut();
    v_res_2178_ = l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr(
        v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_,
    );
    lean_dec(v_a_2176_);
    lean_dec_ref(v_a_2175_);
    lean_dec(v_a_2174_);
    lean_dec_ref(v_a_2173_);
    return v_res_2178_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__1()
-> *mut LeanObject {
    let mut v___x_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut LeanObject = core::ptr::null_mut();
    v___x_2180_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__1_once
        ),
        _init_l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode___closed__1,
    );
    v___x_2181_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2181_, 0, v___x_2180_);
    return v___x_2181_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__2()
-> *mut LeanObject {
    let mut v___x_2182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut LeanObject = core::ptr::null_mut();
    v___x_2182_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__1_once
        ),
        _init_l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__1,
    );
    v___x_2183_ = l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__0;
    v___x_2184_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2184_, 0, v___x_2183_);
    lean_ctor_set(v___x_2184_, 1, v___x_2182_);
    return v___x_2184_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode() -> *mut LeanObject {
    let mut v___x_2185_: *mut LeanObject = core::ptr::null_mut();
    v___x_2185_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__2),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__2_once
        ),
        _init_l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode___closed__2,
    );
    return v___x_2185_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__4()
-> *mut LeanObject {
    let mut v___x_2191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut LeanObject = core::ptr::null_mut();
    v___x_2191_ = lean_box(0);
    v___x_2192_ = l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__3;
    v___x_2193_ = l_Lean_mkConst(v___x_2192_, v___x_2191_);
    return v___x_2193_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0(
    mut v___x_2195_: *mut LeanObject,
    mut v___x_2196_: *mut LeanObject,
    mut v___x_2197_: *mut LeanObject,
    mut v_ctor_2198_: *mut LeanObject,
    mut v_args_2199_: *mut LeanObject,
    mut v___y_2200_: *mut LeanObject,
    mut v___y_2201_: *mut LeanObject,
    mut v___y_2202_: *mut LeanObject,
    mut v___y_2203_: *mut LeanObject,
    mut v___y_2204_: *mut LeanObject,
    mut v___y_2205_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: u8 = 0;
    let mut v___x_2209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: u8 = 0;
    let mut v___x_2211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: u8 = 0;
    let mut v___x_2213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2227_: u8 = 0;
    let mut v_fst_2228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2232_: u8 = 0;
    let mut v___x_2233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2242_: u8 = 0;
    let mut v_isSharedCheck_2243_: u8 = 0;
    let mut v_a_2244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2247_: u8 = 0;
    let mut v___x_2249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2251_: u8 = 0;
    let mut v_a_2252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2255_: u8 = 0;
    let mut v___x_2257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2259_: u8 = 0;
    let mut v___x_2260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2273_: u8 = 0;
    let mut v_fst_2274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2278_: u8 = 0;
    let mut v___x_2279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2288_: u8 = 0;
    let mut v_isSharedCheck_2289_: u8 = 0;
    let mut v_a_2290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2293_: u8 = 0;
    let mut v___x_2295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2297_: u8 = 0;
    let mut v_a_2298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2301_: u8 = 0;
    let mut v___x_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2305_: u8 = 0;
    let mut v___x_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2311_: u8 = 0;
    let mut v___x_2312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2319_: u8 = 0;
    let mut v_unused_2320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2324_: u8 = 0;
    let mut v___x_2326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2327_: *mut LeanObject = core::ptr::null_mut();
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
                            lean_dec_ref(v___x_2197_);
                            lean_dec_ref(v___x_2196_);
                            lean_dec_ref(v___x_2195_);
                            v___x_2213_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm_spec__0___redArg();
                            return v___x_2213_;
                        } else {
                            v___x_2214_ = l_Lean_Name_mkStr4(
                                v___x_2195_,
                                v___x_2196_,
                                v___x_2197_,
                                v___x_2211_,
                            );
                            v___x_2215_ = lean_unsigned_to_nat(1);
                            lean_inc(v___x_2214_);
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
                            if lean_obj_tag(v___x_2216_) == 0 {
                                lean_dec_ref_known(v___x_2216_, 1);
                                v___x_2217_ = lean_box(0);
                                v___x_2218_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__4), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__4_once), _init_l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__4);
                                v___x_2219_ = l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__5;
                                v___x_2220_ = lean_box(0);
                                v___x_2221_ = lean_unsigned_to_nat(0);
                                v___x_2222_ =
                                    lean_array_get_borrowed(v___x_2220_, v_args_2199_, v___x_2221_);
                                lean_inc(v___x_2222_);
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
                                if lean_obj_tag(v___x_2223_) == 0 {
                                    v_a_2224_ = lean_ctor_get(v___x_2223_, 0);
                                    v_isSharedCheck_2243_ = (!lean_is_exclusive(v___x_2223_)) as u8;
                                    if v_isSharedCheck_2243_ == 0 {
                                        v___x_2226_ = v___x_2223_;
                                        v_isShared_2227_ = v_isSharedCheck_2243_;
                                        state = 1;
                                        continue;
                                    } else {
                                        lean_inc(v_a_2224_);
                                        lean_dec(v___x_2223_);
                                        v___x_2226_ = lean_box(0);
                                        v_isShared_2227_ = v_isSharedCheck_2243_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v___x_2214_);
                                    v_a_2244_ = lean_ctor_get(v___x_2223_, 0);
                                    v_isSharedCheck_2251_ = (!lean_is_exclusive(v___x_2223_)) as u8;
                                    if v_isSharedCheck_2251_ == 0 {
                                        v___x_2246_ = v___x_2223_;
                                        v_isShared_2247_ = v_isSharedCheck_2251_;
                                        state = 5;
                                        continue;
                                    } else {
                                        lean_inc(v_a_2244_);
                                        lean_dec(v___x_2223_);
                                        v___x_2246_ = lean_box(0);
                                        v_isShared_2247_ = v_isSharedCheck_2251_;
                                        state = 5;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v___x_2214_);
                                v_a_2252_ = lean_ctor_get(v___x_2216_, 0);
                                v_isSharedCheck_2259_ = (!lean_is_exclusive(v___x_2216_)) as u8;
                                if v_isSharedCheck_2259_ == 0 {
                                    v___x_2254_ = v___x_2216_;
                                    v_isShared_2255_ = v_isSharedCheck_2259_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_2252_);
                                    lean_dec(v___x_2216_);
                                    v___x_2254_ = lean_box(0);
                                    v_isShared_2255_ = v_isSharedCheck_2259_;
                                    state = 7;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v___x_2260_ =
                            l_Lean_Name_mkStr4(v___x_2195_, v___x_2196_, v___x_2197_, v___x_2209_);
                        v___x_2261_ = lean_unsigned_to_nat(1);
                        lean_inc(v___x_2260_);
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
                        if lean_obj_tag(v___x_2262_) == 0 {
                            lean_dec_ref_known(v___x_2262_, 1);
                            v___x_2263_ = lean_box(0);
                            v___x_2264_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__4), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__4_once), _init_l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__4);
                            v___x_2265_ = l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___lam__0___closed__5;
                            v___x_2266_ = lean_box(0);
                            v___x_2267_ = lean_unsigned_to_nat(0);
                            v___x_2268_ =
                                lean_array_get_borrowed(v___x_2266_, v_args_2199_, v___x_2267_);
                            lean_inc(v___x_2268_);
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
                            if lean_obj_tag(v___x_2269_) == 0 {
                                v_a_2270_ = lean_ctor_get(v___x_2269_, 0);
                                v_isSharedCheck_2289_ = (!lean_is_exclusive(v___x_2269_)) as u8;
                                if v_isSharedCheck_2289_ == 0 {
                                    v___x_2272_ = v___x_2269_;
                                    v_isShared_2273_ = v_isSharedCheck_2289_;
                                    state = 9;
                                    continue;
                                } else {
                                    lean_inc(v_a_2270_);
                                    lean_dec(v___x_2269_);
                                    v___x_2272_ = lean_box(0);
                                    v_isShared_2273_ = v_isSharedCheck_2289_;
                                    state = 9;
                                    continue;
                                }
                            } else {
                                lean_dec(v___x_2260_);
                                v_a_2290_ = lean_ctor_get(v___x_2269_, 0);
                                v_isSharedCheck_2297_ = (!lean_is_exclusive(v___x_2269_)) as u8;
                                if v_isSharedCheck_2297_ == 0 {
                                    v___x_2292_ = v___x_2269_;
                                    v_isShared_2293_ = v_isSharedCheck_2297_;
                                    state = 13;
                                    continue;
                                } else {
                                    lean_inc(v_a_2290_);
                                    lean_dec(v___x_2269_);
                                    v___x_2292_ = lean_box(0);
                                    v_isShared_2293_ = v_isSharedCheck_2297_;
                                    state = 13;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v___x_2260_);
                            v_a_2298_ = lean_ctor_get(v___x_2262_, 0);
                            v_isSharedCheck_2305_ = (!lean_is_exclusive(v___x_2262_)) as u8;
                            if v_isSharedCheck_2305_ == 0 {
                                v___x_2300_ = v___x_2262_;
                                v_isShared_2301_ = v_isSharedCheck_2305_;
                                state = 15;
                                continue;
                            } else {
                                lean_inc(v_a_2298_);
                                lean_dec(v___x_2262_);
                                v___x_2300_ = lean_box(0);
                                v_isShared_2301_ = v_isSharedCheck_2305_;
                                state = 15;
                                continue;
                            }
                        }
                    }
                } else {
                    v___x_2306_ =
                        l_Lean_Name_mkStr4(v___x_2195_, v___x_2196_, v___x_2197_, v___x_2207_);
                    v___x_2307_ = lean_unsigned_to_nat(0);
                    lean_inc(v___x_2306_);
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
                    if lean_obj_tag(v___x_2308_) == 0 {
                        v_isSharedCheck_2319_ = (!lean_is_exclusive(v___x_2308_)) as u8;
                        if v_isSharedCheck_2319_ == 0 {
                            v_unused_2320_ = lean_ctor_get(v___x_2308_, 0);
                            lean_dec(v_unused_2320_);
                            v___x_2310_ = v___x_2308_;
                            v_isShared_2311_ = v_isSharedCheck_2319_;
                            state = 17;
                            continue;
                        } else {
                            lean_dec(v___x_2308_);
                            v___x_2310_ = lean_box(0);
                            v_isShared_2311_ = v_isSharedCheck_2319_;
                            state = 17;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_2306_);
                        v_a_2321_ = lean_ctor_get(v___x_2308_, 0);
                        v_isSharedCheck_2328_ = (!lean_is_exclusive(v___x_2308_)) as u8;
                        if v_isSharedCheck_2328_ == 0 {
                            v___x_2323_ = v___x_2308_;
                            v_isShared_2324_ = v_isSharedCheck_2328_;
                            state = 19;
                            continue;
                        } else {
                            lean_inc(v_a_2321_);
                            lean_dec(v___x_2308_);
                            v___x_2323_ = lean_box(0);
                            v_isShared_2324_ = v_isSharedCheck_2328_;
                            state = 19;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_2228_ = lean_ctor_get(v_a_2224_, 0);
                v_snd_2229_ = lean_ctor_get(v_a_2224_, 1);
                v_isSharedCheck_2242_ = (!lean_is_exclusive(v_a_2224_)) as u8;
                if v_isSharedCheck_2242_ == 0 {
                    v___x_2231_ = v_a_2224_;
                    v_isShared_2232_ = v_isSharedCheck_2242_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_2229_);
                    lean_inc(v_fst_2228_);
                    lean_dec(v_a_2224_);
                    v___x_2231_ = lean_box(0);
                    v_isShared_2232_ = v_isSharedCheck_2242_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2233_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2233_, 0, v_fst_2228_);
                v___x_2234_ = l_Lean_Expr_const___override(v___x_2214_, v___x_2217_);
                v___x_2235_ = l_Lean_Expr_app___override(v___x_2234_, v_snd_2229_);
                if v_isShared_2232_ == 0 {
                    lean_ctor_set(v___x_2231_, 1, v___x_2235_);
                    lean_ctor_set(v___x_2231_, 0, v___x_2233_);
                    v___x_2237_ = v___x_2231_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2241_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2241_, 0, v___x_2233_);
                    lean_ctor_set(v_reuseFailAlloc_2241_, 1, v___x_2235_);
                    v___x_2237_ = v_reuseFailAlloc_2241_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2227_ == 0 {
                    lean_ctor_set(v___x_2226_, 0, v___x_2237_);
                    v___x_2239_ = v___x_2226_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2240_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2240_, 0, v___x_2237_);
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
                    v_reuseFailAlloc_2250_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2250_, 0, v_a_2244_);
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
                    v_reuseFailAlloc_2258_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2258_, 0, v_a_2252_);
                    v___x_2257_ = v_reuseFailAlloc_2258_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2257_;
            }
            9 => {
                v_fst_2274_ = lean_ctor_get(v_a_2270_, 0);
                v_snd_2275_ = lean_ctor_get(v_a_2270_, 1);
                v_isSharedCheck_2288_ = (!lean_is_exclusive(v_a_2270_)) as u8;
                if v_isSharedCheck_2288_ == 0 {
                    v___x_2277_ = v_a_2270_;
                    v_isShared_2278_ = v_isSharedCheck_2288_;
                    state = 10;
                    continue;
                } else {
                    lean_inc(v_snd_2275_);
                    lean_inc(v_fst_2274_);
                    lean_dec(v_a_2270_);
                    v___x_2277_ = lean_box(0);
                    v_isShared_2278_ = v_isSharedCheck_2288_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_2279_ = lean_alloc_ctor(2, 1, (0) as u32);
                lean_ctor_set(v___x_2279_, 0, v_fst_2274_);
                v___x_2280_ = l_Lean_Expr_const___override(v___x_2260_, v___x_2263_);
                v___x_2281_ = l_Lean_Expr_app___override(v___x_2280_, v_snd_2275_);
                if v_isShared_2278_ == 0 {
                    lean_ctor_set(v___x_2277_, 1, v___x_2281_);
                    lean_ctor_set(v___x_2277_, 0, v___x_2279_);
                    v___x_2283_ = v___x_2277_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2287_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2287_, 0, v___x_2279_);
                    lean_ctor_set(v_reuseFailAlloc_2287_, 1, v___x_2281_);
                    v___x_2283_ = v_reuseFailAlloc_2287_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_2273_ == 0 {
                    lean_ctor_set(v___x_2272_, 0, v___x_2283_);
                    v___x_2285_ = v___x_2272_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2286_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2286_, 0, v___x_2283_);
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
                    v_reuseFailAlloc_2296_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2296_, 0, v_a_2290_);
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
                    v_reuseFailAlloc_2304_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2304_, 0, v_a_2298_);
                    v___x_2303_ = v_reuseFailAlloc_2304_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2303_;
            }
            17 => {
                v___x_2312_ = lean_box(0);
                v___x_2313_ = lean_box(0);
                v___x_2314_ = l_Lean_Expr_const___override(v___x_2306_, v___x_2313_);
                v___x_2315_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2315_, 0, v___x_2312_);
                lean_ctor_set(v___x_2315_, 1, v___x_2314_);
                if v_isShared_2311_ == 0 {
                    lean_ctor_set(v___x_2310_, 0, v___x_2315_);
                    v___x_2317_ = v___x_2310_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2318_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2318_, 0, v___x_2315_);
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
                    v_reuseFailAlloc_2327_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_a_2321_);
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
    mut v___x_2329_: *mut LeanObject,
    mut v___x_2330_: *mut LeanObject,
    mut v___x_2331_: *mut LeanObject,
    mut v_ctor_2332_: *mut LeanObject,
    mut v_args_2333_: *mut LeanObject,
    mut v___y_2334_: *mut LeanObject,
    mut v___y_2335_: *mut LeanObject,
    mut v___y_2336_: *mut LeanObject,
    mut v___y_2337_: *mut LeanObject,
    mut v___y_2338_: *mut LeanObject,
    mut v___y_2339_: *mut LeanObject,
    mut v___y_2340_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2341_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_2339_);
    lean_dec_ref(v___y_2338_);
    lean_dec(v___y_2337_);
    lean_dec_ref(v___y_2336_);
    lean_dec(v___y_2335_);
    lean_dec_ref(v___y_2334_);
    lean_dec_ref(v_args_2333_);
    lean_dec_ref(v_ctor_2332_);
    return v_res_2341_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm(
    mut v_a_2351_: *mut LeanObject,
    mut v_a_2352_: *mut LeanObject,
    mut v_a_2353_: *mut LeanObject,
    mut v_a_2354_: *mut LeanObject,
    mut v_a_2355_: *mut LeanObject,
    mut v_a_2356_: *mut LeanObject,
    mut v_a_2357_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_2362_: *mut LeanObject,
    mut v_a_2363_: *mut LeanObject,
    mut v_a_2364_: *mut LeanObject,
    mut v_a_2365_: *mut LeanObject,
    mut v_a_2366_: *mut LeanObject,
    mut v_a_2367_: *mut LeanObject,
    mut v_a_2368_: *mut LeanObject,
    mut v_a_2369_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2370_: *mut LeanObject = core::ptr::null_mut();
    v_res_2370_ = l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm(
        v_a_2362_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_,
    );
    lean_dec(v_a_2368_);
    lean_dec_ref(v_a_2367_);
    lean_dec(v_a_2366_);
    lean_dec_ref(v_a_2365_);
    lean_dec(v_a_2364_);
    lean_dec_ref(v_a_2363_);
    return v_res_2370_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__1() -> *mut LeanObject
{
    let mut v___x_2372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut LeanObject = core::ptr::null_mut();
    v___x_2372_ = lean_box(0);
    v___x_2373_ = l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm___closed__2;
    v___x_2374_ = l_Lean_Expr_const___override(v___x_2373_, v___x_2372_);
    return v___x_2374_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__2() -> *mut LeanObject
{
    let mut v___x_2375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut LeanObject = core::ptr::null_mut();
    v___x_2375_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__1_once),
        _init_l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__1,
    );
    v___x_2376_ = l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__0;
    v___x_2377_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2377_, 0, v___x_2376_);
    lean_ctor_set(v___x_2377_, 1, v___x_2375_);
    return v___x_2377_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_instEvalTermOccurrences() -> *mut LeanObject {
    let mut v___x_2378_: *mut LeanObject = core::ptr::null_mut();
    v___x_2378_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__2_once),
        _init_l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__2,
    );
    return v___x_2378_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___lam__0___closed__0()
-> *mut LeanObject {
    let mut v___x_2379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut LeanObject = core::ptr::null_mut();
    v___x_2379_ = l_Lean_Elab_ConfigEval_EvalExpr_instNat;
    v___x_2380_ = l_Lean_Elab_ConfigEval_EvalExpr_instList___redArg(v___x_2379_);
    return v___x_2380_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___lam__0(
    mut v_ctor_2381_: *mut LeanObject,
    mut v_args_2382_: *mut LeanObject,
    mut v___y_2383_: *mut LeanObject,
    mut v___y_2384_: *mut LeanObject,
    mut v___y_2385_: *mut LeanObject,
    mut v___y_2386_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_evalExpr_2390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2398_: u8 = 0;
    let mut v___x_2399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2403_: u8 = 0;
    let mut v_a_2404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2407_: u8 = 0;
    let mut v___x_2409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2411_: u8 = 0;
    let mut v___x_2413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_evalExpr_2414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2422_: u8 = 0;
    let mut v___x_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2427_: u8 = 0;
    let mut v_a_2428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2431_: u8 = 0;
    let mut v___x_2433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2435_: u8 = 0;
    let mut v___x_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: u8 = 0;
    let mut v___x_2441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: u8 = 0;
    let mut v___x_2443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: u8 = 0;
    let mut v___x_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: u8 = 0;
    let mut v___x_2449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2454_: u8 = 0;
    let mut v___x_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2458_: u8 = 0;
    let mut v___x_2459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: u8 = 0;
    let mut v___x_2462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2467_: u8 = 0;
    let mut v___x_2469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2471_: u8 = 0;
    let mut v___x_2472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: u8 = 0;
    let mut v___x_2475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2480_: u8 = 0;
    let mut v___x_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2483_: *mut LeanObject = core::ptr::null_mut();
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
                            v___x_2447_ = lean_unsigned_to_nat(1);
                            v___x_2448_ = lean_nat_dec_eq(v___x_2446_, v___x_2447_);
                            if v___x_2448_ == 0 {
                                v___x_2449_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once), _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
                                v___x_2450_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_2449_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
                                v_a_2451_ = lean_ctor_get(v___x_2450_, 0);
                                v_isSharedCheck_2458_ = (!lean_is_exclusive(v___x_2450_)) as u8;
                                if v_isSharedCheck_2458_ == 0 {
                                    v___x_2453_ = v___x_2450_;
                                    v_isShared_2454_ = v_isSharedCheck_2458_;
                                    state = 12;
                                    continue;
                                } else {
                                    lean_inc(v_a_2451_);
                                    lean_dec(v___x_2450_);
                                    v___x_2453_ = lean_box(0);
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
                        v___x_2460_ = lean_unsigned_to_nat(1);
                        v___x_2461_ = lean_nat_dec_eq(v___x_2459_, v___x_2460_);
                        if v___x_2461_ == 0 {
                            v___x_2462_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once), _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
                            v___x_2463_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_2462_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
                            v_a_2464_ = lean_ctor_get(v___x_2463_, 0);
                            v_isSharedCheck_2471_ = (!lean_is_exclusive(v___x_2463_)) as u8;
                            if v_isSharedCheck_2471_ == 0 {
                                v___x_2466_ = v___x_2463_;
                                v_isShared_2467_ = v_isSharedCheck_2471_;
                                state = 14;
                                continue;
                            } else {
                                lean_inc(v_a_2464_);
                                lean_dec(v___x_2463_);
                                v___x_2466_ = lean_box(0);
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
                    v___x_2473_ = lean_unsigned_to_nat(0);
                    v___x_2474_ = lean_nat_dec_eq(v___x_2472_, v___x_2473_);
                    if v___x_2474_ == 0 {
                        v___x_2475_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1_once), _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr___lam__0___closed__1);
                        v___x_2476_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr_spec__1___redArg(v___x_2475_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
                        v_a_2477_ = lean_ctor_get(v___x_2476_, 0);
                        v_isSharedCheck_2484_ = (!lean_is_exclusive(v___x_2476_)) as u8;
                        if v_isSharedCheck_2484_ == 0 {
                            v___x_2479_ = v___x_2476_;
                            v_isShared_2480_ = v_isSharedCheck_2484_;
                            state = 16;
                            continue;
                        } else {
                            lean_inc(v_a_2477_);
                            lean_dec(v___x_2476_);
                            v___x_2479_ = lean_box(0);
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
                v___x_2389_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___lam__0___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___lam__0___closed__0_once), _init_l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___lam__0___closed__0);
                v_evalExpr_2390_ = lean_ctor_get(v___x_2389_, 0);
                v___x_2391_ = l_Lean_instInhabitedExpr;
                v___x_2392_ = lean_unsigned_to_nat(0);
                v___x_2393_ = lean_array_get_borrowed(v___x_2391_, v_args_2382_, v___x_2392_);
                lean_inc_ref(v_evalExpr_2390_);
                lean_inc(v___y_2386_);
                lean_inc_ref(v___y_2385_);
                lean_inc(v___y_2384_);
                lean_inc_ref(v___y_2383_);
                lean_inc(v___x_2393_);
                v___x_2394_ = lean_apply_6(
                    v_evalExpr_2390_,
                    v___x_2393_,
                    v___y_2383_,
                    v___y_2384_,
                    v___y_2385_,
                    v___y_2386_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_2394_) == 0 {
                    v_a_2395_ = lean_ctor_get(v___x_2394_, 0);
                    v_isSharedCheck_2403_ = (!lean_is_exclusive(v___x_2394_)) as u8;
                    if v_isSharedCheck_2403_ == 0 {
                        v___x_2397_ = v___x_2394_;
                        v_isShared_2398_ = v_isSharedCheck_2403_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_2395_);
                        lean_dec(v___x_2394_);
                        v___x_2397_ = lean_box(0);
                        v_isShared_2398_ = v_isSharedCheck_2403_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_2404_ = lean_ctor_get(v___x_2394_, 0);
                    v_isSharedCheck_2411_ = (!lean_is_exclusive(v___x_2394_)) as u8;
                    if v_isSharedCheck_2411_ == 0 {
                        v___x_2406_ = v___x_2394_;
                        v_isShared_2407_ = v_isSharedCheck_2411_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_2404_);
                        lean_dec(v___x_2394_);
                        v___x_2406_ = lean_box(0);
                        v_isShared_2407_ = v_isSharedCheck_2411_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2399_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2399_, 0, v_a_2395_);
                if v_isShared_2398_ == 0 {
                    lean_ctor_set(v___x_2397_, 0, v___x_2399_);
                    v___x_2401_ = v___x_2397_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2402_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2402_, 0, v___x_2399_);
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
                    v_reuseFailAlloc_2410_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2410_, 0, v_a_2404_);
                    v___x_2409_ = v_reuseFailAlloc_2410_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2409_;
            }
            6 => {
                v___x_2413_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___lam__0___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___lam__0___closed__0_once), _init_l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___lam__0___closed__0);
                v_evalExpr_2414_ = lean_ctor_get(v___x_2413_, 0);
                v___x_2415_ = l_Lean_instInhabitedExpr;
                v___x_2416_ = lean_unsigned_to_nat(0);
                v___x_2417_ = lean_array_get_borrowed(v___x_2415_, v_args_2382_, v___x_2416_);
                lean_inc_ref(v_evalExpr_2414_);
                lean_inc(v___y_2386_);
                lean_inc_ref(v___y_2385_);
                lean_inc(v___y_2384_);
                lean_inc_ref(v___y_2383_);
                lean_inc(v___x_2417_);
                v___x_2418_ = lean_apply_6(
                    v_evalExpr_2414_,
                    v___x_2417_,
                    v___y_2383_,
                    v___y_2384_,
                    v___y_2385_,
                    v___y_2386_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_2418_) == 0 {
                    v_a_2419_ = lean_ctor_get(v___x_2418_, 0);
                    v_isSharedCheck_2427_ = (!lean_is_exclusive(v___x_2418_)) as u8;
                    if v_isSharedCheck_2427_ == 0 {
                        v___x_2421_ = v___x_2418_;
                        v_isShared_2422_ = v_isSharedCheck_2427_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_2419_);
                        lean_dec(v___x_2418_);
                        v___x_2421_ = lean_box(0);
                        v_isShared_2422_ = v_isSharedCheck_2427_;
                        state = 7;
                        continue;
                    }
                } else {
                    v_a_2428_ = lean_ctor_get(v___x_2418_, 0);
                    v_isSharedCheck_2435_ = (!lean_is_exclusive(v___x_2418_)) as u8;
                    if v_isSharedCheck_2435_ == 0 {
                        v___x_2430_ = v___x_2418_;
                        v_isShared_2431_ = v_isSharedCheck_2435_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_2428_);
                        lean_dec(v___x_2418_);
                        v___x_2430_ = lean_box(0);
                        v_isShared_2431_ = v_isSharedCheck_2435_;
                        state = 9;
                        continue;
                    }
                }
            }
            7 => {
                v___x_2423_ = lean_alloc_ctor(2, 1, (0) as u32);
                lean_ctor_set(v___x_2423_, 0, v_a_2419_);
                if v_isShared_2422_ == 0 {
                    lean_ctor_set(v___x_2421_, 0, v___x_2423_);
                    v___x_2425_ = v___x_2421_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2426_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2426_, 0, v___x_2423_);
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
                    v_reuseFailAlloc_2434_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2434_, 0, v_a_2428_);
                    v___x_2433_ = v_reuseFailAlloc_2434_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2433_;
            }
            11 => {
                v___x_2437_ = lean_box(0);
                v___x_2438_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2438_, 0, v___x_2437_);
                return v___x_2438_;
            }
            12 => {
                if v_isShared_2454_ == 0 {
                    v___x_2456_ = v___x_2453_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2457_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_a_2451_);
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
                    v_reuseFailAlloc_2470_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2470_, 0, v_a_2464_);
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
                    v_reuseFailAlloc_2483_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_a_2477_);
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
    mut v_ctor_2485_: *mut LeanObject,
    mut v_args_2486_: *mut LeanObject,
    mut v___y_2487_: *mut LeanObject,
    mut v___y_2488_: *mut LeanObject,
    mut v___y_2489_: *mut LeanObject,
    mut v___y_2490_: *mut LeanObject,
    mut v___y_2491_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2492_: *mut LeanObject = core::ptr::null_mut();
    v_res_2492_ = l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr___lam__0(
        v_ctor_2485_,
        v_args_2486_,
        v___y_2487_,
        v___y_2488_,
        v___y_2489_,
        v___y_2490_,
    );
    lean_dec(v___y_2490_);
    lean_dec_ref(v___y_2489_);
    lean_dec(v___y_2488_);
    lean_dec_ref(v___y_2487_);
    lean_dec_ref(v_args_2486_);
    lean_dec_ref(v_ctor_2485_);
    return v_res_2492_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr(
    mut v_a_2494_: *mut LeanObject,
    mut v_a_2495_: *mut LeanObject,
    mut v_a_2496_: *mut LeanObject,
    mut v_a_2497_: *mut LeanObject,
    mut v_a_2498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_2503_: *mut LeanObject,
    mut v_a_2504_: *mut LeanObject,
    mut v_a_2505_: *mut LeanObject,
    mut v_a_2506_: *mut LeanObject,
    mut v_a_2507_: *mut LeanObject,
    mut v_a_2508_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2509_: *mut LeanObject = core::ptr::null_mut();
    v_res_2509_ = l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr(
        v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_,
    );
    lean_dec(v_a_2507_);
    lean_dec_ref(v_a_2506_);
    lean_dec(v_a_2505_);
    lean_dec_ref(v_a_2504_);
    return v_res_2509_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__1() -> *mut LeanObject
{
    let mut v___x_2511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut LeanObject = core::ptr::null_mut();
    v___x_2511_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__1_once),
        _init_l_Lean_Elab_ConfigEval_instEvalTermOccurrences___closed__1,
    );
    v___x_2512_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2512_, 0, v___x_2511_);
    return v___x_2512_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__2() -> *mut LeanObject
{
    let mut v___x_2513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut LeanObject = core::ptr::null_mut();
    v___x_2513_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__1_once),
        _init_l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__1,
    );
    v___x_2514_ = l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__0;
    v___x_2515_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2515_, 0, v___x_2514_);
    lean_ctor_set(v___x_2515_, 1, v___x_2513_);
    return v___x_2515_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_instEvalExprOccurrences() -> *mut LeanObject {
    let mut v___x_2516_: *mut LeanObject = core::ptr::null_mut();
    v___x_2516_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__2_once),
        _init_l_Lean_Elab_ConfigEval_instEvalExprOccurrences___closed__2,
    );
    return v___x_2516_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_ConfigEval_MetaInstances(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_ConfigEval_Commands(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_ConfigEval_Instances(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_ConfigEval_DeriveEvalTerm(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_ConfigEval_DeriveEvalExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals =
        _init_l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals();
    lean_mark_persistent(l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals);
    l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals =
        _init_l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals();
    lean_mark_persistent(l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals);
    l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode =
        _init_l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode();
    lean_mark_persistent(l_Lean_Elab_ConfigEval_instEvalTermEtaStructMode);
    l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode =
        _init_l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode();
    lean_mark_persistent(l_Lean_Elab_ConfigEval_instEvalExprEtaStructMode);
    l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode =
        _init_l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode();
    lean_mark_persistent(l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode);
    l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode =
        _init_l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode();
    lean_mark_persistent(l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode);
    l_Lean_Elab_ConfigEval_instEvalTermOccurrences =
        _init_l_Lean_Elab_ConfigEval_instEvalTermOccurrences();
    lean_mark_persistent(l_Lean_Elab_ConfigEval_instEvalTermOccurrences);
    l_Lean_Elab_ConfigEval_instEvalExprOccurrences =
        _init_l_Lean_Elab_ConfigEval_instEvalExprOccurrences();
    lean_mark_persistent(l_Lean_Elab_ConfigEval_instEvalExprOccurrences);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_ConfigEval_MetaInstances(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_ConfigEval_MetaInstances(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_ConfigEval_Commands(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_ConfigEval_Instances(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_ConfigEval_DeriveEvalTerm(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_ConfigEval_DeriveEvalExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_ConfigEval_MetaInstances(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_ConfigEval_MetaInstances(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_ConfigEval_MetaInstances(builtin);
}
