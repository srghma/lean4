// Lean compiler output
// Module: Lean.Elab.Tactic.Calc
// Imports: Lean.Elab.Calc Lean.Elab.Tactic.ElabTerm
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr2, l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind,
    l_Lean_replaceRef,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::DocString::Extension::l_Lean_addBuiltinDocString;
use crate::r#gen::Lean::Elab::Calc::{
    initialize_Lean_Elab_Calc, l_Lean_Elab_Term_elabCalcSteps,
    l_Lean_Elab_Term_getCalcRelation_x3f___redArg, l_Lean_Elab_Term_mkCalcStepViews,
    l_Lean_Elab_Term_mkCalcTrans, l_Lean_Elab_Term_throwCalcFailure___redArg,
    runtime_initialize_Lean_Elab_Calc,
};
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    l_Lean_Elab_Tactic_mkInitialTacticInfo, l_Lean_Elab_Tactic_pushGoals___redArg,
    l_Lean_Elab_Tactic_tacticElabAttribute,
};
use crate::r#gen::Lean::Elab::Tactic::ElabTerm::{
    initialize_Lean_Elab_Tactic_ElabTerm, l_Lean_Elab_Tactic_closeMainGoalUsing,
    l_Lean_Elab_Tactic_runTermElab___boxed, l_Lean_Elab_Tactic_withCollectingNewGoalsFrom,
    runtime_initialize_Lean_Elab_Tactic_ElabTerm,
};
use crate::r#gen::Lean::Elab::Term::TermElabM::{
    l_Lean_Elab_Term_ensureHasTypeWithErrorMsgs, l_Lean_Elab_Term_instInhabitedTermElabM,
};
use crate::r#gen::Lean::Exception::l_Lean_Exception_isInterrupt;
use crate::r#gen::Lean::Expr::{l_Lean_Expr_consumeMData, l_Lean_Expr_hasMVar, l_Lean_mkAppB};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Meta::Basic::l_Lean_Meta_isExprDefEq;
use crate::r#gen::Lean::Meta::Tactic::Util::l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar;
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::lean_imports_rs::Init::Prelude::{
    lean_mk_empty_array_with_capacity, lean_panic_fn_borrowed,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_panic___at___00Lean_Elab_Tactic_evalCalc_spec__2___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_panic___at___00Lean_Elab_Tactic_evalCalc_spec__2___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_evalCalc___lam__2___closed__0_value: crate::leanh::LeanStringObject<
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
    m_data: [115, 116, 101, 112, 0],
};
static mut l_Lean_Elab_Tactic_evalCalc___lam__2___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalCalc___lam__2___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_evalCalc___lam__2___closed__1_value: crate::leanh::LeanStringObject<
    22,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 84, 97, 99, 116, 105, 99, 46, 67, 97, 108, 99, 0,
    ],
};
static mut l_Lean_Elab_Tactic_evalCalc___lam__2___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalCalc___lam__2___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_evalCalc___lam__2___closed__2_value: crate::leanh::LeanStringObject<
    26,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 84, 97, 99, 116, 105, 99, 46, 101, 118, 97, 108,
        67, 97, 108, 99, 0,
    ],
};
static mut l_Lean_Elab_Tactic_evalCalc___lam__2___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalCalc___lam__2___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_evalCalc___lam__2___closed__3_value: crate::leanh::LeanStringObject<
    34,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 34,
    m_capacity: 34,
    m_length: 33,
    m_data: [
        117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115,
        32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0,
    ],
};
static mut l_Lean_Elab_Tactic_evalCalc___lam__2___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalCalc___lam__2___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_evalCalc___lam__2___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_evalCalc___lam__2___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_evalCalc___closed__0_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Lean_Elab_Tactic_evalCalc___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalCalc___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_evalCalc___closed__1_value: crate::leanh::LeanStringObject<11> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [99, 97, 108, 99, 84, 97, 99, 116, 105, 99, 0],
    };
static mut l_Lean_Elab_Tactic_evalCalc___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalCalc___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_evalCalc___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalCalc___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_evalCalc___closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalCalc___closed__2_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalCalc___closed__1_value)
                as *mut crate::leanh::LeanObject,
            9158504355193797775 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_evalCalc___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalCalc___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_evalCalc___closed__3_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [99, 97, 108, 99, 83, 116, 101, 112, 115, 0],
    };
static mut l_Lean_Elab_Tactic_evalCalc___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalCalc___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_evalCalc___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalCalc___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_evalCalc___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalCalc___closed__4_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalCalc___closed__3_value)
                as *mut crate::leanh::LeanObject,
            11669652153185471091 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_evalCalc___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalCalc___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_evalCalc___closed__5_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [99, 97, 108, 99, 0],
    };
static mut l_Lean_Elab_Tactic_evalCalc___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalCalc___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_evalCalc___closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalCalc___closed__5_value)
                as *mut crate::leanh::LeanObject,
            6813867156380545898 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_evalCalc___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalCalc___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__2_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [101, 118, 97, 108, 67, 97, 108, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalCalc___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__0_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__1_value) as *mut crate::leanh::LeanObject,12733524109236233889 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__2_value) as *mut crate::leanh::LeanObject,14073051769863737386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_docString__3___closed__0_value: crate::leanh::LeanStringObject<48> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 48, m_capacity: 48, m_length: 47, m_data: [69, 108, 97, 98, 111, 114, 97, 116, 111, 114, 32, 102, 111, 114, 32, 116, 104, 101, 32, 96, 99, 97, 108, 99, 96, 32, 116, 97, 99, 116, 105, 99, 32, 109, 111, 100, 101, 32, 118, 97, 114, 105, 97, 110, 116, 46, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_docString__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_docString__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 15 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 34 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 25 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__0_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__1_value) as *mut crate::leanh::LeanObject,((( 25 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 15 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 15 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 12 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__3_value) as *mut crate::leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__4_value) as *mut crate::leanh::LeanObject,((( 12 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__6_value) as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_830_ = crate::leanh::lean_box(0);
    v___x_831_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_832_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_832_, 0, v___x_831_);
    crate::leanh::lean_ctor_set(v___x_832_, 1, v___x_830_);
    return v___x_832_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_834_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0___redArg___closed__0);
    v___x_835_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_835_, 0, v___x_834_);
    return v___x_835_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0___redArg___boxed(
    mut v___y_836_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_837_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0___redArg();
    return v_res_837_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0(
    mut v_00_u03b1_838_: *mut crate::leanh::LeanObject,
    mut v___y_839_: *mut crate::leanh::LeanObject,
    mut v___y_840_: *mut crate::leanh::LeanObject,
    mut v___y_841_: *mut crate::leanh::LeanObject,
    mut v___y_842_: *mut crate::leanh::LeanObject,
    mut v___y_843_: *mut crate::leanh::LeanObject,
    mut v___y_844_: *mut crate::leanh::LeanObject,
    mut v___y_845_: *mut crate::leanh::LeanObject,
    mut v___y_846_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_848_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0___redArg();
    return v___x_848_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0___boxed(
    mut v_00_u03b1_849_: *mut crate::leanh::LeanObject,
    mut v___y_850_: *mut crate::leanh::LeanObject,
    mut v___y_851_: *mut crate::leanh::LeanObject,
    mut v___y_852_: *mut crate::leanh::LeanObject,
    mut v___y_853_: *mut crate::leanh::LeanObject,
    mut v___y_854_: *mut crate::leanh::LeanObject,
    mut v___y_855_: *mut crate::leanh::LeanObject,
    mut v___y_856_: *mut crate::leanh::LeanObject,
    mut v___y_857_: *mut crate::leanh::LeanObject,
    mut v___y_858_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_859_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0(
        v_00_u03b1_849_,
        v___y_850_,
        v___y_851_,
        v___y_852_,
        v___y_853_,
        v___y_854_,
        v___y_855_,
        v___y_856_,
        v___y_857_,
    );
    crate::leanh::lean_dec(v___y_857_);
    crate::leanh::lean_dec_ref(v___y_856_);
    crate::leanh::lean_dec(v___y_855_);
    crate::leanh::lean_dec_ref(v___y_854_);
    crate::leanh::lean_dec(v___y_853_);
    crate::leanh::lean_dec_ref(v___y_852_);
    crate::leanh::lean_dec(v___y_851_);
    crate::leanh::lean_dec_ref(v___y_850_);
    return v_res_859_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalCalc_spec__1___redArg(
    mut v_e_860_: *mut crate::leanh::LeanObject,
    mut v___y_861_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_863_: u8 = 0;
    let mut v___x_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_877_: u8 = 0;
    let mut v___x_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_883_: u8 = 0;
    let mut v_unused_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_863_ = l_Lean_Expr_hasMVar(v_e_860_);
                if v___x_863_ == 0 {
                    v___x_864_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_864_, 0, v_e_860_);
                    return v___x_864_;
                } else {
                    v___x_865_ = lean_st_ref_get(v___y_861_);
                    v_mctx_866_ = crate::leanh::lean_ctor_get(v___x_865_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_866_);
                    crate::leanh::lean_dec(v___x_865_);
                    v___x_867_ = l_Lean_instantiateMVarsCore(v_mctx_866_, v_e_860_);
                    v_fst_868_ = crate::leanh::lean_ctor_get(v___x_867_, 0);
                    crate::leanh::lean_inc(v_fst_868_);
                    v_snd_869_ = crate::leanh::lean_ctor_get(v___x_867_, 1);
                    crate::leanh::lean_inc(v_snd_869_);
                    crate::leanh::lean_dec_ref(v___x_867_);
                    v___x_870_ = lean_st_ref_take(v___y_861_);
                    v_cache_871_ = crate::leanh::lean_ctor_get(v___x_870_, 1);
                    v_zetaDeltaFVarIds_872_ = crate::leanh::lean_ctor_get(v___x_870_, 2);
                    v_postponed_873_ = crate::leanh::lean_ctor_get(v___x_870_, 3);
                    v_diag_874_ = crate::leanh::lean_ctor_get(v___x_870_, 4);
                    v_isSharedCheck_883_ = (!crate::leanh::lean_is_exclusive(v___x_870_)) as u8;
                    if v_isSharedCheck_883_ == 0 {
                        v_unused_884_ = crate::leanh::lean_ctor_get(v___x_870_, 0);
                        crate::leanh::lean_dec(v_unused_884_);
                        v___x_876_ = v___x_870_;
                        v_isShared_877_ = v_isSharedCheck_883_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_874_);
                        crate::leanh::lean_inc(v_postponed_873_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_872_);
                        crate::leanh::lean_inc(v_cache_871_);
                        crate::leanh::lean_dec(v___x_870_);
                        v___x_876_ = crate::leanh::lean_box(0);
                        v_isShared_877_ = v_isSharedCheck_883_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_877_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_876_, 0, v_snd_869_);
                    v___x_879_ = v___x_876_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_882_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_882_, 0, v_snd_869_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_882_, 1, v_cache_871_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_882_, 2, v_zetaDeltaFVarIds_872_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_882_, 3, v_postponed_873_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_882_, 4, v_diag_874_);
                    v___x_879_ = v_reuseFailAlloc_882_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_880_ = lean_st_ref_set(v___y_861_, v___x_879_);
                v___x_881_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_881_, 0, v_fst_868_);
                return v___x_881_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalCalc_spec__1___redArg___boxed(
    mut v_e_885_: *mut crate::leanh::LeanObject,
    mut v___y_886_: *mut crate::leanh::LeanObject,
    mut v___y_887_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_888_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalCalc_spec__1___redArg(
        v_e_885_, v___y_886_,
    );
    crate::leanh::lean_dec(v___y_886_);
    return v_res_888_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalCalc_spec__1(
    mut v_e_889_: *mut crate::leanh::LeanObject,
    mut v___y_890_: *mut crate::leanh::LeanObject,
    mut v___y_891_: *mut crate::leanh::LeanObject,
    mut v___y_892_: *mut crate::leanh::LeanObject,
    mut v___y_893_: *mut crate::leanh::LeanObject,
    mut v___y_894_: *mut crate::leanh::LeanObject,
    mut v___y_895_: *mut crate::leanh::LeanObject,
    mut v___y_896_: *mut crate::leanh::LeanObject,
    mut v___y_897_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_899_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalCalc_spec__1___redArg(
        v_e_889_, v___y_895_,
    );
    return v___x_899_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalCalc_spec__1___boxed(
    mut v_e_900_: *mut crate::leanh::LeanObject,
    mut v___y_901_: *mut crate::leanh::LeanObject,
    mut v___y_902_: *mut crate::leanh::LeanObject,
    mut v___y_903_: *mut crate::leanh::LeanObject,
    mut v___y_904_: *mut crate::leanh::LeanObject,
    mut v___y_905_: *mut crate::leanh::LeanObject,
    mut v___y_906_: *mut crate::leanh::LeanObject,
    mut v___y_907_: *mut crate::leanh::LeanObject,
    mut v___y_908_: *mut crate::leanh::LeanObject,
    mut v___y_909_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_910_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalCalc_spec__1(
        v_e_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_,
        v___y_907_, v___y_908_,
    );
    crate::leanh::lean_dec(v___y_908_);
    crate::leanh::lean_dec_ref(v___y_907_);
    crate::leanh::lean_dec(v___y_906_);
    crate::leanh::lean_dec_ref(v___y_905_);
    crate::leanh::lean_dec(v___y_904_);
    crate::leanh::lean_dec_ref(v___y_903_);
    crate::leanh::lean_dec(v___y_902_);
    crate::leanh::lean_dec_ref(v___y_901_);
    return v_res_910_;
}
pub unsafe fn _init_l_panic___at___00Lean_Elab_Tactic_evalCalc_spec__2___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_911_ = l_Lean_Elab_Term_instInhabitedTermElabM(crate::leanh::lean_box(0));
    return v___x_911_;
}
pub unsafe fn l_panic___at___00Lean_Elab_Tactic_evalCalc_spec__2(
    mut v_msg_912_: *mut crate::leanh::LeanObject,
    mut v___y_913_: *mut crate::leanh::LeanObject,
    mut v___y_914_: *mut crate::leanh::LeanObject,
    mut v___y_915_: *mut crate::leanh::LeanObject,
    mut v___y_916_: *mut crate::leanh::LeanObject,
    mut v___y_917_: *mut crate::leanh::LeanObject,
    mut v___y_918_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_11008__overap_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_920_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_panic___at___00Lean_Elab_Tactic_evalCalc_spec__2___closed__0),
        core::ptr::addr_of_mut!(
            l_panic___at___00Lean_Elab_Tactic_evalCalc_spec__2___closed__0_once
        ),
        _init_l_panic___at___00Lean_Elab_Tactic_evalCalc_spec__2___closed__0,
    );
    v___x_11008__overap_921_ = lean_panic_fn_borrowed(v___x_920_, v_msg_912_);
    crate::leanh::lean_inc(v___y_918_);
    crate::leanh::lean_inc_ref(v___y_917_);
    crate::leanh::lean_inc(v___y_916_);
    crate::leanh::lean_inc_ref(v___y_915_);
    crate::leanh::lean_inc(v___y_914_);
    crate::leanh::lean_inc_ref(v___y_913_);
    v___x_922_ = crate::leanh::lean_apply_7(
        v___x_11008__overap_921_,
        v___y_913_,
        v___y_914_,
        v___y_915_,
        v___y_916_,
        v___y_917_,
        v___y_918_,
        crate::leanh::lean_box(0),
    );
    return v___x_922_;
}
pub unsafe fn l_panic___at___00Lean_Elab_Tactic_evalCalc_spec__2___boxed(
    mut v_msg_923_: *mut crate::leanh::LeanObject,
    mut v___y_924_: *mut crate::leanh::LeanObject,
    mut v___y_925_: *mut crate::leanh::LeanObject,
    mut v___y_926_: *mut crate::leanh::LeanObject,
    mut v___y_927_: *mut crate::leanh::LeanObject,
    mut v___y_928_: *mut crate::leanh::LeanObject,
    mut v___y_929_: *mut crate::leanh::LeanObject,
    mut v___y_930_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_931_ = l_panic___at___00Lean_Elab_Tactic_evalCalc_spec__2(
        v_msg_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_,
    );
    crate::leanh::lean_dec(v___y_929_);
    crate::leanh::lean_dec_ref(v___y_928_);
    crate::leanh::lean_dec(v___y_927_);
    crate::leanh::lean_dec_ref(v___y_926_);
    crate::leanh::lean_dec(v___y_925_);
    crate::leanh::lean_dec_ref(v___y_924_);
    return v_res_931_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalCalc___lam__0(
    mut v_a_932_: *mut crate::leanh::LeanObject,
    mut v_x_933_: *mut crate::leanh::LeanObject,
    mut v___y_934_: *mut crate::leanh::LeanObject,
    mut v___y_935_: *mut crate::leanh::LeanObject,
    mut v___y_936_: *mut crate::leanh::LeanObject,
    mut v___y_937_: *mut crate::leanh::LeanObject,
    mut v___y_938_: *mut crate::leanh::LeanObject,
    mut v___y_939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_941_ = l_Lean_Elab_Term_throwCalcFailure___redArg(
        v_a_932_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_,
    );
    return v___x_941_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalCalc___lam__0___boxed(
    mut v_a_942_: *mut crate::leanh::LeanObject,
    mut v_x_943_: *mut crate::leanh::LeanObject,
    mut v___y_944_: *mut crate::leanh::LeanObject,
    mut v___y_945_: *mut crate::leanh::LeanObject,
    mut v___y_946_: *mut crate::leanh::LeanObject,
    mut v___y_947_: *mut crate::leanh::LeanObject,
    mut v___y_948_: *mut crate::leanh::LeanObject,
    mut v___y_949_: *mut crate::leanh::LeanObject,
    mut v___y_950_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_951_ = l_Lean_Elab_Tactic_evalCalc___lam__0(
        v_a_942_, v_x_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_,
    );
    crate::leanh::lean_dec(v___y_949_);
    crate::leanh::lean_dec_ref(v___y_948_);
    crate::leanh::lean_dec(v___y_947_);
    crate::leanh::lean_dec_ref(v___y_946_);
    crate::leanh::lean_dec(v_x_943_);
    crate::leanh::lean_dec_ref(v_a_942_);
    return v_res_951_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalCalc___lam__1(
    mut v_a_952_: *mut crate::leanh::LeanObject,
    mut v_x_953_: *mut crate::leanh::LeanObject,
    mut v___y_954_: *mut crate::leanh::LeanObject,
    mut v___y_955_: *mut crate::leanh::LeanObject,
    mut v___y_956_: *mut crate::leanh::LeanObject,
    mut v___y_957_: *mut crate::leanh::LeanObject,
    mut v___y_958_: *mut crate::leanh::LeanObject,
    mut v___y_959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_961_ = l_Lean_Elab_Term_throwCalcFailure___redArg(
        v_a_952_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_,
    );
    return v___x_961_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalCalc___lam__1___boxed(
    mut v_a_962_: *mut crate::leanh::LeanObject,
    mut v_x_963_: *mut crate::leanh::LeanObject,
    mut v___y_964_: *mut crate::leanh::LeanObject,
    mut v___y_965_: *mut crate::leanh::LeanObject,
    mut v___y_966_: *mut crate::leanh::LeanObject,
    mut v___y_967_: *mut crate::leanh::LeanObject,
    mut v___y_968_: *mut crate::leanh::LeanObject,
    mut v___y_969_: *mut crate::leanh::LeanObject,
    mut v___y_970_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_971_ = l_Lean_Elab_Tactic_evalCalc___lam__1(
        v_a_962_, v_x_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_,
    );
    crate::leanh::lean_dec(v___y_969_);
    crate::leanh::lean_dec_ref(v___y_968_);
    crate::leanh::lean_dec(v___y_967_);
    crate::leanh::lean_dec_ref(v___y_966_);
    crate::leanh::lean_dec(v_x_963_);
    crate::leanh::lean_dec_ref(v_a_962_);
    return v_res_971_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_evalCalc___lam__2___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_976_ = l_Lean_Elab_Tactic_evalCalc___lam__2___closed__3;
    v___x_977_ = crate::leanh::lean_unsigned_to_nat(65);
    v___x_978_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_979_ = l_Lean_Elab_Tactic_evalCalc___lam__2___closed__2;
    v___x_980_ = l_Lean_Elab_Tactic_evalCalc___lam__2___closed__1;
    v___x_981_ =
        l_mkPanicMessageWithDecl(v___x_980_, v___x_979_, v___x_978_, v___x_977_, v___x_976_);
    return v___x_981_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalCalc___lam__2(
    mut v_a_982_: *mut crate::leanh::LeanObject,
    mut v___x_983_: *mut crate::leanh::LeanObject,
    mut v___f_984_: *mut crate::leanh::LeanObject,
    mut v___f_985_: *mut crate::leanh::LeanObject,
    mut v___x_986_: *mut crate::leanh::LeanObject,
    mut v_tag_987_: *mut crate::leanh::LeanObject,
    mut v___y_988_: *mut crate::leanh::LeanObject,
    mut v___y_989_: *mut crate::leanh::LeanObject,
    mut v___y_990_: *mut crate::leanh::LeanObject,
    mut v___y_991_: *mut crate::leanh::LeanObject,
    mut v___y_992_: *mut crate::leanh::LeanObject,
    mut v___y_993_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_999_: u8 = 0;
    let mut v_fst_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1013_: u8 = 0;
    let mut v___x_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: u8 = 0;
    let mut v___x_1020_: u8 = 0;
    let mut v___x_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1025_: u8 = 0;
    let mut v___x_1026_: u8 = 0;
    let mut v___x_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: u8 = 0;
    let mut v___x_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1058_: u8 = 0;
    let mut v___x_1059_: u8 = 0;
    let mut v___x_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1063_: u8 = 0;
    let mut v_a_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1069_: u8 = 0;
    let mut v___x_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1073_: u8 = 0;
    let mut v___x_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: u8 = 0;
    let mut v___x_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1085_: u8 = 0;
    let mut v___x_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1089_: u8 = 0;
    let mut v___x_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1095_: u8 = 0;
    let mut v___x_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1099_: u8 = 0;
    let mut v___x_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1103_: u8 = 0;
    let mut v_a_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1107_: u8 = 0;
    let mut v___x_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1111_: u8 = 0;
    let mut v_isSharedCheck_1112_: u8 = 0;
    let mut v_a_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1116_: u8 = 0;
    let mut v___x_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1120_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_995_ = l_Lean_Elab_Term_elabCalcSteps(
                    v_a_982_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_,
                    v___y_993_,
                );
                if crate::leanh::lean_obj_tag(v___x_995_) == 0 {
                    v_a_996_ = crate::leanh::lean_ctor_get(v___x_995_, 0);
                    v_isSharedCheck_1112_ = (!crate::leanh::lean_is_exclusive(v___x_995_)) as u8;
                    if v_isSharedCheck_1112_ == 0 {
                        v___x_998_ = v___x_995_;
                        v_isShared_999_ = v_isSharedCheck_1112_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_996_);
                        crate::leanh::lean_dec(v___x_995_);
                        v___x_998_ = crate::leanh::lean_box(0);
                        v_isShared_999_ = v_isSharedCheck_1112_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___y_993_);
                    crate::leanh::lean_dec_ref(v___y_992_);
                    crate::leanh::lean_dec(v___y_991_);
                    crate::leanh::lean_dec_ref(v___y_990_);
                    crate::leanh::lean_dec(v_tag_987_);
                    crate::leanh::lean_dec_ref(v___x_986_);
                    crate::leanh::lean_dec_ref(v___f_985_);
                    crate::leanh::lean_dec_ref(v___f_984_);
                    crate::leanh::lean_dec_ref(v___x_983_);
                    v_a_1113_ = crate::leanh::lean_ctor_get(v___x_995_, 0);
                    v_isSharedCheck_1120_ = (!crate::leanh::lean_is_exclusive(v___x_995_)) as u8;
                    if v_isSharedCheck_1120_ == 0 {
                        v___x_1115_ = v___x_995_;
                        v_isShared_1116_ = v_isSharedCheck_1120_;
                        state = 19;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1113_);
                        crate::leanh::lean_dec(v___x_995_);
                        v___x_1115_ = crate::leanh::lean_box(0);
                        v_isShared_1116_ = v_isSharedCheck_1120_;
                        state = 19;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1000_ = crate::leanh::lean_ctor_get(v_a_996_, 0);
                crate::leanh::lean_inc(v_fst_1000_);
                v_snd_1001_ = crate::leanh::lean_ctor_get(v_a_996_, 1);
                crate::leanh::lean_inc_n(v_snd_1001_, 2);
                crate::leanh::lean_dec(v_a_996_);
                crate::leanh::lean_inc_ref(v___x_983_);
                v___x_1021_ = l_Lean_Meta_isExprDefEq(
                    v_snd_1001_,
                    v___x_983_,
                    v___y_990_,
                    v___y_991_,
                    v___y_992_,
                    v___y_993_,
                );
                if crate::leanh::lean_obj_tag(v___x_1021_) == 0 {
                    v_a_1022_ = crate::leanh::lean_ctor_get(v___x_1021_, 0);
                    v_isSharedCheck_1103_ = (!crate::leanh::lean_is_exclusive(v___x_1021_)) as u8;
                    if v_isSharedCheck_1103_ == 0 {
                        v___x_1024_ = v___x_1021_;
                        v_isShared_1025_ = v_isSharedCheck_1103_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1022_);
                        crate::leanh::lean_dec(v___x_1021_);
                        v___x_1024_ = crate::leanh::lean_box(0);
                        v_isShared_1025_ = v_isSharedCheck_1103_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_snd_1001_);
                    crate::leanh::lean_dec(v_fst_1000_);
                    crate::leanh::lean_del_object(v___x_998_);
                    crate::leanh::lean_dec(v___y_993_);
                    crate::leanh::lean_dec_ref(v___y_992_);
                    crate::leanh::lean_dec(v___y_991_);
                    crate::leanh::lean_dec_ref(v___y_990_);
                    crate::leanh::lean_dec(v_tag_987_);
                    crate::leanh::lean_dec_ref(v___x_986_);
                    crate::leanh::lean_dec_ref(v___f_985_);
                    crate::leanh::lean_dec_ref(v___f_984_);
                    crate::leanh::lean_dec_ref(v___x_983_);
                    v_a_1104_ = crate::leanh::lean_ctor_get(v___x_1021_, 0);
                    v_isSharedCheck_1111_ = (!crate::leanh::lean_is_exclusive(v___x_1021_)) as u8;
                    if v_isSharedCheck_1111_ == 0 {
                        v___x_1106_ = v___x_1021_;
                        v_isShared_1107_ = v_isSharedCheck_1111_;
                        state = 17;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1104_);
                        crate::leanh::lean_dec(v___x_1021_);
                        v___x_1106_ = crate::leanh::lean_box(0);
                        v_isShared_1107_ = v_isSharedCheck_1111_;
                        state = 17;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1009_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1009_, 0, v___x_983_);
                v___x_1010_ = l_Lean_Elab_Term_ensureHasTypeWithErrorMsgs(
                    v___x_1009_,
                    v_fst_1000_,
                    v___f_984_,
                    v___f_985_,
                    v___y_1003_,
                    v___y_1004_,
                    v___y_1005_,
                    v___y_1006_,
                    v___y_1007_,
                    v___y_1008_,
                );
                crate::leanh::lean_dec(v___y_1008_);
                crate::leanh::lean_dec_ref(v___y_1007_);
                crate::leanh::lean_dec(v___y_1006_);
                crate::leanh::lean_dec_ref(v___y_1005_);
                return v___x_1010_;
            }
            3 => {
                if v___y_1013_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_1012_);
                    crate::leanh::lean_del_object(v___x_998_);
                    v___y_1003_ = v___y_988_;
                    v___y_1004_ = v___y_989_;
                    v___y_1005_ = v___y_990_;
                    v___y_1006_ = v___y_991_;
                    v___y_1007_ = v___y_992_;
                    v___y_1008_ = v___y_993_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_fst_1000_);
                    crate::leanh::lean_dec(v___y_993_);
                    crate::leanh::lean_dec_ref(v___y_992_);
                    crate::leanh::lean_dec(v___y_991_);
                    crate::leanh::lean_dec_ref(v___y_990_);
                    crate::leanh::lean_dec_ref(v___f_985_);
                    crate::leanh::lean_dec_ref(v___f_984_);
                    crate::leanh::lean_dec_ref(v___x_983_);
                    if v_isShared_999_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_998_, 1);
                        crate::leanh::lean_ctor_set(v___x_998_, 0, v___y_1012_);
                        v___x_1015_ = v___x_998_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1016_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1016_, 0, v___y_1012_);
                        v___x_1015_ = v_reuseFailAlloc_1016_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_1015_;
            }
            5 => {
                v___x_1019_ = l_Lean_Exception_isInterrupt(v_a_1018_);
                if v___x_1019_ == 0 {
                    crate::leanh::lean_inc_ref(v_a_1018_);
                    v___x_1020_ = l_Lean_Exception_isRuntime(v_a_1018_);
                    v___y_1012_ = v_a_1018_;
                    v___y_1013_ = v___x_1020_;
                    state = 3;
                    continue;
                } else {
                    v___y_1012_ = v_a_1018_;
                    v___y_1013_ = v___x_1019_;
                    state = 3;
                    continue;
                }
            }
            6 => {
                v___x_1026_ = (crate::leanh::lean_unbox(v_a_1022_) as u8);
                crate::leanh::lean_dec(v_a_1022_);
                if v___x_1026_ == 0 {
                    crate::leanh::lean_del_object(v___x_1024_);
                    v___x_1027_ = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(v_snd_1001_);
                    if crate::leanh::lean_obj_tag(v___x_1027_) == 0 {
                        v_a_1028_ = crate::leanh::lean_ctor_get(v___x_1027_, 0);
                        crate::leanh::lean_inc(v_a_1028_);
                        crate::leanh::lean_dec_ref_known(v___x_1027_, 1);
                        if crate::leanh::lean_obj_tag(v_a_1028_) == 1 {
                            v_val_1029_ = crate::leanh::lean_ctor_get(v_a_1028_, 0);
                            crate::leanh::lean_inc(v_val_1029_);
                            crate::leanh::lean_dec_ref_known(v_a_1028_, 1);
                            v_snd_1030_ = crate::leanh::lean_ctor_get(v_val_1029_, 1);
                            crate::leanh::lean_inc(v_snd_1030_);
                            crate::leanh::lean_dec(v_val_1029_);
                            v_fst_1031_ = crate::leanh::lean_ctor_get(v_snd_1030_, 0);
                            crate::leanh::lean_inc(v_fst_1031_);
                            v_snd_1032_ = crate::leanh::lean_ctor_get(v_snd_1030_, 1);
                            crate::leanh::lean_inc(v_snd_1032_);
                            crate::leanh::lean_dec(v_snd_1030_);
                            v___x_1033_ = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(v___x_983_);
                            if crate::leanh::lean_obj_tag(v___x_1033_) == 0 {
                                v_a_1034_ = crate::leanh::lean_ctor_get(v___x_1033_, 0);
                                crate::leanh::lean_inc(v_a_1034_);
                                crate::leanh::lean_dec_ref_known(v___x_1033_, 1);
                                if crate::leanh::lean_obj_tag(v_a_1034_) == 1 {
                                    v_val_1035_ = crate::leanh::lean_ctor_get(v_a_1034_, 0);
                                    crate::leanh::lean_inc(v_val_1035_);
                                    crate::leanh::lean_dec_ref_known(v_a_1034_, 1);
                                    v_snd_1036_ = crate::leanh::lean_ctor_get(v_val_1035_, 1);
                                    crate::leanh::lean_inc(v_snd_1036_);
                                    v_fst_1037_ = crate::leanh::lean_ctor_get(v_val_1035_, 0);
                                    crate::leanh::lean_inc(v_fst_1037_);
                                    crate::leanh::lean_dec(v_val_1035_);
                                    v_fst_1038_ = crate::leanh::lean_ctor_get(v_snd_1036_, 0);
                                    crate::leanh::lean_inc(v_fst_1038_);
                                    v_snd_1039_ = crate::leanh::lean_ctor_get(v_snd_1036_, 1);
                                    crate::leanh::lean_inc(v_snd_1039_);
                                    crate::leanh::lean_dec(v_snd_1036_);
                                    crate::leanh::lean_inc(v___y_993_);
                                    crate::leanh::lean_inc_ref(v___y_992_);
                                    crate::leanh::lean_inc(v___y_991_);
                                    crate::leanh::lean_inc_ref(v___y_990_);
                                    crate::leanh::lean_inc(v_snd_1032_);
                                    v___x_1074_ = lean_infer_type(
                                        v_snd_1032_,
                                        v___y_990_,
                                        v___y_991_,
                                        v___y_992_,
                                        v___y_993_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_1074_) == 0 {
                                        v_a_1075_ = crate::leanh::lean_ctor_get(v___x_1074_, 0);
                                        crate::leanh::lean_inc(v_a_1075_);
                                        crate::leanh::lean_dec_ref_known(v___x_1074_, 1);
                                        crate::leanh::lean_inc(v___y_993_);
                                        crate::leanh::lean_inc_ref(v___y_992_);
                                        crate::leanh::lean_inc(v___y_991_);
                                        crate::leanh::lean_inc_ref(v___y_990_);
                                        crate::leanh::lean_inc(v_fst_1038_);
                                        v___x_1076_ = lean_infer_type(
                                            v_fst_1038_,
                                            v___y_990_,
                                            v___y_991_,
                                            v___y_992_,
                                            v___y_993_,
                                        );
                                        if crate::leanh::lean_obj_tag(v___x_1076_) == 0 {
                                            v_a_1077_ = crate::leanh::lean_ctor_get(v___x_1076_, 0);
                                            crate::leanh::lean_inc(v_a_1077_);
                                            crate::leanh::lean_dec_ref_known(v___x_1076_, 1);
                                            v___x_1078_ = l_Lean_Meta_isExprDefEq(
                                                v_fst_1031_,
                                                v_fst_1038_,
                                                v___y_990_,
                                                v___y_991_,
                                                v___y_992_,
                                                v___y_993_,
                                            );
                                            if crate::leanh::lean_obj_tag(v___x_1078_) == 0 {
                                                v_a_1079_ =
                                                    crate::leanh::lean_ctor_get(v___x_1078_, 0);
                                                crate::leanh::lean_inc(v_a_1079_);
                                                v___x_1080_ =
                                                    (crate::leanh::lean_unbox(v_a_1079_) as u8);
                                                crate::leanh::lean_dec(v_a_1079_);
                                                if v___x_1080_ == 0 {
                                                    crate::leanh::lean_dec(v_a_1077_);
                                                    crate::leanh::lean_dec(v_a_1075_);
                                                    v___y_1041_ = v___x_1078_;
                                                    state = 7;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_dec_ref_known(
                                                        v___x_1078_,
                                                        1,
                                                    );
                                                    v___x_1081_ = l_Lean_Meta_isExprDefEq(
                                                        v_a_1075_, v_a_1077_, v___y_990_,
                                                        v___y_991_, v___y_992_, v___y_993_,
                                                    );
                                                    v___y_1041_ = v___x_1081_;
                                                    state = 7;
                                                    continue;
                                                }
                                            } else {
                                                crate::leanh::lean_dec(v_a_1077_);
                                                crate::leanh::lean_dec(v_a_1075_);
                                                v___y_1041_ = v___x_1078_;
                                                state = 7;
                                                continue;
                                            }
                                        } else {
                                            crate::leanh::lean_dec(v_a_1075_);
                                            crate::leanh::lean_dec(v_snd_1039_);
                                            crate::leanh::lean_dec(v_fst_1038_);
                                            crate::leanh::lean_dec(v_fst_1037_);
                                            crate::leanh::lean_dec(v_snd_1032_);
                                            crate::leanh::lean_dec(v_fst_1031_);
                                            crate::leanh::lean_dec(v_snd_1001_);
                                            crate::leanh::lean_dec(v_fst_1000_);
                                            crate::leanh::lean_del_object(v___x_998_);
                                            crate::leanh::lean_dec(v___y_993_);
                                            crate::leanh::lean_dec_ref(v___y_992_);
                                            crate::leanh::lean_dec(v___y_991_);
                                            crate::leanh::lean_dec_ref(v___y_990_);
                                            crate::leanh::lean_dec(v_tag_987_);
                                            crate::leanh::lean_dec_ref(v___x_986_);
                                            crate::leanh::lean_dec_ref(v___f_985_);
                                            crate::leanh::lean_dec_ref(v___f_984_);
                                            crate::leanh::lean_dec_ref(v___x_983_);
                                            return v___x_1076_;
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_snd_1039_);
                                        crate::leanh::lean_dec(v_fst_1038_);
                                        crate::leanh::lean_dec(v_fst_1037_);
                                        crate::leanh::lean_dec(v_snd_1032_);
                                        crate::leanh::lean_dec(v_fst_1031_);
                                        crate::leanh::lean_dec(v_snd_1001_);
                                        crate::leanh::lean_dec(v_fst_1000_);
                                        crate::leanh::lean_del_object(v___x_998_);
                                        crate::leanh::lean_dec(v___y_993_);
                                        crate::leanh::lean_dec_ref(v___y_992_);
                                        crate::leanh::lean_dec(v___y_991_);
                                        crate::leanh::lean_dec_ref(v___y_990_);
                                        crate::leanh::lean_dec(v_tag_987_);
                                        crate::leanh::lean_dec_ref(v___x_986_);
                                        crate::leanh::lean_dec_ref(v___f_985_);
                                        crate::leanh::lean_dec_ref(v___f_984_);
                                        crate::leanh::lean_dec_ref(v___x_983_);
                                        return v___x_1074_;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_1034_);
                                    crate::leanh::lean_dec(v_snd_1032_);
                                    crate::leanh::lean_dec(v_fst_1031_);
                                    crate::leanh::lean_dec(v_snd_1001_);
                                    crate::leanh::lean_del_object(v___x_998_);
                                    crate::leanh::lean_dec(v_tag_987_);
                                    crate::leanh::lean_dec_ref(v___x_986_);
                                    v___y_1003_ = v___y_988_;
                                    v___y_1004_ = v___y_989_;
                                    v___y_1005_ = v___y_990_;
                                    v___y_1006_ = v___y_991_;
                                    v___y_1007_ = v___y_992_;
                                    v___y_1008_ = v___y_993_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_snd_1032_);
                                crate::leanh::lean_dec(v_fst_1031_);
                                crate::leanh::lean_dec(v_snd_1001_);
                                crate::leanh::lean_dec(v_fst_1000_);
                                crate::leanh::lean_del_object(v___x_998_);
                                crate::leanh::lean_dec(v___y_993_);
                                crate::leanh::lean_dec_ref(v___y_992_);
                                crate::leanh::lean_dec(v___y_991_);
                                crate::leanh::lean_dec_ref(v___y_990_);
                                crate::leanh::lean_dec(v_tag_987_);
                                crate::leanh::lean_dec_ref(v___x_986_);
                                crate::leanh::lean_dec_ref(v___f_985_);
                                crate::leanh::lean_dec_ref(v___f_984_);
                                crate::leanh::lean_dec_ref(v___x_983_);
                                v_a_1082_ = crate::leanh::lean_ctor_get(v___x_1033_, 0);
                                v_isSharedCheck_1089_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1033_)) as u8;
                                if v_isSharedCheck_1089_ == 0 {
                                    v___x_1084_ = v___x_1033_;
                                    v_isShared_1085_ = v_isSharedCheck_1089_;
                                    state = 12;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1082_);
                                    crate::leanh::lean_dec(v___x_1033_);
                                    v___x_1084_ = crate::leanh::lean_box(0);
                                    v_isShared_1085_ = v_isSharedCheck_1089_;
                                    state = 12;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_1028_);
                            crate::leanh::lean_dec(v_snd_1001_);
                            crate::leanh::lean_dec(v_fst_1000_);
                            crate::leanh::lean_del_object(v___x_998_);
                            crate::leanh::lean_dec(v_tag_987_);
                            crate::leanh::lean_dec_ref(v___x_986_);
                            crate::leanh::lean_dec_ref(v___f_985_);
                            crate::leanh::lean_dec_ref(v___f_984_);
                            crate::leanh::lean_dec_ref(v___x_983_);
                            v___x_1090_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_Tactic_evalCalc___lam__2___closed__4
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_Tactic_evalCalc___lam__2___closed__4_once
                                ),
                                _init_l_Lean_Elab_Tactic_evalCalc___lam__2___closed__4,
                            );
                            v___x_1091_ = l_panic___at___00Lean_Elab_Tactic_evalCalc_spec__2(
                                v___x_1090_,
                                v___y_988_,
                                v___y_989_,
                                v___y_990_,
                                v___y_991_,
                                v___y_992_,
                                v___y_993_,
                            );
                            crate::leanh::lean_dec(v___y_993_);
                            crate::leanh::lean_dec_ref(v___y_992_);
                            crate::leanh::lean_dec(v___y_991_);
                            crate::leanh::lean_dec_ref(v___y_990_);
                            return v___x_1091_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_snd_1001_);
                        crate::leanh::lean_dec(v_fst_1000_);
                        crate::leanh::lean_del_object(v___x_998_);
                        crate::leanh::lean_dec(v___y_993_);
                        crate::leanh::lean_dec_ref(v___y_992_);
                        crate::leanh::lean_dec(v___y_991_);
                        crate::leanh::lean_dec_ref(v___y_990_);
                        crate::leanh::lean_dec(v_tag_987_);
                        crate::leanh::lean_dec_ref(v___x_986_);
                        crate::leanh::lean_dec_ref(v___f_985_);
                        crate::leanh::lean_dec_ref(v___f_984_);
                        crate::leanh::lean_dec_ref(v___x_983_);
                        v_a_1092_ = crate::leanh::lean_ctor_get(v___x_1027_, 0);
                        v_isSharedCheck_1099_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1027_)) as u8;
                        if v_isSharedCheck_1099_ == 0 {
                            v___x_1094_ = v___x_1027_;
                            v_isShared_1095_ = v_isSharedCheck_1099_;
                            state = 14;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1092_);
                            crate::leanh::lean_dec(v___x_1027_);
                            v___x_1094_ = crate::leanh::lean_box(0);
                            v_isShared_1095_ = v_isSharedCheck_1099_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_snd_1001_);
                    crate::leanh::lean_del_object(v___x_998_);
                    crate::leanh::lean_dec(v___y_993_);
                    crate::leanh::lean_dec_ref(v___y_992_);
                    crate::leanh::lean_dec(v___y_991_);
                    crate::leanh::lean_dec_ref(v___y_990_);
                    crate::leanh::lean_dec(v_tag_987_);
                    crate::leanh::lean_dec_ref(v___x_986_);
                    crate::leanh::lean_dec_ref(v___f_985_);
                    crate::leanh::lean_dec_ref(v___f_984_);
                    crate::leanh::lean_dec_ref(v___x_983_);
                    if v_isShared_1025_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1024_, 0, v_fst_1000_);
                        v___x_1101_ = v___x_1024_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_1102_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_fst_1000_);
                        v___x_1101_ = v_reuseFailAlloc_1102_;
                        state = 16;
                        continue;
                    }
                }
            }
            7 => {
                if crate::leanh::lean_obj_tag(v___y_1041_) == 0 {
                    v_a_1042_ = crate::leanh::lean_ctor_get(v___y_1041_, 0);
                    crate::leanh::lean_inc(v_a_1042_);
                    crate::leanh::lean_dec_ref_known(v___y_1041_, 1);
                    v___x_1043_ = (crate::leanh::lean_unbox(v_a_1042_) as u8);
                    crate::leanh::lean_dec(v_a_1042_);
                    if v___x_1043_ == 0 {
                        crate::leanh::lean_dec(v_snd_1039_);
                        crate::leanh::lean_dec(v_fst_1037_);
                        crate::leanh::lean_dec(v_snd_1032_);
                        crate::leanh::lean_dec(v_snd_1001_);
                        crate::leanh::lean_del_object(v___x_998_);
                        crate::leanh::lean_dec(v_tag_987_);
                        crate::leanh::lean_dec_ref(v___x_986_);
                        v___y_1003_ = v___y_988_;
                        v___y_1004_ = v___y_989_;
                        v___y_1005_ = v___y_990_;
                        v___y_1006_ = v___y_991_;
                        v___y_1007_ = v___y_992_;
                        v___y_1008_ = v___y_993_;
                        state = 2;
                        continue;
                    } else {
                        v___x_1044_ = l_Lean_mkAppB(v_fst_1037_, v_snd_1032_, v_snd_1039_);
                        v___x_1045_ = l_Lean_Elab_Tactic_evalCalc___lam__2___closed__0;
                        v___x_1046_ = l_Lean_Name_mkStr2(v___x_986_, v___x_1045_);
                        v___x_1047_ = l_Lean_Name_append(v_tag_987_, v___x_1046_);
                        crate::leanh::lean_inc_ref(v___x_1044_);
                        v___x_1048_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                            v___x_1044_,
                            v___x_1047_,
                            v___y_990_,
                            v___y_991_,
                            v___y_992_,
                            v___y_993_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1048_) == 0 {
                            v_a_1049_ = crate::leanh::lean_ctor_get(v___x_1048_, 0);
                            crate::leanh::lean_inc(v_a_1049_);
                            crate::leanh::lean_dec_ref_known(v___x_1048_, 1);
                            crate::leanh::lean_inc(v_fst_1000_);
                            v___x_1050_ = l_Lean_Elab_Term_mkCalcTrans(
                                v_fst_1000_,
                                v_snd_1001_,
                                v_a_1049_,
                                v___x_1044_,
                                v___y_990_,
                                v___y_991_,
                                v___y_992_,
                                v___y_993_,
                            );
                            crate::leanh::lean_dec(v_snd_1001_);
                            if crate::leanh::lean_obj_tag(v___x_1050_) == 0 {
                                v_a_1051_ = crate::leanh::lean_ctor_get(v___x_1050_, 0);
                                crate::leanh::lean_inc(v_a_1051_);
                                crate::leanh::lean_dec_ref_known(v___x_1050_, 1);
                                v_fst_1052_ = crate::leanh::lean_ctor_get(v_a_1051_, 0);
                                crate::leanh::lean_inc(v_fst_1052_);
                                v_snd_1053_ = crate::leanh::lean_ctor_get(v_a_1051_, 1);
                                crate::leanh::lean_inc(v_snd_1053_);
                                crate::leanh::lean_dec(v_a_1051_);
                                crate::leanh::lean_inc_ref(v___x_983_);
                                v___x_1054_ = l_Lean_Meta_isExprDefEq(
                                    v_snd_1053_,
                                    v___x_983_,
                                    v___y_990_,
                                    v___y_991_,
                                    v___y_992_,
                                    v___y_993_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_1054_) == 0 {
                                    crate::leanh::lean_del_object(v___x_998_);
                                    v_a_1055_ = crate::leanh::lean_ctor_get(v___x_1054_, 0);
                                    v_isSharedCheck_1063_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1054_)) as u8;
                                    if v_isSharedCheck_1063_ == 0 {
                                        v___x_1057_ = v___x_1054_;
                                        v_isShared_1058_ = v_isSharedCheck_1063_;
                                        state = 8;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_1055_);
                                        crate::leanh::lean_dec(v___x_1054_);
                                        v___x_1057_ = crate::leanh::lean_box(0);
                                        v_isShared_1058_ = v_isSharedCheck_1063_;
                                        state = 8;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_fst_1052_);
                                    v_a_1064_ = crate::leanh::lean_ctor_get(v___x_1054_, 0);
                                    crate::leanh::lean_inc(v_a_1064_);
                                    crate::leanh::lean_dec_ref_known(v___x_1054_, 1);
                                    v_a_1018_ = v_a_1064_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                v_a_1065_ = crate::leanh::lean_ctor_get(v___x_1050_, 0);
                                crate::leanh::lean_inc(v_a_1065_);
                                crate::leanh::lean_dec_ref_known(v___x_1050_, 1);
                                v_a_1018_ = v_a_1065_;
                                state = 5;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_1044_);
                            crate::leanh::lean_dec(v_snd_1001_);
                            crate::leanh::lean_dec(v_fst_1000_);
                            crate::leanh::lean_del_object(v___x_998_);
                            crate::leanh::lean_dec(v___y_993_);
                            crate::leanh::lean_dec_ref(v___y_992_);
                            crate::leanh::lean_dec(v___y_991_);
                            crate::leanh::lean_dec_ref(v___y_990_);
                            crate::leanh::lean_dec_ref(v___f_985_);
                            crate::leanh::lean_dec_ref(v___f_984_);
                            crate::leanh::lean_dec_ref(v___x_983_);
                            return v___x_1048_;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_snd_1039_);
                    crate::leanh::lean_dec(v_fst_1037_);
                    crate::leanh::lean_dec(v_snd_1032_);
                    crate::leanh::lean_dec(v_snd_1001_);
                    crate::leanh::lean_dec(v_fst_1000_);
                    crate::leanh::lean_del_object(v___x_998_);
                    crate::leanh::lean_dec(v___y_993_);
                    crate::leanh::lean_dec_ref(v___y_992_);
                    crate::leanh::lean_dec(v___y_991_);
                    crate::leanh::lean_dec_ref(v___y_990_);
                    crate::leanh::lean_dec(v_tag_987_);
                    crate::leanh::lean_dec_ref(v___x_986_);
                    crate::leanh::lean_dec_ref(v___f_985_);
                    crate::leanh::lean_dec_ref(v___f_984_);
                    crate::leanh::lean_dec_ref(v___x_983_);
                    v_a_1066_ = crate::leanh::lean_ctor_get(v___y_1041_, 0);
                    v_isSharedCheck_1073_ = (!crate::leanh::lean_is_exclusive(v___y_1041_)) as u8;
                    if v_isSharedCheck_1073_ == 0 {
                        v___x_1068_ = v___y_1041_;
                        v_isShared_1069_ = v_isSharedCheck_1073_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1066_);
                        crate::leanh::lean_dec(v___y_1041_);
                        v___x_1068_ = crate::leanh::lean_box(0);
                        v_isShared_1069_ = v_isSharedCheck_1073_;
                        state = 10;
                        continue;
                    }
                }
            }
            8 => {
                v___x_1059_ = (crate::leanh::lean_unbox(v_a_1055_) as u8);
                crate::leanh::lean_dec(v_a_1055_);
                if v___x_1059_ == 0 {
                    crate::leanh::lean_del_object(v___x_1057_);
                    crate::leanh::lean_dec(v_fst_1052_);
                    v___y_1003_ = v___y_988_;
                    v___y_1004_ = v___y_989_;
                    v___y_1005_ = v___y_990_;
                    v___y_1006_ = v___y_991_;
                    v___y_1007_ = v___y_992_;
                    v___y_1008_ = v___y_993_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_fst_1000_);
                    crate::leanh::lean_dec(v___y_993_);
                    crate::leanh::lean_dec_ref(v___y_992_);
                    crate::leanh::lean_dec(v___y_991_);
                    crate::leanh::lean_dec_ref(v___y_990_);
                    crate::leanh::lean_dec_ref(v___f_985_);
                    crate::leanh::lean_dec_ref(v___f_984_);
                    crate::leanh::lean_dec_ref(v___x_983_);
                    if v_isShared_1058_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1057_, 0, v_fst_1052_);
                        v___x_1061_ = v___x_1057_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_1062_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_fst_1052_);
                        v___x_1061_ = v_reuseFailAlloc_1062_;
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                return v___x_1061_;
            }
            10 => {
                if v_isShared_1069_ == 0 {
                    v___x_1071_ = v___x_1068_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1072_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_a_1066_);
                    v___x_1071_ = v_reuseFailAlloc_1072_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1071_;
            }
            12 => {
                if v_isShared_1085_ == 0 {
                    v___x_1087_ = v___x_1084_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1088_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_a_1082_);
                    v___x_1087_ = v_reuseFailAlloc_1088_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1087_;
            }
            14 => {
                if v_isShared_1095_ == 0 {
                    v___x_1097_ = v___x_1094_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1098_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_a_1092_);
                    v___x_1097_ = v_reuseFailAlloc_1098_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_1097_;
            }
            16 => {
                return v___x_1101_;
            }
            17 => {
                if v_isShared_1107_ == 0 {
                    v___x_1109_ = v___x_1106_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1110_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_a_1104_);
                    v___x_1109_ = v_reuseFailAlloc_1110_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_1109_;
            }
            19 => {
                if v_isShared_1116_ == 0 {
                    v___x_1118_ = v___x_1115_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1119_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_a_1113_);
                    v___x_1118_ = v_reuseFailAlloc_1119_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_1118_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalCalc___lam__2___boxed(
    mut v_a_1121_: *mut crate::leanh::LeanObject,
    mut v___x_1122_: *mut crate::leanh::LeanObject,
    mut v___f_1123_: *mut crate::leanh::LeanObject,
    mut v___f_1124_: *mut crate::leanh::LeanObject,
    mut v___x_1125_: *mut crate::leanh::LeanObject,
    mut v_tag_1126_: *mut crate::leanh::LeanObject,
    mut v___y_1127_: *mut crate::leanh::LeanObject,
    mut v___y_1128_: *mut crate::leanh::LeanObject,
    mut v___y_1129_: *mut crate::leanh::LeanObject,
    mut v___y_1130_: *mut crate::leanh::LeanObject,
    mut v___y_1131_: *mut crate::leanh::LeanObject,
    mut v___y_1132_: *mut crate::leanh::LeanObject,
    mut v___y_1133_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1134_ = l_Lean_Elab_Tactic_evalCalc___lam__2(
        v_a_1121_,
        v___x_1122_,
        v___f_1123_,
        v___f_1124_,
        v___x_1125_,
        v_tag_1126_,
        v___y_1127_,
        v___y_1128_,
        v___y_1129_,
        v___y_1130_,
        v___y_1131_,
        v___y_1132_,
    );
    crate::leanh::lean_dec(v___y_1128_);
    crate::leanh::lean_dec_ref(v___y_1127_);
    crate::leanh::lean_dec_ref(v_a_1121_);
    return v_res_1134_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalCalc___lam__3(
    mut v_steps_1135_: *mut crate::leanh::LeanObject,
    mut v_target_1136_: *mut crate::leanh::LeanObject,
    mut v___x_1137_: *mut crate::leanh::LeanObject,
    mut v_tag_1138_: *mut crate::leanh::LeanObject,
    mut v___x_1139_: *mut crate::leanh::LeanObject,
    mut v___y_1140_: *mut crate::leanh::LeanObject,
    mut v___y_1141_: *mut crate::leanh::LeanObject,
    mut v___y_1142_: *mut crate::leanh::LeanObject,
    mut v___y_1143_: *mut crate::leanh::LeanObject,
    mut v___y_1144_: *mut crate::leanh::LeanObject,
    mut v___y_1145_: *mut crate::leanh::LeanObject,
    mut v___y_1146_: *mut crate::leanh::LeanObject,
    mut v___y_1147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: u8 = 0;
    let mut v___x_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1167_: u8 = 0;
    let mut v___x_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1171_: u8 = 0;
    let mut v_unused_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1176_: u8 = 0;
    let mut v___x_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1180_: u8 = 0;
    let mut v_a_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1184_: u8 = 0;
    let mut v___x_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1188_: u8 = 0;
    let mut v_a_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1192_: u8 = 0;
    let mut v___x_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1196_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1149_ = l_Lean_Elab_Term_mkCalcStepViews(
                    v_steps_1135_,
                    v___y_1142_,
                    v___y_1143_,
                    v___y_1144_,
                    v___y_1145_,
                    v___y_1146_,
                    v___y_1147_,
                );
                if crate::leanh::lean_obj_tag(v___x_1149_) == 0 {
                    v_a_1150_ = crate::leanh::lean_ctor_get(v___x_1149_, 0);
                    crate::leanh::lean_inc_n(v_a_1150_, 3);
                    crate::leanh::lean_dec_ref_known(v___x_1149_, 1);
                    v___x_1151_ =
                        l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalCalc_spec__1___redArg(
                            v_target_1136_,
                            v___y_1145_,
                        );
                    v_a_1152_ = crate::leanh::lean_ctor_get(v___x_1151_, 0);
                    crate::leanh::lean_inc(v_a_1152_);
                    crate::leanh::lean_dec_ref(v___x_1151_);
                    v___f_1153_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Elab_Tactic_evalCalc___lam__0___boxed as *mut core::ffi::c_void,
                        9,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_1153_, 0, v_a_1150_);
                    v___f_1154_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Elab_Tactic_evalCalc___lam__1___boxed as *mut core::ffi::c_void,
                        9,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_1154_, 0, v_a_1150_);
                    v___x_1155_ = l_Lean_Expr_consumeMData(v_a_1152_);
                    crate::leanh::lean_dec(v_a_1152_);
                    crate::leanh::lean_inc(v_tag_1138_);
                    v___f_1156_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Elab_Tactic_evalCalc___lam__2___boxed as *mut core::ffi::c_void,
                        13,
                        6,
                    );
                    crate::leanh::lean_closure_set(v___f_1156_, 0, v_a_1150_);
                    crate::leanh::lean_closure_set(v___f_1156_, 1, v___x_1155_);
                    crate::leanh::lean_closure_set(v___f_1156_, 2, v___f_1154_);
                    crate::leanh::lean_closure_set(v___f_1156_, 3, v___f_1153_);
                    crate::leanh::lean_closure_set(v___f_1156_, 4, v___x_1137_);
                    crate::leanh::lean_closure_set(v___f_1156_, 5, v_tag_1138_);
                    v___x_1157_ = 0;
                    v___x_1158_ = crate::leanh::lean_box((v___x_1157_) as usize);
                    v___x_1159_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Elab_Tactic_runTermElab___boxed as *mut core::ffi::c_void,
                        12,
                        3,
                    );
                    crate::leanh::lean_closure_set(v___x_1159_, 0, crate::leanh::lean_box(0));
                    crate::leanh::lean_closure_set(v___x_1159_, 1, v___f_1156_);
                    crate::leanh::lean_closure_set(v___x_1159_, 2, v___x_1158_);
                    v___x_1160_ = l_Lean_Elab_Tactic_withCollectingNewGoalsFrom(
                        v___x_1159_,
                        v_tag_1138_,
                        v___x_1139_,
                        v___x_1157_,
                        v___y_1140_,
                        v___y_1141_,
                        v___y_1142_,
                        v___y_1143_,
                        v___y_1144_,
                        v___y_1145_,
                        v___y_1146_,
                        v___y_1147_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1160_) == 0 {
                        v_a_1161_ = crate::leanh::lean_ctor_get(v___x_1160_, 0);
                        crate::leanh::lean_inc(v_a_1161_);
                        crate::leanh::lean_dec_ref_known(v___x_1160_, 1);
                        v_fst_1162_ = crate::leanh::lean_ctor_get(v_a_1161_, 0);
                        crate::leanh::lean_inc(v_fst_1162_);
                        v_snd_1163_ = crate::leanh::lean_ctor_get(v_a_1161_, 1);
                        crate::leanh::lean_inc(v_snd_1163_);
                        crate::leanh::lean_dec(v_a_1161_);
                        v___x_1164_ =
                            l_Lean_Elab_Tactic_pushGoals___redArg(v_snd_1163_, v___y_1141_);
                        if crate::leanh::lean_obj_tag(v___x_1164_) == 0 {
                            v_isSharedCheck_1171_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1164_)) as u8;
                            if v_isSharedCheck_1171_ == 0 {
                                v_unused_1172_ = crate::leanh::lean_ctor_get(v___x_1164_, 0);
                                crate::leanh::lean_dec(v_unused_1172_);
                                v___x_1166_ = v___x_1164_;
                                v_isShared_1167_ = v_isSharedCheck_1171_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_1164_);
                                v___x_1166_ = crate::leanh::lean_box(0);
                                v_isShared_1167_ = v_isSharedCheck_1171_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_fst_1162_);
                            v_a_1173_ = crate::leanh::lean_ctor_get(v___x_1164_, 0);
                            v_isSharedCheck_1180_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1164_)) as u8;
                            if v_isSharedCheck_1180_ == 0 {
                                v___x_1175_ = v___x_1164_;
                                v_isShared_1176_ = v_isSharedCheck_1180_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1173_);
                                crate::leanh::lean_dec(v___x_1164_);
                                v___x_1175_ = crate::leanh::lean_box(0);
                                v_isShared_1176_ = v_isSharedCheck_1180_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        v_a_1181_ = crate::leanh::lean_ctor_get(v___x_1160_, 0);
                        v_isSharedCheck_1188_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1160_)) as u8;
                        if v_isSharedCheck_1188_ == 0 {
                            v___x_1183_ = v___x_1160_;
                            v_isShared_1184_ = v_isSharedCheck_1188_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1181_);
                            crate::leanh::lean_dec(v___x_1160_);
                            v___x_1183_ = crate::leanh::lean_box(0);
                            v_isShared_1184_ = v_isSharedCheck_1188_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1139_);
                    crate::leanh::lean_dec(v_tag_1138_);
                    crate::leanh::lean_dec_ref(v___x_1137_);
                    crate::leanh::lean_dec_ref(v_target_1136_);
                    v_a_1189_ = crate::leanh::lean_ctor_get(v___x_1149_, 0);
                    v_isSharedCheck_1196_ = (!crate::leanh::lean_is_exclusive(v___x_1149_)) as u8;
                    if v_isSharedCheck_1196_ == 0 {
                        v___x_1191_ = v___x_1149_;
                        v_isShared_1192_ = v_isSharedCheck_1196_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1189_);
                        crate::leanh::lean_dec(v___x_1149_);
                        v___x_1191_ = crate::leanh::lean_box(0);
                        v_isShared_1192_ = v_isSharedCheck_1196_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1167_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1166_, 0, v_fst_1162_);
                    v___x_1169_ = v___x_1166_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1170_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_fst_1162_);
                    v___x_1169_ = v_reuseFailAlloc_1170_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1169_;
            }
            3 => {
                if v_isShared_1176_ == 0 {
                    v___x_1178_ = v___x_1175_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1179_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_a_1173_);
                    v___x_1178_ = v_reuseFailAlloc_1179_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1178_;
            }
            5 => {
                if v_isShared_1184_ == 0 {
                    v___x_1186_ = v___x_1183_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1187_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_a_1181_);
                    v___x_1186_ = v_reuseFailAlloc_1187_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1186_;
            }
            7 => {
                if v_isShared_1192_ == 0 {
                    v___x_1194_ = v___x_1191_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1195_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_a_1189_);
                    v___x_1194_ = v_reuseFailAlloc_1195_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1194_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalCalc___lam__3___boxed(
    mut v_steps_1197_: *mut crate::leanh::LeanObject,
    mut v_target_1198_: *mut crate::leanh::LeanObject,
    mut v___x_1199_: *mut crate::leanh::LeanObject,
    mut v_tag_1200_: *mut crate::leanh::LeanObject,
    mut v___x_1201_: *mut crate::leanh::LeanObject,
    mut v___y_1202_: *mut crate::leanh::LeanObject,
    mut v___y_1203_: *mut crate::leanh::LeanObject,
    mut v___y_1204_: *mut crate::leanh::LeanObject,
    mut v___y_1205_: *mut crate::leanh::LeanObject,
    mut v___y_1206_: *mut crate::leanh::LeanObject,
    mut v___y_1207_: *mut crate::leanh::LeanObject,
    mut v___y_1208_: *mut crate::leanh::LeanObject,
    mut v___y_1209_: *mut crate::leanh::LeanObject,
    mut v___y_1210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1211_ = l_Lean_Elab_Tactic_evalCalc___lam__3(
        v_steps_1197_,
        v_target_1198_,
        v___x_1199_,
        v_tag_1200_,
        v___x_1201_,
        v___y_1202_,
        v___y_1203_,
        v___y_1204_,
        v___y_1205_,
        v___y_1206_,
        v___y_1207_,
        v___y_1208_,
        v___y_1209_,
    );
    crate::leanh::lean_dec(v___y_1209_);
    crate::leanh::lean_dec_ref(v___y_1208_);
    crate::leanh::lean_dec(v___y_1207_);
    crate::leanh::lean_dec_ref(v___y_1206_);
    crate::leanh::lean_dec(v___y_1205_);
    crate::leanh::lean_dec_ref(v___y_1204_);
    crate::leanh::lean_dec(v___y_1203_);
    crate::leanh::lean_dec_ref(v___y_1202_);
    return v_res_1211_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalCalc___lam__4(
    mut v_a_1212_: *mut crate::leanh::LeanObject,
    mut v_trees_1213_: *mut crate::leanh::LeanObject,
    mut v___y_1214_: *mut crate::leanh::LeanObject,
    mut v___y_1215_: *mut crate::leanh::LeanObject,
    mut v___y_1216_: *mut crate::leanh::LeanObject,
    mut v___y_1217_: *mut crate::leanh::LeanObject,
    mut v___y_1218_: *mut crate::leanh::LeanObject,
    mut v___y_1219_: *mut crate::leanh::LeanObject,
    mut v___y_1220_: *mut crate::leanh::LeanObject,
    mut v___y_1221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1227_: u8 = 0;
    let mut v___x_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1232_: u8 = 0;
    let mut v_a_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1236_: u8 = 0;
    let mut v___x_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1240_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_1221_);
                crate::leanh::lean_inc_ref(v___y_1220_);
                crate::leanh::lean_inc(v___y_1219_);
                crate::leanh::lean_inc_ref(v___y_1218_);
                crate::leanh::lean_inc(v___y_1217_);
                crate::leanh::lean_inc_ref(v___y_1216_);
                crate::leanh::lean_inc(v___y_1215_);
                crate::leanh::lean_inc_ref(v___y_1214_);
                v___x_1223_ = crate::leanh::lean_apply_9(
                    v_a_1212_,
                    v___y_1214_,
                    v___y_1215_,
                    v___y_1216_,
                    v___y_1217_,
                    v___y_1218_,
                    v___y_1219_,
                    v___y_1220_,
                    v___y_1221_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_1223_) == 0 {
                    v_a_1224_ = crate::leanh::lean_ctor_get(v___x_1223_, 0);
                    v_isSharedCheck_1232_ = (!crate::leanh::lean_is_exclusive(v___x_1223_)) as u8;
                    if v_isSharedCheck_1232_ == 0 {
                        v___x_1226_ = v___x_1223_;
                        v_isShared_1227_ = v_isSharedCheck_1232_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1224_);
                        crate::leanh::lean_dec(v___x_1223_);
                        v___x_1226_ = crate::leanh::lean_box(0);
                        v_isShared_1227_ = v_isSharedCheck_1232_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_trees_1213_);
                    v_a_1233_ = crate::leanh::lean_ctor_get(v___x_1223_, 0);
                    v_isSharedCheck_1240_ = (!crate::leanh::lean_is_exclusive(v___x_1223_)) as u8;
                    if v_isSharedCheck_1240_ == 0 {
                        v___x_1235_ = v___x_1223_;
                        v_isShared_1236_ = v_isSharedCheck_1240_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1233_);
                        crate::leanh::lean_dec(v___x_1223_);
                        v___x_1235_ = crate::leanh::lean_box(0);
                        v_isShared_1236_ = v_isSharedCheck_1240_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1228_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1228_, 0, v_a_1224_);
                crate::leanh::lean_ctor_set(v___x_1228_, 1, v_trees_1213_);
                if v_isShared_1227_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1226_, 0, v___x_1228_);
                    v___x_1230_ = v___x_1226_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1231_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1231_, 0, v___x_1228_);
                    v___x_1230_ = v_reuseFailAlloc_1231_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1230_;
            }
            3 => {
                if v_isShared_1236_ == 0 {
                    v___x_1238_ = v___x_1235_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1239_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_a_1233_);
                    v___x_1238_ = v_reuseFailAlloc_1239_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1238_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalCalc___lam__4___boxed(
    mut v_a_1241_: *mut crate::leanh::LeanObject,
    mut v_trees_1242_: *mut crate::leanh::LeanObject,
    mut v___y_1243_: *mut crate::leanh::LeanObject,
    mut v___y_1244_: *mut crate::leanh::LeanObject,
    mut v___y_1245_: *mut crate::leanh::LeanObject,
    mut v___y_1246_: *mut crate::leanh::LeanObject,
    mut v___y_1247_: *mut crate::leanh::LeanObject,
    mut v___y_1248_: *mut crate::leanh::LeanObject,
    mut v___y_1249_: *mut crate::leanh::LeanObject,
    mut v___y_1250_: *mut crate::leanh::LeanObject,
    mut v___y_1251_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1252_ = l_Lean_Elab_Tactic_evalCalc___lam__4(
        v_a_1241_,
        v_trees_1242_,
        v___y_1243_,
        v___y_1244_,
        v___y_1245_,
        v___y_1246_,
        v___y_1247_,
        v___y_1248_,
        v___y_1249_,
        v___y_1250_,
    );
    crate::leanh::lean_dec(v___y_1250_);
    crate::leanh::lean_dec_ref(v___y_1249_);
    crate::leanh::lean_dec(v___y_1248_);
    crate::leanh::lean_dec_ref(v___y_1247_);
    crate::leanh::lean_dec(v___y_1246_);
    crate::leanh::lean_dec_ref(v___y_1245_);
    crate::leanh::lean_dec(v___y_1244_);
    crate::leanh::lean_dec_ref(v___y_1243_);
    return v_res_1252_;
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___redArg___lam__0(
    mut v___y_1253_: *mut crate::leanh::LeanObject,
    mut v_mkInfoTree_1254_: *mut crate::leanh::LeanObject,
    mut v___y_1255_: *mut crate::leanh::LeanObject,
    mut v___y_1256_: *mut crate::leanh::LeanObject,
    mut v___y_1257_: *mut crate::leanh::LeanObject,
    mut v___y_1258_: *mut crate::leanh::LeanObject,
    mut v___y_1259_: *mut crate::leanh::LeanObject,
    mut v___y_1260_: *mut crate::leanh::LeanObject,
    mut v___y_1261_: *mut crate::leanh::LeanObject,
    mut v_a_1262_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_1263_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trees_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1272_: u8 = 0;
    let mut v___x_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1285_: u8 = 0;
    let mut v_enabled_1286_: u8 = 0;
    let mut v_assignment_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1291_: u8 = 0;
    let mut v___x_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1304_: u8 = 0;
    let mut v_unused_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1306_: u8 = 0;
    let mut v_isSharedCheck_1307_: u8 = 0;
    let mut v_a_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1311_: u8 = 0;
    let mut v___x_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1315_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1265_ = lean_st_ref_get(v___y_1253_);
                v_infoState_1266_ = crate::leanh::lean_ctor_get(v___x_1265_, 7);
                crate::leanh::lean_inc_ref(v_infoState_1266_);
                crate::leanh::lean_dec(v___x_1265_);
                v_trees_1267_ = crate::leanh::lean_ctor_get(v_infoState_1266_, 2);
                crate::leanh::lean_inc_ref(v_trees_1267_);
                crate::leanh::lean_dec_ref(v_infoState_1266_);
                crate::leanh::lean_inc(v___y_1253_);
                crate::leanh::lean_inc_ref(v___y_1261_);
                crate::leanh::lean_inc(v___y_1260_);
                crate::leanh::lean_inc_ref(v___y_1259_);
                crate::leanh::lean_inc(v___y_1258_);
                crate::leanh::lean_inc_ref(v___y_1257_);
                crate::leanh::lean_inc(v___y_1256_);
                crate::leanh::lean_inc_ref(v___y_1255_);
                v___x_1268_ = crate::leanh::lean_apply_10(
                    v_mkInfoTree_1254_,
                    v_trees_1267_,
                    v___y_1255_,
                    v___y_1256_,
                    v___y_1257_,
                    v___y_1258_,
                    v___y_1259_,
                    v___y_1260_,
                    v___y_1261_,
                    v___y_1253_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_1268_) == 0 {
                    v_a_1269_ = crate::leanh::lean_ctor_get(v___x_1268_, 0);
                    v_isSharedCheck_1307_ = (!crate::leanh::lean_is_exclusive(v___x_1268_)) as u8;
                    if v_isSharedCheck_1307_ == 0 {
                        v___x_1271_ = v___x_1268_;
                        v_isShared_1272_ = v_isSharedCheck_1307_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1269_);
                        crate::leanh::lean_dec(v___x_1268_);
                        v___x_1271_ = crate::leanh::lean_box(0);
                        v_isShared_1272_ = v_isSharedCheck_1307_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_a_1262_);
                    v_a_1308_ = crate::leanh::lean_ctor_get(v___x_1268_, 0);
                    v_isSharedCheck_1315_ = (!crate::leanh::lean_is_exclusive(v___x_1268_)) as u8;
                    if v_isSharedCheck_1315_ == 0 {
                        v___x_1310_ = v___x_1268_;
                        v_isShared_1311_ = v_isSharedCheck_1315_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1308_);
                        crate::leanh::lean_dec(v___x_1268_);
                        v___x_1310_ = crate::leanh::lean_box(0);
                        v_isShared_1311_ = v_isSharedCheck_1315_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1273_ = lean_st_ref_take(v___y_1253_);
                v_infoState_1274_ = crate::leanh::lean_ctor_get(v___x_1273_, 7);
                v_env_1275_ = crate::leanh::lean_ctor_get(v___x_1273_, 0);
                v_nextMacroScope_1276_ = crate::leanh::lean_ctor_get(v___x_1273_, 1);
                v_ngen_1277_ = crate::leanh::lean_ctor_get(v___x_1273_, 2);
                v_auxDeclNGen_1278_ = crate::leanh::lean_ctor_get(v___x_1273_, 3);
                v_traceState_1279_ = crate::leanh::lean_ctor_get(v___x_1273_, 4);
                v_cache_1280_ = crate::leanh::lean_ctor_get(v___x_1273_, 5);
                v_messages_1281_ = crate::leanh::lean_ctor_get(v___x_1273_, 6);
                v_snapshotTasks_1282_ = crate::leanh::lean_ctor_get(v___x_1273_, 8);
                v_isSharedCheck_1306_ = (!crate::leanh::lean_is_exclusive(v___x_1273_)) as u8;
                if v_isSharedCheck_1306_ == 0 {
                    v___x_1284_ = v___x_1273_;
                    v_isShared_1285_ = v_isSharedCheck_1306_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_1282_);
                    crate::leanh::lean_inc(v_infoState_1274_);
                    crate::leanh::lean_inc(v_messages_1281_);
                    crate::leanh::lean_inc(v_cache_1280_);
                    crate::leanh::lean_inc(v_traceState_1279_);
                    crate::leanh::lean_inc(v_auxDeclNGen_1278_);
                    crate::leanh::lean_inc(v_ngen_1277_);
                    crate::leanh::lean_inc(v_nextMacroScope_1276_);
                    crate::leanh::lean_inc(v_env_1275_);
                    crate::leanh::lean_dec(v___x_1273_);
                    v___x_1284_ = crate::leanh::lean_box(0);
                    v_isShared_1285_ = v_isSharedCheck_1306_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_enabled_1286_ = crate::leanh::lean_ctor_get_uint8(
                    v_infoState_1274_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_assignment_1287_ = crate::leanh::lean_ctor_get(v_infoState_1274_, 0);
                v_lazyAssignment_1288_ = crate::leanh::lean_ctor_get(v_infoState_1274_, 1);
                v_isSharedCheck_1304_ = (!crate::leanh::lean_is_exclusive(v_infoState_1274_)) as u8;
                if v_isSharedCheck_1304_ == 0 {
                    v_unused_1305_ = crate::leanh::lean_ctor_get(v_infoState_1274_, 2);
                    crate::leanh::lean_dec(v_unused_1305_);
                    v___x_1290_ = v_infoState_1274_;
                    v_isShared_1291_ = v_isSharedCheck_1304_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_lazyAssignment_1288_);
                    crate::leanh::lean_inc(v_assignment_1287_);
                    crate::leanh::lean_dec(v_infoState_1274_);
                    v___x_1290_ = crate::leanh::lean_box(0);
                    v_isShared_1291_ = v_isSharedCheck_1304_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1292_ = l_Lean_PersistentArray_push___redArg(v_a_1262_, v_a_1269_);
                if v_isShared_1291_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1290_, 2, v___x_1292_);
                    v___x_1294_ = v___x_1290_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1303_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1303_, 0, v_assignment_1287_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1303_, 1, v_lazyAssignment_1288_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1303_, 2, v___x_1292_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1303_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_enabled_1286_,
                    );
                    v___x_1294_ = v_reuseFailAlloc_1303_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1285_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1284_, 7, v___x_1294_);
                    v___x_1296_ = v___x_1284_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1302_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_env_1275_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1302_, 1, v_nextMacroScope_1276_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1302_, 2, v_ngen_1277_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1302_, 3, v_auxDeclNGen_1278_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1302_, 4, v_traceState_1279_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1302_, 5, v_cache_1280_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1302_, 6, v_messages_1281_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1302_, 7, v___x_1294_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1302_, 8, v_snapshotTasks_1282_);
                    v___x_1296_ = v_reuseFailAlloc_1302_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1297_ = lean_st_ref_set(v___y_1253_, v___x_1296_);
                v___x_1298_ = crate::leanh::lean_box(0);
                if v_isShared_1272_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1271_, 0, v___x_1298_);
                    v___x_1300_ = v___x_1271_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1301_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1301_, 0, v___x_1298_);
                    v___x_1300_ = v_reuseFailAlloc_1301_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1300_;
            }
            7 => {
                if v_isShared_1311_ == 0 {
                    v___x_1313_ = v___x_1310_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1314_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1314_, 0, v_a_1308_);
                    v___x_1313_ = v_reuseFailAlloc_1314_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1313_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___redArg___lam__0___boxed(
    mut v___y_1316_: *mut crate::leanh::LeanObject,
    mut v_mkInfoTree_1317_: *mut crate::leanh::LeanObject,
    mut v___y_1318_: *mut crate::leanh::LeanObject,
    mut v___y_1319_: *mut crate::leanh::LeanObject,
    mut v___y_1320_: *mut crate::leanh::LeanObject,
    mut v___y_1321_: *mut crate::leanh::LeanObject,
    mut v___y_1322_: *mut crate::leanh::LeanObject,
    mut v___y_1323_: *mut crate::leanh::LeanObject,
    mut v___y_1324_: *mut crate::leanh::LeanObject,
    mut v_a_1325_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_1326_: *mut crate::leanh::LeanObject,
    mut v___y_1327_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1328_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___redArg___lam__0(v___y_1316_, v_mkInfoTree_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v_a_1325_, v_a_x3f_1326_);
    crate::leanh::lean_dec(v_a_x3f_1326_);
    crate::leanh::lean_dec_ref(v___y_1324_);
    crate::leanh::lean_dec(v___y_1323_);
    crate::leanh::lean_dec_ref(v___y_1322_);
    crate::leanh::lean_dec(v___y_1321_);
    crate::leanh::lean_dec_ref(v___y_1320_);
    crate::leanh::lean_dec(v___y_1319_);
    crate::leanh::lean_dec_ref(v___y_1318_);
    crate::leanh::lean_dec(v___y_1316_);
    return v_res_1328_;
}
pub unsafe fn _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1329_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1330_ = lean_mk_empty_array_with_capacity(v___x_1329_);
    v___x_1331_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1331_, 0, v___x_1330_);
    return v___x_1331_;
}
pub unsafe fn _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1332_: usize = 0;
    let mut v___x_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1332_ = 5usize;
    v___x_1333_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1334_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1335_ = lean_mk_empty_array_with_capacity(v___x_1334_);
    v___x_1336_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg___closed__0_once), _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg___closed__0);
    v___x_1337_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_1337_, 0, v___x_1336_);
    crate::leanh::lean_ctor_set(v___x_1337_, 1, v___x_1335_);
    crate::leanh::lean_ctor_set(v___x_1337_, 2, v___x_1333_);
    crate::leanh::lean_ctor_set(v___x_1337_, 3, v___x_1333_);
    crate::leanh::lean_ctor_set_usize(v___x_1337_, 4, v___x_1332_);
    return v___x_1337_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg(
    mut v___y_1338_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trees_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1355_: u8 = 0;
    let mut v_enabled_1356_: u8 = 0;
    let mut v_assignment_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1361_: u8 = 0;
    let mut v___x_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1371_: u8 = 0;
    let mut v_unused_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1373_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1340_ = lean_st_ref_get(v___y_1338_);
                v_infoState_1341_ = crate::leanh::lean_ctor_get(v___x_1340_, 7);
                crate::leanh::lean_inc_ref(v_infoState_1341_);
                crate::leanh::lean_dec(v___x_1340_);
                v_trees_1342_ = crate::leanh::lean_ctor_get(v_infoState_1341_, 2);
                crate::leanh::lean_inc_ref(v_trees_1342_);
                crate::leanh::lean_dec_ref(v_infoState_1341_);
                v___x_1343_ = lean_st_ref_take(v___y_1338_);
                v_infoState_1344_ = crate::leanh::lean_ctor_get(v___x_1343_, 7);
                v_env_1345_ = crate::leanh::lean_ctor_get(v___x_1343_, 0);
                v_nextMacroScope_1346_ = crate::leanh::lean_ctor_get(v___x_1343_, 1);
                v_ngen_1347_ = crate::leanh::lean_ctor_get(v___x_1343_, 2);
                v_auxDeclNGen_1348_ = crate::leanh::lean_ctor_get(v___x_1343_, 3);
                v_traceState_1349_ = crate::leanh::lean_ctor_get(v___x_1343_, 4);
                v_cache_1350_ = crate::leanh::lean_ctor_get(v___x_1343_, 5);
                v_messages_1351_ = crate::leanh::lean_ctor_get(v___x_1343_, 6);
                v_snapshotTasks_1352_ = crate::leanh::lean_ctor_get(v___x_1343_, 8);
                v_isSharedCheck_1373_ = (!crate::leanh::lean_is_exclusive(v___x_1343_)) as u8;
                if v_isSharedCheck_1373_ == 0 {
                    v___x_1354_ = v___x_1343_;
                    v_isShared_1355_ = v_isSharedCheck_1373_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_1352_);
                    crate::leanh::lean_inc(v_infoState_1344_);
                    crate::leanh::lean_inc(v_messages_1351_);
                    crate::leanh::lean_inc(v_cache_1350_);
                    crate::leanh::lean_inc(v_traceState_1349_);
                    crate::leanh::lean_inc(v_auxDeclNGen_1348_);
                    crate::leanh::lean_inc(v_ngen_1347_);
                    crate::leanh::lean_inc(v_nextMacroScope_1346_);
                    crate::leanh::lean_inc(v_env_1345_);
                    crate::leanh::lean_dec(v___x_1343_);
                    v___x_1354_ = crate::leanh::lean_box(0);
                    v_isShared_1355_ = v_isSharedCheck_1373_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_enabled_1356_ = crate::leanh::lean_ctor_get_uint8(
                    v_infoState_1344_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_assignment_1357_ = crate::leanh::lean_ctor_get(v_infoState_1344_, 0);
                v_lazyAssignment_1358_ = crate::leanh::lean_ctor_get(v_infoState_1344_, 1);
                v_isSharedCheck_1371_ = (!crate::leanh::lean_is_exclusive(v_infoState_1344_)) as u8;
                if v_isSharedCheck_1371_ == 0 {
                    v_unused_1372_ = crate::leanh::lean_ctor_get(v_infoState_1344_, 2);
                    crate::leanh::lean_dec(v_unused_1372_);
                    v___x_1360_ = v_infoState_1344_;
                    v_isShared_1361_ = v_isSharedCheck_1371_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_lazyAssignment_1358_);
                    crate::leanh::lean_inc(v_assignment_1357_);
                    crate::leanh::lean_dec(v_infoState_1344_);
                    v___x_1360_ = crate::leanh::lean_box(0);
                    v_isShared_1361_ = v_isSharedCheck_1371_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1362_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg___closed__1_once), _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg___closed__1);
                if v_isShared_1361_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1360_, 2, v___x_1362_);
                    v___x_1364_ = v___x_1360_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1370_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_assignment_1357_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1370_, 1, v_lazyAssignment_1358_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1370_, 2, v___x_1362_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1370_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_enabled_1356_,
                    );
                    v___x_1364_ = v_reuseFailAlloc_1370_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1355_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1354_, 7, v___x_1364_);
                    v___x_1366_ = v___x_1354_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1369_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_env_1345_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1369_, 1, v_nextMacroScope_1346_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1369_, 2, v_ngen_1347_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1369_, 3, v_auxDeclNGen_1348_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1369_, 4, v_traceState_1349_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1369_, 5, v_cache_1350_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1369_, 6, v_messages_1351_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1369_, 7, v___x_1364_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1369_, 8, v_snapshotTasks_1352_);
                    v___x_1366_ = v_reuseFailAlloc_1369_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1367_ = lean_st_ref_set(v___y_1338_, v___x_1366_);
                v___x_1368_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1368_, 0, v_trees_1342_);
                return v___x_1368_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg___boxed(
    mut v___y_1374_: *mut crate::leanh::LeanObject,
    mut v___y_1375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1376_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg(v___y_1374_);
    crate::leanh::lean_dec(v___y_1374_);
    return v_res_1376_;
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___redArg(
    mut v_x_1377_: *mut crate::leanh::LeanObject,
    mut v_mkInfoTree_1378_: *mut crate::leanh::LeanObject,
    mut v___y_1379_: *mut crate::leanh::LeanObject,
    mut v___y_1380_: *mut crate::leanh::LeanObject,
    mut v___y_1381_: *mut crate::leanh::LeanObject,
    mut v___y_1382_: *mut crate::leanh::LeanObject,
    mut v___y_1383_: *mut crate::leanh::LeanObject,
    mut v___y_1384_: *mut crate::leanh::LeanObject,
    mut v___y_1385_: *mut crate::leanh::LeanObject,
    mut v___y_1386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_1390_: u8 = 0;
    let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1398_: u8 = 0;
    let mut v___x_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1404_: u8 = 0;
    let mut v___x_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1408_: u8 = 0;
    let mut v_unused_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1413_: u8 = 0;
    let mut v___x_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1417_: u8 = 0;
    let mut v_reuseFailAlloc_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1419_: u8 = 0;
    let mut v_a_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1425_: u8 = 0;
    let mut v___x_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1429_: u8 = 0;
    let mut v_unused_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1434_: u8 = 0;
    let mut v___x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1438_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1388_ = lean_st_ref_get(v___y_1386_);
                v_infoState_1389_ = crate::leanh::lean_ctor_get(v___x_1388_, 7);
                crate::leanh::lean_inc_ref(v_infoState_1389_);
                crate::leanh::lean_dec(v___x_1388_);
                v_enabled_1390_ = crate::leanh::lean_ctor_get_uint8(
                    v_infoState_1389_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                crate::leanh::lean_dec_ref(v_infoState_1389_);
                if v_enabled_1390_ == 0 {
                    crate::leanh::lean_dec_ref(v_mkInfoTree_1378_);
                    crate::leanh::lean_inc(v___y_1386_);
                    crate::leanh::lean_inc_ref(v___y_1385_);
                    crate::leanh::lean_inc(v___y_1384_);
                    crate::leanh::lean_inc_ref(v___y_1383_);
                    crate::leanh::lean_inc(v___y_1382_);
                    crate::leanh::lean_inc_ref(v___y_1381_);
                    crate::leanh::lean_inc(v___y_1380_);
                    crate::leanh::lean_inc_ref(v___y_1379_);
                    v___x_1391_ = crate::leanh::lean_apply_9(
                        v_x_1377_,
                        v___y_1379_,
                        v___y_1380_,
                        v___y_1381_,
                        v___y_1382_,
                        v___y_1383_,
                        v___y_1384_,
                        v___y_1385_,
                        v___y_1386_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_1391_;
                } else {
                    v___x_1392_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg(v___y_1386_);
                    v_a_1393_ = crate::leanh::lean_ctor_get(v___x_1392_, 0);
                    crate::leanh::lean_inc(v_a_1393_);
                    crate::leanh::lean_dec_ref(v___x_1392_);
                    crate::leanh::lean_inc(v___y_1386_);
                    crate::leanh::lean_inc_ref(v___y_1385_);
                    crate::leanh::lean_inc(v___y_1384_);
                    crate::leanh::lean_inc_ref(v___y_1383_);
                    crate::leanh::lean_inc(v___y_1382_);
                    crate::leanh::lean_inc_ref(v___y_1381_);
                    crate::leanh::lean_inc(v___y_1380_);
                    crate::leanh::lean_inc_ref(v___y_1379_);
                    v_r_1394_ = crate::leanh::lean_apply_9(
                        v_x_1377_,
                        v___y_1379_,
                        v___y_1380_,
                        v___y_1381_,
                        v___y_1382_,
                        v___y_1383_,
                        v___y_1384_,
                        v___y_1385_,
                        v___y_1386_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v_r_1394_) == 0 {
                        v_a_1395_ = crate::leanh::lean_ctor_get(v_r_1394_, 0);
                        v_isSharedCheck_1419_ = (!crate::leanh::lean_is_exclusive(v_r_1394_)) as u8;
                        if v_isSharedCheck_1419_ == 0 {
                            v___x_1397_ = v_r_1394_;
                            v_isShared_1398_ = v_isSharedCheck_1419_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1395_);
                            crate::leanh::lean_dec(v_r_1394_);
                            v___x_1397_ = crate::leanh::lean_box(0);
                            v_isShared_1398_ = v_isSharedCheck_1419_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1420_ = crate::leanh::lean_ctor_get(v_r_1394_, 0);
                        crate::leanh::lean_inc(v_a_1420_);
                        crate::leanh::lean_dec_ref_known(v_r_1394_, 1);
                        v___x_1421_ = crate::leanh::lean_box(0);
                        v___x_1422_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___redArg___lam__0(v___y_1386_, v_mkInfoTree_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v_a_1393_, v___x_1421_);
                        if crate::leanh::lean_obj_tag(v___x_1422_) == 0 {
                            v_isSharedCheck_1429_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1422_)) as u8;
                            if v_isSharedCheck_1429_ == 0 {
                                v_unused_1430_ = crate::leanh::lean_ctor_get(v___x_1422_, 0);
                                crate::leanh::lean_dec(v_unused_1430_);
                                v___x_1424_ = v___x_1422_;
                                v_isShared_1425_ = v_isSharedCheck_1429_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_1422_);
                                v___x_1424_ = crate::leanh::lean_box(0);
                                v_isShared_1425_ = v_isSharedCheck_1429_;
                                state = 7;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_1420_);
                            v_a_1431_ = crate::leanh::lean_ctor_get(v___x_1422_, 0);
                            v_isSharedCheck_1438_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1422_)) as u8;
                            if v_isSharedCheck_1438_ == 0 {
                                v___x_1433_ = v___x_1422_;
                                v_isShared_1434_ = v_isSharedCheck_1438_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1431_);
                                crate::leanh::lean_dec(v___x_1422_);
                                v___x_1433_ = crate::leanh::lean_box(0);
                                v_isShared_1434_ = v_isSharedCheck_1438_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_a_1395_);
                if v_isShared_1398_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1397_, 1);
                    v___x_1400_ = v___x_1397_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1418_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_a_1395_);
                    v___x_1400_ = v_reuseFailAlloc_1418_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1401_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___redArg___lam__0(v___y_1386_, v_mkInfoTree_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v_a_1393_, v___x_1400_);
                crate::leanh::lean_dec_ref(v___x_1400_);
                if crate::leanh::lean_obj_tag(v___x_1401_) == 0 {
                    v_isSharedCheck_1408_ = (!crate::leanh::lean_is_exclusive(v___x_1401_)) as u8;
                    if v_isSharedCheck_1408_ == 0 {
                        v_unused_1409_ = crate::leanh::lean_ctor_get(v___x_1401_, 0);
                        crate::leanh::lean_dec(v_unused_1409_);
                        v___x_1403_ = v___x_1401_;
                        v_isShared_1404_ = v_isSharedCheck_1408_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_1401_);
                        v___x_1403_ = crate::leanh::lean_box(0);
                        v_isShared_1404_ = v_isSharedCheck_1408_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1395_);
                    v_a_1410_ = crate::leanh::lean_ctor_get(v___x_1401_, 0);
                    v_isSharedCheck_1417_ = (!crate::leanh::lean_is_exclusive(v___x_1401_)) as u8;
                    if v_isSharedCheck_1417_ == 0 {
                        v___x_1412_ = v___x_1401_;
                        v_isShared_1413_ = v_isSharedCheck_1417_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1410_);
                        crate::leanh::lean_dec(v___x_1401_);
                        v___x_1412_ = crate::leanh::lean_box(0);
                        v_isShared_1413_ = v_isSharedCheck_1417_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_1404_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1403_, 0, v_a_1395_);
                    v___x_1406_ = v___x_1403_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1407_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1407_, 0, v_a_1395_);
                    v___x_1406_ = v_reuseFailAlloc_1407_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1406_;
            }
            5 => {
                if v_isShared_1413_ == 0 {
                    v___x_1415_ = v___x_1412_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1416_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_a_1410_);
                    v___x_1415_ = v_reuseFailAlloc_1416_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1415_;
            }
            7 => {
                if v_isShared_1425_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1424_, 1);
                    crate::leanh::lean_ctor_set(v___x_1424_, 0, v_a_1420_);
                    v___x_1427_ = v___x_1424_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1428_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_a_1420_);
                    v___x_1427_ = v_reuseFailAlloc_1428_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1427_;
            }
            9 => {
                if v_isShared_1434_ == 0 {
                    v___x_1436_ = v___x_1433_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1437_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_a_1431_);
                    v___x_1436_ = v_reuseFailAlloc_1437_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1436_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___redArg___boxed(
    mut v_x_1439_: *mut crate::leanh::LeanObject,
    mut v_mkInfoTree_1440_: *mut crate::leanh::LeanObject,
    mut v___y_1441_: *mut crate::leanh::LeanObject,
    mut v___y_1442_: *mut crate::leanh::LeanObject,
    mut v___y_1443_: *mut crate::leanh::LeanObject,
    mut v___y_1444_: *mut crate::leanh::LeanObject,
    mut v___y_1445_: *mut crate::leanh::LeanObject,
    mut v___y_1446_: *mut crate::leanh::LeanObject,
    mut v___y_1447_: *mut crate::leanh::LeanObject,
    mut v___y_1448_: *mut crate::leanh::LeanObject,
    mut v___y_1449_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1450_ =
        l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___redArg(
            v_x_1439_,
            v_mkInfoTree_1440_,
            v___y_1441_,
            v___y_1442_,
            v___y_1443_,
            v___y_1444_,
            v___y_1445_,
            v___y_1446_,
            v___y_1447_,
            v___y_1448_,
        );
    crate::leanh::lean_dec(v___y_1448_);
    crate::leanh::lean_dec_ref(v___y_1447_);
    crate::leanh::lean_dec(v___y_1446_);
    crate::leanh::lean_dec_ref(v___y_1445_);
    crate::leanh::lean_dec(v___y_1444_);
    crate::leanh::lean_dec_ref(v___y_1443_);
    crate::leanh::lean_dec(v___y_1442_);
    crate::leanh::lean_dec_ref(v___y_1441_);
    return v_res_1450_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalCalc___lam__5(
    mut v_steps_1451_: *mut crate::leanh::LeanObject,
    mut v___x_1452_: *mut crate::leanh::LeanObject,
    mut v___x_1453_: *mut crate::leanh::LeanObject,
    mut v_target_1454_: *mut crate::leanh::LeanObject,
    mut v_tag_1455_: *mut crate::leanh::LeanObject,
    mut v___y_1456_: *mut crate::leanh::LeanObject,
    mut v___y_1457_: *mut crate::leanh::LeanObject,
    mut v___y_1458_: *mut crate::leanh::LeanObject,
    mut v___y_1459_: *mut crate::leanh::LeanObject,
    mut v___y_1460_: *mut crate::leanh::LeanObject,
    mut v___y_1461_: *mut crate::leanh::LeanObject,
    mut v___y_1462_: *mut crate::leanh::LeanObject,
    mut v___y_1463_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1473_: u8 = 0;
    let mut v___x_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1477_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_steps_1451_);
                v___x_1465_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(
                    v_steps_1451_,
                    v___y_1456_,
                    v___y_1457_,
                    v___y_1458_,
                    v___y_1459_,
                    v___y_1460_,
                    v___y_1461_,
                    v___y_1462_,
                    v___y_1463_,
                );
                if crate::leanh::lean_obj_tag(v___x_1465_) == 0 {
                    v_a_1466_ = crate::leanh::lean_ctor_get(v___x_1465_, 0);
                    crate::leanh::lean_inc(v_a_1466_);
                    crate::leanh::lean_dec_ref_known(v___x_1465_, 1);
                    v___f_1467_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Elab_Tactic_evalCalc___lam__3___boxed as *mut core::ffi::c_void,
                        14,
                        5,
                    );
                    crate::leanh::lean_closure_set(v___f_1467_, 0, v_steps_1451_);
                    crate::leanh::lean_closure_set(v___f_1467_, 1, v_target_1454_);
                    crate::leanh::lean_closure_set(v___f_1467_, 2, v___x_1452_);
                    crate::leanh::lean_closure_set(v___f_1467_, 3, v_tag_1455_);
                    crate::leanh::lean_closure_set(v___f_1467_, 4, v___x_1453_);
                    v___f_1468_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Elab_Tactic_evalCalc___lam__4___boxed as *mut core::ffi::c_void,
                        11,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_1468_, 0, v_a_1466_);
                    v___x_1469_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___redArg(v___f_1467_, v___f_1468_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
                    return v___x_1469_;
                } else {
                    crate::leanh::lean_dec(v_tag_1455_);
                    crate::leanh::lean_dec_ref(v_target_1454_);
                    crate::leanh::lean_dec(v___x_1453_);
                    crate::leanh::lean_dec_ref(v___x_1452_);
                    crate::leanh::lean_dec(v_steps_1451_);
                    v_a_1470_ = crate::leanh::lean_ctor_get(v___x_1465_, 0);
                    v_isSharedCheck_1477_ = (!crate::leanh::lean_is_exclusive(v___x_1465_)) as u8;
                    if v_isSharedCheck_1477_ == 0 {
                        v___x_1472_ = v___x_1465_;
                        v_isShared_1473_ = v_isSharedCheck_1477_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1470_);
                        crate::leanh::lean_dec(v___x_1465_);
                        v___x_1472_ = crate::leanh::lean_box(0);
                        v_isShared_1473_ = v_isSharedCheck_1477_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1473_ == 0 {
                    v___x_1475_ = v___x_1472_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1476_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_a_1470_);
                    v___x_1475_ = v_reuseFailAlloc_1476_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1475_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalCalc___lam__5___boxed(
    mut v_steps_1478_: *mut crate::leanh::LeanObject,
    mut v___x_1479_: *mut crate::leanh::LeanObject,
    mut v___x_1480_: *mut crate::leanh::LeanObject,
    mut v_target_1481_: *mut crate::leanh::LeanObject,
    mut v_tag_1482_: *mut crate::leanh::LeanObject,
    mut v___y_1483_: *mut crate::leanh::LeanObject,
    mut v___y_1484_: *mut crate::leanh::LeanObject,
    mut v___y_1485_: *mut crate::leanh::LeanObject,
    mut v___y_1486_: *mut crate::leanh::LeanObject,
    mut v___y_1487_: *mut crate::leanh::LeanObject,
    mut v___y_1488_: *mut crate::leanh::LeanObject,
    mut v___y_1489_: *mut crate::leanh::LeanObject,
    mut v___y_1490_: *mut crate::leanh::LeanObject,
    mut v___y_1491_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1492_ = l_Lean_Elab_Tactic_evalCalc___lam__5(
        v_steps_1478_,
        v___x_1479_,
        v___x_1480_,
        v_target_1481_,
        v_tag_1482_,
        v___y_1483_,
        v___y_1484_,
        v___y_1485_,
        v___y_1486_,
        v___y_1487_,
        v___y_1488_,
        v___y_1489_,
        v___y_1490_,
    );
    crate::leanh::lean_dec(v___y_1490_);
    crate::leanh::lean_dec_ref(v___y_1489_);
    crate::leanh::lean_dec(v___y_1488_);
    crate::leanh::lean_dec_ref(v___y_1487_);
    crate::leanh::lean_dec(v___y_1486_);
    crate::leanh::lean_dec_ref(v___y_1485_);
    crate::leanh::lean_dec(v___y_1484_);
    crate::leanh::lean_dec_ref(v___y_1483_);
    return v_res_1492_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalCalc(
    mut v_x_1505_: *mut crate::leanh::LeanObject,
    mut v_a_1506_: *mut crate::leanh::LeanObject,
    mut v_a_1507_: *mut crate::leanh::LeanObject,
    mut v_a_1508_: *mut crate::leanh::LeanObject,
    mut v_a_1509_: *mut crate::leanh::LeanObject,
    mut v_a_1510_: *mut crate::leanh::LeanObject,
    mut v_a_1511_: *mut crate::leanh::LeanObject,
    mut v_a_1512_: *mut crate::leanh::LeanObject,
    mut v_a_1513_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: u8 = 0;
    v___x_1515_ = l_Lean_Elab_Tactic_evalCalc___closed__2;
    crate::leanh::lean_inc(v_x_1505_);
    v___x_1516_ = l_Lean_Syntax_isOfKind(v_x_1505_, v___x_1515_);
    if v___x_1516_ == 0 {
        let mut v___x_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_1505_);
        v___x_1517_ =
            l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0___redArg(
            );
        return v___x_1517_;
    } else {
        let mut v___x_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_steps_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1521_: u8 = 0;
        v___x_1518_ = crate::leanh::lean_unsigned_to_nat(1);
        v_steps_1519_ = l_Lean_Syntax_getArg(v_x_1505_, v___x_1518_);
        v___x_1520_ = l_Lean_Elab_Tactic_evalCalc___closed__4;
        crate::leanh::lean_inc(v_steps_1519_);
        v___x_1521_ = l_Lean_Syntax_isOfKind(v_steps_1519_, v___x_1520_);
        if v___x_1521_ == 0 {
            let mut v___x_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_steps_1519_);
            crate::leanh::lean_dec(v_x_1505_);
            v___x_1522_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0___redArg();
            return v___x_1522_;
        } else {
            let mut v_fileName_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_fileMap_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_options_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_currRecDepth_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_maxRecDepth_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_ref_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_currNamespace_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_openDecls_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_initHeartbeats_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_maxHeartbeats_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_quotContext_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_currMacroScope_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_diag_1535_: u8 = 0;
            let mut v_cancelTk_x3f_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_suppressElabErrors_1537_: u8 = 0;
            let mut v_inheritedTraceOptions_1538_: *mut crate::leanh::LeanObject =
                core::ptr::null_mut();
            let mut v___x_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tk_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1544_: u8 = 0;
            let mut v_ref_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_fileName_1523_ = crate::leanh::lean_ctor_get(v_a_1512_, 0);
            v_fileMap_1524_ = crate::leanh::lean_ctor_get(v_a_1512_, 1);
            v_options_1525_ = crate::leanh::lean_ctor_get(v_a_1512_, 2);
            v_currRecDepth_1526_ = crate::leanh::lean_ctor_get(v_a_1512_, 3);
            v_maxRecDepth_1527_ = crate::leanh::lean_ctor_get(v_a_1512_, 4);
            v_ref_1528_ = crate::leanh::lean_ctor_get(v_a_1512_, 5);
            v_currNamespace_1529_ = crate::leanh::lean_ctor_get(v_a_1512_, 6);
            v_openDecls_1530_ = crate::leanh::lean_ctor_get(v_a_1512_, 7);
            v_initHeartbeats_1531_ = crate::leanh::lean_ctor_get(v_a_1512_, 8);
            v_maxHeartbeats_1532_ = crate::leanh::lean_ctor_get(v_a_1512_, 9);
            v_quotContext_1533_ = crate::leanh::lean_ctor_get(v_a_1512_, 10);
            v_currMacroScope_1534_ = crate::leanh::lean_ctor_get(v_a_1512_, 11);
            v_diag_1535_ = crate::leanh::lean_ctor_get_uint8(
                v_a_1512_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
            );
            v_cancelTk_x3f_1536_ = crate::leanh::lean_ctor_get(v_a_1512_, 12);
            v_suppressElabErrors_1537_ = crate::leanh::lean_ctor_get_uint8(
                v_a_1512_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
            );
            v_inheritedTraceOptions_1538_ = crate::leanh::lean_ctor_get(v_a_1512_, 13);
            v___x_1539_ = crate::leanh::lean_unsigned_to_nat(0);
            v_tk_1540_ = l_Lean_Syntax_getArg(v_x_1505_, v___x_1539_);
            crate::leanh::lean_dec(v_x_1505_);
            v___x_1541_ = l_Lean_Elab_Tactic_evalCalc___closed__5;
            v___x_1542_ = l_Lean_Elab_Tactic_evalCalc___closed__6;
            v___f_1543_ = crate::leanh::lean_alloc_closure(
                l_Lean_Elab_Tactic_evalCalc___lam__5___boxed as *mut core::ffi::c_void,
                14,
                3,
            );
            crate::leanh::lean_closure_set(v___f_1543_, 0, v_steps_1519_);
            crate::leanh::lean_closure_set(v___f_1543_, 1, v___x_1541_);
            crate::leanh::lean_closure_set(v___f_1543_, 2, v___x_1542_);
            v___x_1544_ = 0;
            v_ref_1545_ = l_Lean_replaceRef(v_tk_1540_, v_ref_1528_);
            crate::leanh::lean_dec(v_tk_1540_);
            crate::leanh::lean_inc_ref(v_inheritedTraceOptions_1538_);
            crate::leanh::lean_inc(v_cancelTk_x3f_1536_);
            crate::leanh::lean_inc(v_currMacroScope_1534_);
            crate::leanh::lean_inc(v_quotContext_1533_);
            crate::leanh::lean_inc(v_maxHeartbeats_1532_);
            crate::leanh::lean_inc(v_initHeartbeats_1531_);
            crate::leanh::lean_inc(v_openDecls_1530_);
            crate::leanh::lean_inc(v_currNamespace_1529_);
            crate::leanh::lean_inc(v_maxRecDepth_1527_);
            crate::leanh::lean_inc(v_currRecDepth_1526_);
            crate::leanh::lean_inc_ref(v_options_1525_);
            crate::leanh::lean_inc_ref(v_fileMap_1524_);
            crate::leanh::lean_inc_ref(v_fileName_1523_);
            v___x_1546_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
            crate::leanh::lean_ctor_set(v___x_1546_, 0, v_fileName_1523_);
            crate::leanh::lean_ctor_set(v___x_1546_, 1, v_fileMap_1524_);
            crate::leanh::lean_ctor_set(v___x_1546_, 2, v_options_1525_);
            crate::leanh::lean_ctor_set(v___x_1546_, 3, v_currRecDepth_1526_);
            crate::leanh::lean_ctor_set(v___x_1546_, 4, v_maxRecDepth_1527_);
            crate::leanh::lean_ctor_set(v___x_1546_, 5, v_ref_1545_);
            crate::leanh::lean_ctor_set(v___x_1546_, 6, v_currNamespace_1529_);
            crate::leanh::lean_ctor_set(v___x_1546_, 7, v_openDecls_1530_);
            crate::leanh::lean_ctor_set(v___x_1546_, 8, v_initHeartbeats_1531_);
            crate::leanh::lean_ctor_set(v___x_1546_, 9, v_maxHeartbeats_1532_);
            crate::leanh::lean_ctor_set(v___x_1546_, 10, v_quotContext_1533_);
            crate::leanh::lean_ctor_set(v___x_1546_, 11, v_currMacroScope_1534_);
            crate::leanh::lean_ctor_set(v___x_1546_, 12, v_cancelTk_x3f_1536_);
            crate::leanh::lean_ctor_set(v___x_1546_, 13, v_inheritedTraceOptions_1538_);
            crate::leanh::lean_ctor_set_uint8(
                v___x_1546_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                v_diag_1535_,
            );
            crate::leanh::lean_ctor_set_uint8(
                v___x_1546_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                v_suppressElabErrors_1537_,
            );
            v___x_1547_ = l_Lean_Elab_Tactic_closeMainGoalUsing(
                v___x_1542_,
                v___f_1543_,
                v___x_1544_,
                v_a_1506_,
                v_a_1507_,
                v_a_1508_,
                v_a_1509_,
                v_a_1510_,
                v_a_1511_,
                v___x_1546_,
                v_a_1513_,
            );
            crate::leanh::lean_dec_ref_known(v___x_1546_, 14);
            return v___x_1547_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalCalc___boxed(
    mut v_x_1548_: *mut crate::leanh::LeanObject,
    mut v_a_1549_: *mut crate::leanh::LeanObject,
    mut v_a_1550_: *mut crate::leanh::LeanObject,
    mut v_a_1551_: *mut crate::leanh::LeanObject,
    mut v_a_1552_: *mut crate::leanh::LeanObject,
    mut v_a_1553_: *mut crate::leanh::LeanObject,
    mut v_a_1554_: *mut crate::leanh::LeanObject,
    mut v_a_1555_: *mut crate::leanh::LeanObject,
    mut v_a_1556_: *mut crate::leanh::LeanObject,
    mut v_a_1557_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1558_ = l_Lean_Elab_Tactic_evalCalc(
        v_x_1548_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_,
        v_a_1556_,
    );
    crate::leanh::lean_dec(v_a_1556_);
    crate::leanh::lean_dec_ref(v_a_1555_);
    crate::leanh::lean_dec(v_a_1554_);
    crate::leanh::lean_dec_ref(v_a_1553_);
    crate::leanh::lean_dec(v_a_1552_);
    crate::leanh::lean_dec_ref(v_a_1551_);
    crate::leanh::lean_dec(v_a_1550_);
    crate::leanh::lean_dec_ref(v_a_1549_);
    return v_res_1558_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3(
    mut v___y_1559_: *mut crate::leanh::LeanObject,
    mut v___y_1560_: *mut crate::leanh::LeanObject,
    mut v___y_1561_: *mut crate::leanh::LeanObject,
    mut v___y_1562_: *mut crate::leanh::LeanObject,
    mut v___y_1563_: *mut crate::leanh::LeanObject,
    mut v___y_1564_: *mut crate::leanh::LeanObject,
    mut v___y_1565_: *mut crate::leanh::LeanObject,
    mut v___y_1566_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1568_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg(v___y_1566_);
    return v___x_1568_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___boxed(
    mut v___y_1569_: *mut crate::leanh::LeanObject,
    mut v___y_1570_: *mut crate::leanh::LeanObject,
    mut v___y_1571_: *mut crate::leanh::LeanObject,
    mut v___y_1572_: *mut crate::leanh::LeanObject,
    mut v___y_1573_: *mut crate::leanh::LeanObject,
    mut v___y_1574_: *mut crate::leanh::LeanObject,
    mut v___y_1575_: *mut crate::leanh::LeanObject,
    mut v___y_1576_: *mut crate::leanh::LeanObject,
    mut v___y_1577_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1578_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3(v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_);
    crate::leanh::lean_dec(v___y_1576_);
    crate::leanh::lean_dec_ref(v___y_1575_);
    crate::leanh::lean_dec(v___y_1574_);
    crate::leanh::lean_dec_ref(v___y_1573_);
    crate::leanh::lean_dec(v___y_1572_);
    crate::leanh::lean_dec_ref(v___y_1571_);
    crate::leanh::lean_dec(v___y_1570_);
    crate::leanh::lean_dec_ref(v___y_1569_);
    return v_res_1578_;
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3(
    mut v_00_u03b1_1579_: *mut crate::leanh::LeanObject,
    mut v_x_1580_: *mut crate::leanh::LeanObject,
    mut v_mkInfoTree_1581_: *mut crate::leanh::LeanObject,
    mut v___y_1582_: *mut crate::leanh::LeanObject,
    mut v___y_1583_: *mut crate::leanh::LeanObject,
    mut v___y_1584_: *mut crate::leanh::LeanObject,
    mut v___y_1585_: *mut crate::leanh::LeanObject,
    mut v___y_1586_: *mut crate::leanh::LeanObject,
    mut v___y_1587_: *mut crate::leanh::LeanObject,
    mut v___y_1588_: *mut crate::leanh::LeanObject,
    mut v___y_1589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1591_ =
        l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___redArg(
            v_x_1580_,
            v_mkInfoTree_1581_,
            v___y_1582_,
            v___y_1583_,
            v___y_1584_,
            v___y_1585_,
            v___y_1586_,
            v___y_1587_,
            v___y_1588_,
            v___y_1589_,
        );
    return v___x_1591_;
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___boxed(
    mut v_00_u03b1_1592_: *mut crate::leanh::LeanObject,
    mut v_x_1593_: *mut crate::leanh::LeanObject,
    mut v_mkInfoTree_1594_: *mut crate::leanh::LeanObject,
    mut v___y_1595_: *mut crate::leanh::LeanObject,
    mut v___y_1596_: *mut crate::leanh::LeanObject,
    mut v___y_1597_: *mut crate::leanh::LeanObject,
    mut v___y_1598_: *mut crate::leanh::LeanObject,
    mut v___y_1599_: *mut crate::leanh::LeanObject,
    mut v___y_1600_: *mut crate::leanh::LeanObject,
    mut v___y_1601_: *mut crate::leanh::LeanObject,
    mut v___y_1602_: *mut crate::leanh::LeanObject,
    mut v___y_1603_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1604_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3(
        v_00_u03b1_1592_,
        v_x_1593_,
        v_mkInfoTree_1594_,
        v___y_1595_,
        v___y_1596_,
        v___y_1597_,
        v___y_1598_,
        v___y_1599_,
        v___y_1600_,
        v___y_1601_,
        v___y_1602_,
    );
    crate::leanh::lean_dec(v___y_1602_);
    crate::leanh::lean_dec_ref(v___y_1601_);
    crate::leanh::lean_dec(v___y_1600_);
    crate::leanh::lean_dec_ref(v___y_1599_);
    crate::leanh::lean_dec(v___y_1598_);
    crate::leanh::lean_dec_ref(v___y_1597_);
    crate::leanh::lean_dec(v___y_1596_);
    crate::leanh::lean_dec_ref(v___y_1595_);
    return v_res_1604_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1614_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_1615_ = l_Lean_Elab_Tactic_evalCalc___closed__2;
    v___x_1616_ = l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__3;
    v___x_1617_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_evalCalc___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_1618_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1614_,
        v___x_1615_,
        v___x_1616_,
        v___x_1617_,
    );
    return v___x_1618_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___boxed(
    mut v_a_1619_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1620_ = l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1();
    return v_res_1620_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_docString__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1623_ = l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__3;
    v___x_1624_ = l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_docString__3___closed__0;
    v___x_1625_ = l_Lean_addBuiltinDocString(v___x_1623_, v___x_1624_);
    return v___x_1625_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_docString__3___boxed(
    mut v_a_1626_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1627_ = l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_docString__3();
    return v_res_1627_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1654_ = l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__3;
    v___x_1655_ = l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__6;
    v___x_1656_ = l_Lean_addBuiltinDeclarationRanges(v___x_1654_, v___x_1655_);
    return v___x_1656_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___boxed(
    mut v_a_1657_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1658_ = l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5();
    return v_res_1658_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Calc(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Calc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_ElabTerm(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_docString__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Calc(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Calc(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Calc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_ElabTerm(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Calc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Calc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Calc(builtin);
}
