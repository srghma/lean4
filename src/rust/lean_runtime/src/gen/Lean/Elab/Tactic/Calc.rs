// Lean compiler output
// Module: Lean.Elab.Tactic.Calc
// Imports: Lean.Elab.Calc Lean.Elab.Tactic.ElabTerm
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr4,
    l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind, l_Lean_replaceRef,
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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_7,
    lean_apply_9, lean_apply_10, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8, lean_ctor_set_usize, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unsigned_to_nat,
};
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_panic___at___00Lean_Elab_Tactic_evalCalc_spec__2___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_panic___at___00Lean_Elab_Tactic_evalCalc_spec__2___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_evalCalc___lam__2___closed__0_value: LeanStringObject<5> =
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
        m_data: [115, 116, 101, 112, 0],
    };
static mut l_Lean_Elab_Tactic_evalCalc___lam__2___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalCalc___lam__2___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalCalc___lam__2___closed__1_value: LeanStringObject<22> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 22,
        m_capacity: 22,
        m_length: 21,
        m_data: [
            76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 84, 97, 99, 116, 105, 99, 46, 67, 97, 108,
            99, 0,
        ],
    };
static mut l_Lean_Elab_Tactic_evalCalc___lam__2___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalCalc___lam__2___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalCalc___lam__2___closed__2_value: LeanStringObject<26> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 84, 97, 99, 116, 105, 99, 46, 101, 118, 97,
            108, 67, 97, 108, 99, 0,
        ],
    };
static mut l_Lean_Elab_Tactic_evalCalc___lam__2___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalCalc___lam__2___closed__2_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalCalc___lam__2___closed__3_value: LeanStringObject<34> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 34,
        m_capacity: 34,
        m_length: 33,
        m_data: [
            117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97,
            115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0,
        ],
    };
static mut l_Lean_Elab_Tactic_evalCalc___lam__2___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalCalc___lam__2___closed__3_value) as *mut LeanObject;
static mut l_Lean_Elab_Tactic_evalCalc___lam__2___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_evalCalc___lam__2___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_evalCalc___closed__0_value: LeanStringObject<5> = LeanStringObject {
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
static mut l_Lean_Elab_Tactic_evalCalc___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalCalc___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalCalc___closed__1_value: LeanStringObject<11> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_evalCalc___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalCalc___closed__1_value) as *mut LeanObject;
static l_Lean_Elab_Tactic_evalCalc___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_evalCalc___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_evalCalc___closed__2_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_evalCalc___closed__2_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_evalCalc___closed__1_value) as *mut LeanObject,
        9158504355193797775 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_evalCalc___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalCalc___closed__2_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalCalc___closed__3_value: LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_evalCalc___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalCalc___closed__3_value) as *mut LeanObject;
static l_Lean_Elab_Tactic_evalCalc___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_evalCalc___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_evalCalc___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_evalCalc___closed__4_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_evalCalc___closed__3_value) as *mut LeanObject,
        11669652153185471091 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_evalCalc___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalCalc___closed__4_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalCalc___closed__5_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_evalCalc___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalCalc___closed__5_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalCalc___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_evalCalc___closed__5_value) as *mut LeanObject,
        6813867156380545898 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_evalCalc___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalCalc___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__2_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [101, 118, 97, 108, 67, 97, 108, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__2_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalCalc___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__0_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__1_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__2_value) as *mut LeanObject,14073051769863737386 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_docString__3___closed__0_value: LeanStringObject<48> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 48, m_capacity: 48, m_length: 47, m_data: [69, 108, 97, 98, 111, 114, 97, 116, 111, 114, 32, 102, 111, 114, 32, 116, 104, 101, 32, 96, 99, 97, 108, 99, 96, 32, 116, 97, 99, 116, 105, 99, 32, 109, 111, 100, 101, 32, 118, 97, 114, 105, 97, 110, 116, 46, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_docString__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_docString__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 15 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 34 as usize) << 1) | 1) as *mut LeanObject,((( 25 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__0_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__1_value) as *mut LeanObject,((( 25 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 15 as usize) << 1) | 1) as *mut LeanObject,((( 4 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 15 as usize) << 1) | 1) as *mut LeanObject,((( 12 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__3_value) as *mut LeanObject,((( 4 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__4_value) as *mut LeanObject,((( 12 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__6_value) as *mut LeanObject;
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_832_: *mut LeanObject = core::ptr::null_mut();
    v___x_830_ = lean_box(0);
    v___x_831_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_832_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_832_, 0, v___x_831_);
    lean_ctor_set(v___x_832_, 1, v___x_830_);
    return v___x_832_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0___redArg()
-> *mut LeanObject {
    let mut v___x_834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_835_: *mut LeanObject = core::ptr::null_mut();
    v___x_834_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0___redArg___closed__0);
    v___x_835_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_835_, 0, v___x_834_);
    return v___x_835_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0___redArg___boxed(
    mut v___y_836_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_837_: *mut LeanObject = core::ptr::null_mut();
    v_res_837_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0___redArg();
    return v_res_837_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0(
    mut v_00_u03b1_838_: *mut LeanObject,
    mut v___y_839_: *mut LeanObject,
    mut v___y_840_: *mut LeanObject,
    mut v___y_841_: *mut LeanObject,
    mut v___y_842_: *mut LeanObject,
    mut v___y_843_: *mut LeanObject,
    mut v___y_844_: *mut LeanObject,
    mut v___y_845_: *mut LeanObject,
    mut v___y_846_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_848_: *mut LeanObject = core::ptr::null_mut();
    v___x_848_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0___redArg();
    return v___x_848_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0___boxed(
    mut v_00_u03b1_849_: *mut LeanObject,
    mut v___y_850_: *mut LeanObject,
    mut v___y_851_: *mut LeanObject,
    mut v___y_852_: *mut LeanObject,
    mut v___y_853_: *mut LeanObject,
    mut v___y_854_: *mut LeanObject,
    mut v___y_855_: *mut LeanObject,
    mut v___y_856_: *mut LeanObject,
    mut v___y_857_: *mut LeanObject,
    mut v___y_858_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_859_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_857_);
    lean_dec_ref(v___y_856_);
    lean_dec(v___y_855_);
    lean_dec_ref(v___y_854_);
    lean_dec(v___y_853_);
    lean_dec_ref(v___y_852_);
    lean_dec(v___y_851_);
    lean_dec_ref(v___y_850_);
    return v_res_859_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalCalc_spec__1___redArg(
    mut v_e_860_: *mut LeanObject,
    mut v___y_861_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_863_: u8 = 0;
    let mut v___x_864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_877_: u8 = 0;
    let mut v___x_879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_883_: u8 = 0;
    let mut v_unused_884_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_863_ = l_Lean_Expr_hasMVar(v_e_860_);
                if v___x_863_ == 0 {
                    v___x_864_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_864_, 0, v_e_860_);
                    return v___x_864_;
                } else {
                    v___x_865_ = lean_st_ref_get(v___y_861_);
                    v_mctx_866_ = lean_ctor_get(v___x_865_, 0);
                    lean_inc_ref(v_mctx_866_);
                    lean_dec(v___x_865_);
                    v___x_867_ = l_Lean_instantiateMVarsCore(v_mctx_866_, v_e_860_);
                    v_fst_868_ = lean_ctor_get(v___x_867_, 0);
                    lean_inc(v_fst_868_);
                    v_snd_869_ = lean_ctor_get(v___x_867_, 1);
                    lean_inc(v_snd_869_);
                    lean_dec_ref(v___x_867_);
                    v___x_870_ = lean_st_ref_take(v___y_861_);
                    v_cache_871_ = lean_ctor_get(v___x_870_, 1);
                    v_zetaDeltaFVarIds_872_ = lean_ctor_get(v___x_870_, 2);
                    v_postponed_873_ = lean_ctor_get(v___x_870_, 3);
                    v_diag_874_ = lean_ctor_get(v___x_870_, 4);
                    v_isSharedCheck_883_ = (!lean_is_exclusive(v___x_870_)) as u8;
                    if v_isSharedCheck_883_ == 0 {
                        v_unused_884_ = lean_ctor_get(v___x_870_, 0);
                        lean_dec(v_unused_884_);
                        v___x_876_ = v___x_870_;
                        v_isShared_877_ = v_isSharedCheck_883_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_874_);
                        lean_inc(v_postponed_873_);
                        lean_inc(v_zetaDeltaFVarIds_872_);
                        lean_inc(v_cache_871_);
                        lean_dec(v___x_870_);
                        v___x_876_ = lean_box(0);
                        v_isShared_877_ = v_isSharedCheck_883_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_877_ == 0 {
                    lean_ctor_set(v___x_876_, 0, v_snd_869_);
                    v___x_879_ = v___x_876_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_882_, 0, v_snd_869_);
                    lean_ctor_set(v_reuseFailAlloc_882_, 1, v_cache_871_);
                    lean_ctor_set(v_reuseFailAlloc_882_, 2, v_zetaDeltaFVarIds_872_);
                    lean_ctor_set(v_reuseFailAlloc_882_, 3, v_postponed_873_);
                    lean_ctor_set(v_reuseFailAlloc_882_, 4, v_diag_874_);
                    v___x_879_ = v_reuseFailAlloc_882_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_880_ = lean_st_ref_set(v___y_861_, v___x_879_);
                v___x_881_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_881_, 0, v_fst_868_);
                return v___x_881_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalCalc_spec__1___redArg___boxed(
    mut v_e_885_: *mut LeanObject,
    mut v___y_886_: *mut LeanObject,
    mut v___y_887_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_888_: *mut LeanObject = core::ptr::null_mut();
    v_res_888_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalCalc_spec__1___redArg(
        v_e_885_, v___y_886_,
    );
    lean_dec(v___y_886_);
    return v_res_888_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalCalc_spec__1(
    mut v_e_889_: *mut LeanObject,
    mut v___y_890_: *mut LeanObject,
    mut v___y_891_: *mut LeanObject,
    mut v___y_892_: *mut LeanObject,
    mut v___y_893_: *mut LeanObject,
    mut v___y_894_: *mut LeanObject,
    mut v___y_895_: *mut LeanObject,
    mut v___y_896_: *mut LeanObject,
    mut v___y_897_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_899_: *mut LeanObject = core::ptr::null_mut();
    v___x_899_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalCalc_spec__1___redArg(
        v_e_889_, v___y_895_,
    );
    return v___x_899_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalCalc_spec__1___boxed(
    mut v_e_900_: *mut LeanObject,
    mut v___y_901_: *mut LeanObject,
    mut v___y_902_: *mut LeanObject,
    mut v___y_903_: *mut LeanObject,
    mut v___y_904_: *mut LeanObject,
    mut v___y_905_: *mut LeanObject,
    mut v___y_906_: *mut LeanObject,
    mut v___y_907_: *mut LeanObject,
    mut v___y_908_: *mut LeanObject,
    mut v___y_909_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_910_: *mut LeanObject = core::ptr::null_mut();
    v_res_910_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalCalc_spec__1(
        v_e_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_,
        v___y_907_, v___y_908_,
    );
    lean_dec(v___y_908_);
    lean_dec_ref(v___y_907_);
    lean_dec(v___y_906_);
    lean_dec_ref(v___y_905_);
    lean_dec(v___y_904_);
    lean_dec_ref(v___y_903_);
    lean_dec(v___y_902_);
    lean_dec_ref(v___y_901_);
    return v_res_910_;
}
pub unsafe fn _init_l_panic___at___00Lean_Elab_Tactic_evalCalc_spec__2___closed__0()
-> *mut LeanObject {
    let mut v___x_911_: *mut LeanObject = core::ptr::null_mut();
    v___x_911_ = l_Lean_Elab_Term_instInhabitedTermElabM(lean_box(0));
    return v___x_911_;
}
pub unsafe fn l_panic___at___00Lean_Elab_Tactic_evalCalc_spec__2(
    mut v_msg_912_: *mut LeanObject,
    mut v___y_913_: *mut LeanObject,
    mut v___y_914_: *mut LeanObject,
    mut v___y_915_: *mut LeanObject,
    mut v___y_916_: *mut LeanObject,
    mut v___y_917_: *mut LeanObject,
    mut v___y_918_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_11008__overap_921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_922_: *mut LeanObject = core::ptr::null_mut();
    v___x_920_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_panic___at___00Lean_Elab_Tactic_evalCalc_spec__2___closed__0),
        core::ptr::addr_of_mut!(
            l_panic___at___00Lean_Elab_Tactic_evalCalc_spec__2___closed__0_once
        ),
        _init_l_panic___at___00Lean_Elab_Tactic_evalCalc_spec__2___closed__0,
    );
    v___x_11008__overap_921_ = lean_panic_fn_borrowed(v___x_920_, v_msg_912_);
    lean_inc(v___y_918_);
    lean_inc_ref(v___y_917_);
    lean_inc(v___y_916_);
    lean_inc_ref(v___y_915_);
    lean_inc(v___y_914_);
    lean_inc_ref(v___y_913_);
    v___x_922_ = lean_apply_7(
        v___x_11008__overap_921_,
        v___y_913_,
        v___y_914_,
        v___y_915_,
        v___y_916_,
        v___y_917_,
        v___y_918_,
        lean_box(0),
    );
    return v___x_922_;
}
pub unsafe fn l_panic___at___00Lean_Elab_Tactic_evalCalc_spec__2___boxed(
    mut v_msg_923_: *mut LeanObject,
    mut v___y_924_: *mut LeanObject,
    mut v___y_925_: *mut LeanObject,
    mut v___y_926_: *mut LeanObject,
    mut v___y_927_: *mut LeanObject,
    mut v___y_928_: *mut LeanObject,
    mut v___y_929_: *mut LeanObject,
    mut v___y_930_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_931_: *mut LeanObject = core::ptr::null_mut();
    v_res_931_ = l_panic___at___00Lean_Elab_Tactic_evalCalc_spec__2(
        v_msg_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_,
    );
    lean_dec(v___y_929_);
    lean_dec_ref(v___y_928_);
    lean_dec(v___y_927_);
    lean_dec_ref(v___y_926_);
    lean_dec(v___y_925_);
    lean_dec_ref(v___y_924_);
    return v_res_931_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalCalc___lam__0(
    mut v_a_932_: *mut LeanObject,
    mut v_x_933_: *mut LeanObject,
    mut v___y_934_: *mut LeanObject,
    mut v___y_935_: *mut LeanObject,
    mut v___y_936_: *mut LeanObject,
    mut v___y_937_: *mut LeanObject,
    mut v___y_938_: *mut LeanObject,
    mut v___y_939_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_941_: *mut LeanObject = core::ptr::null_mut();
    v___x_941_ = l_Lean_Elab_Term_throwCalcFailure___redArg(
        v_a_932_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_,
    );
    return v___x_941_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalCalc___lam__0___boxed(
    mut v_a_942_: *mut LeanObject,
    mut v_x_943_: *mut LeanObject,
    mut v___y_944_: *mut LeanObject,
    mut v___y_945_: *mut LeanObject,
    mut v___y_946_: *mut LeanObject,
    mut v___y_947_: *mut LeanObject,
    mut v___y_948_: *mut LeanObject,
    mut v___y_949_: *mut LeanObject,
    mut v___y_950_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_951_: *mut LeanObject = core::ptr::null_mut();
    v_res_951_ = l_Lean_Elab_Tactic_evalCalc___lam__0(
        v_a_942_, v_x_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_,
    );
    lean_dec(v___y_949_);
    lean_dec_ref(v___y_948_);
    lean_dec(v___y_947_);
    lean_dec_ref(v___y_946_);
    lean_dec(v_x_943_);
    lean_dec_ref(v_a_942_);
    return v_res_951_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalCalc___lam__1(
    mut v_a_952_: *mut LeanObject,
    mut v_x_953_: *mut LeanObject,
    mut v___y_954_: *mut LeanObject,
    mut v___y_955_: *mut LeanObject,
    mut v___y_956_: *mut LeanObject,
    mut v___y_957_: *mut LeanObject,
    mut v___y_958_: *mut LeanObject,
    mut v___y_959_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_961_: *mut LeanObject = core::ptr::null_mut();
    v___x_961_ = l_Lean_Elab_Term_throwCalcFailure___redArg(
        v_a_952_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_,
    );
    return v___x_961_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalCalc___lam__1___boxed(
    mut v_a_962_: *mut LeanObject,
    mut v_x_963_: *mut LeanObject,
    mut v___y_964_: *mut LeanObject,
    mut v___y_965_: *mut LeanObject,
    mut v___y_966_: *mut LeanObject,
    mut v___y_967_: *mut LeanObject,
    mut v___y_968_: *mut LeanObject,
    mut v___y_969_: *mut LeanObject,
    mut v___y_970_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_971_: *mut LeanObject = core::ptr::null_mut();
    v_res_971_ = l_Lean_Elab_Tactic_evalCalc___lam__1(
        v_a_962_, v_x_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_,
    );
    lean_dec(v___y_969_);
    lean_dec_ref(v___y_968_);
    lean_dec(v___y_967_);
    lean_dec_ref(v___y_966_);
    lean_dec(v_x_963_);
    lean_dec_ref(v_a_962_);
    return v_res_971_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_evalCalc___lam__2___closed__4() -> *mut LeanObject {
    let mut v___x_976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut LeanObject = core::ptr::null_mut();
    v___x_976_ = l_Lean_Elab_Tactic_evalCalc___lam__2___closed__3;
    v___x_977_ = lean_unsigned_to_nat(65);
    v___x_978_ = lean_unsigned_to_nat(32);
    v___x_979_ = l_Lean_Elab_Tactic_evalCalc___lam__2___closed__2;
    v___x_980_ = l_Lean_Elab_Tactic_evalCalc___lam__2___closed__1;
    v___x_981_ =
        l_mkPanicMessageWithDecl(v___x_980_, v___x_979_, v___x_978_, v___x_977_, v___x_976_);
    return v___x_981_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalCalc___lam__2(
    mut v_a_982_: *mut LeanObject,
    mut v___x_983_: *mut LeanObject,
    mut v___f_984_: *mut LeanObject,
    mut v___f_985_: *mut LeanObject,
    mut v___x_986_: *mut LeanObject,
    mut v_tag_987_: *mut LeanObject,
    mut v___y_988_: *mut LeanObject,
    mut v___y_989_: *mut LeanObject,
    mut v___y_990_: *mut LeanObject,
    mut v___y_991_: *mut LeanObject,
    mut v___y_992_: *mut LeanObject,
    mut v___y_993_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_999_: u8 = 0;
    let mut v_fst_1000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1013_: u8 = 0;
    let mut v___x_1015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: u8 = 0;
    let mut v___x_1020_: u8 = 0;
    let mut v___x_1021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1025_: u8 = 0;
    let mut v___x_1026_: u8 = 0;
    let mut v___x_1027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: u8 = 0;
    let mut v___x_1044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1058_: u8 = 0;
    let mut v___x_1059_: u8 = 0;
    let mut v___x_1061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1063_: u8 = 0;
    let mut v_a_1064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1069_: u8 = 0;
    let mut v___x_1071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1073_: u8 = 0;
    let mut v___x_1074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: u8 = 0;
    let mut v___x_1081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1085_: u8 = 0;
    let mut v___x_1087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1089_: u8 = 0;
    let mut v___x_1090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1095_: u8 = 0;
    let mut v___x_1097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1099_: u8 = 0;
    let mut v___x_1101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1103_: u8 = 0;
    let mut v_a_1104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1107_: u8 = 0;
    let mut v___x_1109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1111_: u8 = 0;
    let mut v_isSharedCheck_1112_: u8 = 0;
    let mut v_a_1113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1116_: u8 = 0;
    let mut v___x_1118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1120_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_995_ = l_Lean_Elab_Term_elabCalcSteps(
                    v_a_982_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_,
                    v___y_993_,
                );
                if lean_obj_tag(v___x_995_) == 0 {
                    v_a_996_ = lean_ctor_get(v___x_995_, 0);
                    v_isSharedCheck_1112_ = (!lean_is_exclusive(v___x_995_)) as u8;
                    if v_isSharedCheck_1112_ == 0 {
                        v___x_998_ = v___x_995_;
                        v_isShared_999_ = v_isSharedCheck_1112_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_996_);
                        lean_dec(v___x_995_);
                        v___x_998_ = lean_box(0);
                        v_isShared_999_ = v_isSharedCheck_1112_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___y_993_);
                    lean_dec_ref(v___y_992_);
                    lean_dec(v___y_991_);
                    lean_dec_ref(v___y_990_);
                    lean_dec(v_tag_987_);
                    lean_dec_ref(v___x_986_);
                    lean_dec_ref(v___f_985_);
                    lean_dec_ref(v___f_984_);
                    lean_dec_ref(v___x_983_);
                    v_a_1113_ = lean_ctor_get(v___x_995_, 0);
                    v_isSharedCheck_1120_ = (!lean_is_exclusive(v___x_995_)) as u8;
                    if v_isSharedCheck_1120_ == 0 {
                        v___x_1115_ = v___x_995_;
                        v_isShared_1116_ = v_isSharedCheck_1120_;
                        state = 19;
                        continue;
                    } else {
                        lean_inc(v_a_1113_);
                        lean_dec(v___x_995_);
                        v___x_1115_ = lean_box(0);
                        v_isShared_1116_ = v_isSharedCheck_1120_;
                        state = 19;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1000_ = lean_ctor_get(v_a_996_, 0);
                lean_inc(v_fst_1000_);
                v_snd_1001_ = lean_ctor_get(v_a_996_, 1);
                lean_inc_n(v_snd_1001_, 2);
                lean_dec(v_a_996_);
                lean_inc_ref(v___x_983_);
                v___x_1021_ = l_Lean_Meta_isExprDefEq(
                    v_snd_1001_,
                    v___x_983_,
                    v___y_990_,
                    v___y_991_,
                    v___y_992_,
                    v___y_993_,
                );
                if lean_obj_tag(v___x_1021_) == 0 {
                    v_a_1022_ = lean_ctor_get(v___x_1021_, 0);
                    v_isSharedCheck_1103_ = (!lean_is_exclusive(v___x_1021_)) as u8;
                    if v_isSharedCheck_1103_ == 0 {
                        v___x_1024_ = v___x_1021_;
                        v_isShared_1025_ = v_isSharedCheck_1103_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_1022_);
                        lean_dec(v___x_1021_);
                        v___x_1024_ = lean_box(0);
                        v_isShared_1025_ = v_isSharedCheck_1103_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_dec(v_snd_1001_);
                    lean_dec(v_fst_1000_);
                    lean_del_object(v___x_998_);
                    lean_dec(v___y_993_);
                    lean_dec_ref(v___y_992_);
                    lean_dec(v___y_991_);
                    lean_dec_ref(v___y_990_);
                    lean_dec(v_tag_987_);
                    lean_dec_ref(v___x_986_);
                    lean_dec_ref(v___f_985_);
                    lean_dec_ref(v___f_984_);
                    lean_dec_ref(v___x_983_);
                    v_a_1104_ = lean_ctor_get(v___x_1021_, 0);
                    v_isSharedCheck_1111_ = (!lean_is_exclusive(v___x_1021_)) as u8;
                    if v_isSharedCheck_1111_ == 0 {
                        v___x_1106_ = v___x_1021_;
                        v_isShared_1107_ = v_isSharedCheck_1111_;
                        state = 17;
                        continue;
                    } else {
                        lean_inc(v_a_1104_);
                        lean_dec(v___x_1021_);
                        v___x_1106_ = lean_box(0);
                        v_isShared_1107_ = v_isSharedCheck_1111_;
                        state = 17;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1009_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1009_, 0, v___x_983_);
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
                lean_dec(v___y_1008_);
                lean_dec_ref(v___y_1007_);
                lean_dec(v___y_1006_);
                lean_dec_ref(v___y_1005_);
                return v___x_1010_;
            }
            3 => {
                if v___y_1013_ == 0 {
                    lean_dec_ref(v___y_1012_);
                    lean_del_object(v___x_998_);
                    v___y_1003_ = v___y_988_;
                    v___y_1004_ = v___y_989_;
                    v___y_1005_ = v___y_990_;
                    v___y_1006_ = v___y_991_;
                    v___y_1007_ = v___y_992_;
                    v___y_1008_ = v___y_993_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_fst_1000_);
                    lean_dec(v___y_993_);
                    lean_dec_ref(v___y_992_);
                    lean_dec(v___y_991_);
                    lean_dec_ref(v___y_990_);
                    lean_dec_ref(v___f_985_);
                    lean_dec_ref(v___f_984_);
                    lean_dec_ref(v___x_983_);
                    if v_isShared_999_ == 0 {
                        lean_ctor_set_tag(v___x_998_, 1);
                        lean_ctor_set(v___x_998_, 0, v___y_1012_);
                        v___x_1015_ = v___x_998_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1016_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1016_, 0, v___y_1012_);
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
                    lean_inc_ref(v_a_1018_);
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
                v___x_1026_ = (lean_unbox(v_a_1022_) as u8);
                lean_dec(v_a_1022_);
                if v___x_1026_ == 0 {
                    lean_del_object(v___x_1024_);
                    v___x_1027_ = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(v_snd_1001_);
                    if lean_obj_tag(v___x_1027_) == 0 {
                        v_a_1028_ = lean_ctor_get(v___x_1027_, 0);
                        lean_inc(v_a_1028_);
                        lean_dec_ref_known(v___x_1027_, 1);
                        if lean_obj_tag(v_a_1028_) == 1 {
                            v_val_1029_ = lean_ctor_get(v_a_1028_, 0);
                            lean_inc(v_val_1029_);
                            lean_dec_ref_known(v_a_1028_, 1);
                            v_snd_1030_ = lean_ctor_get(v_val_1029_, 1);
                            lean_inc(v_snd_1030_);
                            lean_dec(v_val_1029_);
                            v_fst_1031_ = lean_ctor_get(v_snd_1030_, 0);
                            lean_inc(v_fst_1031_);
                            v_snd_1032_ = lean_ctor_get(v_snd_1030_, 1);
                            lean_inc(v_snd_1032_);
                            lean_dec(v_snd_1030_);
                            v___x_1033_ = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(v___x_983_);
                            if lean_obj_tag(v___x_1033_) == 0 {
                                v_a_1034_ = lean_ctor_get(v___x_1033_, 0);
                                lean_inc(v_a_1034_);
                                lean_dec_ref_known(v___x_1033_, 1);
                                if lean_obj_tag(v_a_1034_) == 1 {
                                    v_val_1035_ = lean_ctor_get(v_a_1034_, 0);
                                    lean_inc(v_val_1035_);
                                    lean_dec_ref_known(v_a_1034_, 1);
                                    v_snd_1036_ = lean_ctor_get(v_val_1035_, 1);
                                    lean_inc(v_snd_1036_);
                                    v_fst_1037_ = lean_ctor_get(v_val_1035_, 0);
                                    lean_inc(v_fst_1037_);
                                    lean_dec(v_val_1035_);
                                    v_fst_1038_ = lean_ctor_get(v_snd_1036_, 0);
                                    lean_inc(v_fst_1038_);
                                    v_snd_1039_ = lean_ctor_get(v_snd_1036_, 1);
                                    lean_inc(v_snd_1039_);
                                    lean_dec(v_snd_1036_);
                                    lean_inc(v___y_993_);
                                    lean_inc_ref(v___y_992_);
                                    lean_inc(v___y_991_);
                                    lean_inc_ref(v___y_990_);
                                    lean_inc(v_snd_1032_);
                                    v___x_1074_ = lean_infer_type(
                                        v_snd_1032_,
                                        v___y_990_,
                                        v___y_991_,
                                        v___y_992_,
                                        v___y_993_,
                                    );
                                    if lean_obj_tag(v___x_1074_) == 0 {
                                        v_a_1075_ = lean_ctor_get(v___x_1074_, 0);
                                        lean_inc(v_a_1075_);
                                        lean_dec_ref_known(v___x_1074_, 1);
                                        lean_inc(v___y_993_);
                                        lean_inc_ref(v___y_992_);
                                        lean_inc(v___y_991_);
                                        lean_inc_ref(v___y_990_);
                                        lean_inc(v_fst_1038_);
                                        v___x_1076_ = lean_infer_type(
                                            v_fst_1038_,
                                            v___y_990_,
                                            v___y_991_,
                                            v___y_992_,
                                            v___y_993_,
                                        );
                                        if lean_obj_tag(v___x_1076_) == 0 {
                                            v_a_1077_ = lean_ctor_get(v___x_1076_, 0);
                                            lean_inc(v_a_1077_);
                                            lean_dec_ref_known(v___x_1076_, 1);
                                            v___x_1078_ = l_Lean_Meta_isExprDefEq(
                                                v_fst_1031_,
                                                v_fst_1038_,
                                                v___y_990_,
                                                v___y_991_,
                                                v___y_992_,
                                                v___y_993_,
                                            );
                                            if lean_obj_tag(v___x_1078_) == 0 {
                                                v_a_1079_ = lean_ctor_get(v___x_1078_, 0);
                                                lean_inc(v_a_1079_);
                                                v___x_1080_ = (lean_unbox(v_a_1079_) as u8);
                                                lean_dec(v_a_1079_);
                                                if v___x_1080_ == 0 {
                                                    lean_dec(v_a_1077_);
                                                    lean_dec(v_a_1075_);
                                                    v___y_1041_ = v___x_1078_;
                                                    state = 7;
                                                    continue;
                                                } else {
                                                    lean_dec_ref_known(v___x_1078_, 1);
                                                    v___x_1081_ = l_Lean_Meta_isExprDefEq(
                                                        v_a_1075_, v_a_1077_, v___y_990_,
                                                        v___y_991_, v___y_992_, v___y_993_,
                                                    );
                                                    v___y_1041_ = v___x_1081_;
                                                    state = 7;
                                                    continue;
                                                }
                                            } else {
                                                lean_dec(v_a_1077_);
                                                lean_dec(v_a_1075_);
                                                v___y_1041_ = v___x_1078_;
                                                state = 7;
                                                continue;
                                            }
                                        } else {
                                            lean_dec(v_a_1075_);
                                            lean_dec(v_snd_1039_);
                                            lean_dec(v_fst_1038_);
                                            lean_dec(v_fst_1037_);
                                            lean_dec(v_snd_1032_);
                                            lean_dec(v_fst_1031_);
                                            lean_dec(v_snd_1001_);
                                            lean_dec(v_fst_1000_);
                                            lean_del_object(v___x_998_);
                                            lean_dec(v___y_993_);
                                            lean_dec_ref(v___y_992_);
                                            lean_dec(v___y_991_);
                                            lean_dec_ref(v___y_990_);
                                            lean_dec(v_tag_987_);
                                            lean_dec_ref(v___x_986_);
                                            lean_dec_ref(v___f_985_);
                                            lean_dec_ref(v___f_984_);
                                            lean_dec_ref(v___x_983_);
                                            return v___x_1076_;
                                        }
                                    } else {
                                        lean_dec(v_snd_1039_);
                                        lean_dec(v_fst_1038_);
                                        lean_dec(v_fst_1037_);
                                        lean_dec(v_snd_1032_);
                                        lean_dec(v_fst_1031_);
                                        lean_dec(v_snd_1001_);
                                        lean_dec(v_fst_1000_);
                                        lean_del_object(v___x_998_);
                                        lean_dec(v___y_993_);
                                        lean_dec_ref(v___y_992_);
                                        lean_dec(v___y_991_);
                                        lean_dec_ref(v___y_990_);
                                        lean_dec(v_tag_987_);
                                        lean_dec_ref(v___x_986_);
                                        lean_dec_ref(v___f_985_);
                                        lean_dec_ref(v___f_984_);
                                        lean_dec_ref(v___x_983_);
                                        return v___x_1074_;
                                    }
                                } else {
                                    lean_dec(v_a_1034_);
                                    lean_dec(v_snd_1032_);
                                    lean_dec(v_fst_1031_);
                                    lean_dec(v_snd_1001_);
                                    lean_del_object(v___x_998_);
                                    lean_dec(v_tag_987_);
                                    lean_dec_ref(v___x_986_);
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
                                lean_dec(v_snd_1032_);
                                lean_dec(v_fst_1031_);
                                lean_dec(v_snd_1001_);
                                lean_dec(v_fst_1000_);
                                lean_del_object(v___x_998_);
                                lean_dec(v___y_993_);
                                lean_dec_ref(v___y_992_);
                                lean_dec(v___y_991_);
                                lean_dec_ref(v___y_990_);
                                lean_dec(v_tag_987_);
                                lean_dec_ref(v___x_986_);
                                lean_dec_ref(v___f_985_);
                                lean_dec_ref(v___f_984_);
                                lean_dec_ref(v___x_983_);
                                v_a_1082_ = lean_ctor_get(v___x_1033_, 0);
                                v_isSharedCheck_1089_ = (!lean_is_exclusive(v___x_1033_)) as u8;
                                if v_isSharedCheck_1089_ == 0 {
                                    v___x_1084_ = v___x_1033_;
                                    v_isShared_1085_ = v_isSharedCheck_1089_;
                                    state = 12;
                                    continue;
                                } else {
                                    lean_inc(v_a_1082_);
                                    lean_dec(v___x_1033_);
                                    v___x_1084_ = lean_box(0);
                                    v_isShared_1085_ = v_isSharedCheck_1089_;
                                    state = 12;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_1028_);
                            lean_dec(v_snd_1001_);
                            lean_dec(v_fst_1000_);
                            lean_del_object(v___x_998_);
                            lean_dec(v_tag_987_);
                            lean_dec_ref(v___x_986_);
                            lean_dec_ref(v___f_985_);
                            lean_dec_ref(v___f_984_);
                            lean_dec_ref(v___x_983_);
                            v___x_1090_ = lean_obj_once(
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
                            lean_dec(v___y_993_);
                            lean_dec_ref(v___y_992_);
                            lean_dec(v___y_991_);
                            lean_dec_ref(v___y_990_);
                            return v___x_1091_;
                        }
                    } else {
                        lean_dec(v_snd_1001_);
                        lean_dec(v_fst_1000_);
                        lean_del_object(v___x_998_);
                        lean_dec(v___y_993_);
                        lean_dec_ref(v___y_992_);
                        lean_dec(v___y_991_);
                        lean_dec_ref(v___y_990_);
                        lean_dec(v_tag_987_);
                        lean_dec_ref(v___x_986_);
                        lean_dec_ref(v___f_985_);
                        lean_dec_ref(v___f_984_);
                        lean_dec_ref(v___x_983_);
                        v_a_1092_ = lean_ctor_get(v___x_1027_, 0);
                        v_isSharedCheck_1099_ = (!lean_is_exclusive(v___x_1027_)) as u8;
                        if v_isSharedCheck_1099_ == 0 {
                            v___x_1094_ = v___x_1027_;
                            v_isShared_1095_ = v_isSharedCheck_1099_;
                            state = 14;
                            continue;
                        } else {
                            lean_inc(v_a_1092_);
                            lean_dec(v___x_1027_);
                            v___x_1094_ = lean_box(0);
                            v_isShared_1095_ = v_isSharedCheck_1099_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_snd_1001_);
                    lean_del_object(v___x_998_);
                    lean_dec(v___y_993_);
                    lean_dec_ref(v___y_992_);
                    lean_dec(v___y_991_);
                    lean_dec_ref(v___y_990_);
                    lean_dec(v_tag_987_);
                    lean_dec_ref(v___x_986_);
                    lean_dec_ref(v___f_985_);
                    lean_dec_ref(v___f_984_);
                    lean_dec_ref(v___x_983_);
                    if v_isShared_1025_ == 0 {
                        lean_ctor_set(v___x_1024_, 0, v_fst_1000_);
                        v___x_1101_ = v___x_1024_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_1102_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_fst_1000_);
                        v___x_1101_ = v_reuseFailAlloc_1102_;
                        state = 16;
                        continue;
                    }
                }
            }
            7 => {
                if lean_obj_tag(v___y_1041_) == 0 {
                    v_a_1042_ = lean_ctor_get(v___y_1041_, 0);
                    lean_inc(v_a_1042_);
                    lean_dec_ref_known(v___y_1041_, 1);
                    v___x_1043_ = (lean_unbox(v_a_1042_) as u8);
                    lean_dec(v_a_1042_);
                    if v___x_1043_ == 0 {
                        lean_dec(v_snd_1039_);
                        lean_dec(v_fst_1037_);
                        lean_dec(v_snd_1032_);
                        lean_dec(v_snd_1001_);
                        lean_del_object(v___x_998_);
                        lean_dec(v_tag_987_);
                        lean_dec_ref(v___x_986_);
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
                        lean_inc_ref(v___x_1044_);
                        v___x_1048_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                            v___x_1044_,
                            v___x_1047_,
                            v___y_990_,
                            v___y_991_,
                            v___y_992_,
                            v___y_993_,
                        );
                        if lean_obj_tag(v___x_1048_) == 0 {
                            v_a_1049_ = lean_ctor_get(v___x_1048_, 0);
                            lean_inc(v_a_1049_);
                            lean_dec_ref_known(v___x_1048_, 1);
                            lean_inc(v_fst_1000_);
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
                            lean_dec(v_snd_1001_);
                            if lean_obj_tag(v___x_1050_) == 0 {
                                v_a_1051_ = lean_ctor_get(v___x_1050_, 0);
                                lean_inc(v_a_1051_);
                                lean_dec_ref_known(v___x_1050_, 1);
                                v_fst_1052_ = lean_ctor_get(v_a_1051_, 0);
                                lean_inc(v_fst_1052_);
                                v_snd_1053_ = lean_ctor_get(v_a_1051_, 1);
                                lean_inc(v_snd_1053_);
                                lean_dec(v_a_1051_);
                                lean_inc_ref(v___x_983_);
                                v___x_1054_ = l_Lean_Meta_isExprDefEq(
                                    v_snd_1053_,
                                    v___x_983_,
                                    v___y_990_,
                                    v___y_991_,
                                    v___y_992_,
                                    v___y_993_,
                                );
                                if lean_obj_tag(v___x_1054_) == 0 {
                                    lean_del_object(v___x_998_);
                                    v_a_1055_ = lean_ctor_get(v___x_1054_, 0);
                                    v_isSharedCheck_1063_ = (!lean_is_exclusive(v___x_1054_)) as u8;
                                    if v_isSharedCheck_1063_ == 0 {
                                        v___x_1057_ = v___x_1054_;
                                        v_isShared_1058_ = v_isSharedCheck_1063_;
                                        state = 8;
                                        continue;
                                    } else {
                                        lean_inc(v_a_1055_);
                                        lean_dec(v___x_1054_);
                                        v___x_1057_ = lean_box(0);
                                        v_isShared_1058_ = v_isSharedCheck_1063_;
                                        state = 8;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_fst_1052_);
                                    v_a_1064_ = lean_ctor_get(v___x_1054_, 0);
                                    lean_inc(v_a_1064_);
                                    lean_dec_ref_known(v___x_1054_, 1);
                                    v_a_1018_ = v_a_1064_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                v_a_1065_ = lean_ctor_get(v___x_1050_, 0);
                                lean_inc(v_a_1065_);
                                lean_dec_ref_known(v___x_1050_, 1);
                                v_a_1018_ = v_a_1065_;
                                state = 5;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v___x_1044_);
                            lean_dec(v_snd_1001_);
                            lean_dec(v_fst_1000_);
                            lean_del_object(v___x_998_);
                            lean_dec(v___y_993_);
                            lean_dec_ref(v___y_992_);
                            lean_dec(v___y_991_);
                            lean_dec_ref(v___y_990_);
                            lean_dec_ref(v___f_985_);
                            lean_dec_ref(v___f_984_);
                            lean_dec_ref(v___x_983_);
                            return v___x_1048_;
                        }
                    }
                } else {
                    lean_dec(v_snd_1039_);
                    lean_dec(v_fst_1037_);
                    lean_dec(v_snd_1032_);
                    lean_dec(v_snd_1001_);
                    lean_dec(v_fst_1000_);
                    lean_del_object(v___x_998_);
                    lean_dec(v___y_993_);
                    lean_dec_ref(v___y_992_);
                    lean_dec(v___y_991_);
                    lean_dec_ref(v___y_990_);
                    lean_dec(v_tag_987_);
                    lean_dec_ref(v___x_986_);
                    lean_dec_ref(v___f_985_);
                    lean_dec_ref(v___f_984_);
                    lean_dec_ref(v___x_983_);
                    v_a_1066_ = lean_ctor_get(v___y_1041_, 0);
                    v_isSharedCheck_1073_ = (!lean_is_exclusive(v___y_1041_)) as u8;
                    if v_isSharedCheck_1073_ == 0 {
                        v___x_1068_ = v___y_1041_;
                        v_isShared_1069_ = v_isSharedCheck_1073_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_1066_);
                        lean_dec(v___y_1041_);
                        v___x_1068_ = lean_box(0);
                        v_isShared_1069_ = v_isSharedCheck_1073_;
                        state = 10;
                        continue;
                    }
                }
            }
            8 => {
                v___x_1059_ = (lean_unbox(v_a_1055_) as u8);
                lean_dec(v_a_1055_);
                if v___x_1059_ == 0 {
                    lean_del_object(v___x_1057_);
                    lean_dec(v_fst_1052_);
                    v___y_1003_ = v___y_988_;
                    v___y_1004_ = v___y_989_;
                    v___y_1005_ = v___y_990_;
                    v___y_1006_ = v___y_991_;
                    v___y_1007_ = v___y_992_;
                    v___y_1008_ = v___y_993_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_fst_1000_);
                    lean_dec(v___y_993_);
                    lean_dec_ref(v___y_992_);
                    lean_dec(v___y_991_);
                    lean_dec_ref(v___y_990_);
                    lean_dec_ref(v___f_985_);
                    lean_dec_ref(v___f_984_);
                    lean_dec_ref(v___x_983_);
                    if v_isShared_1058_ == 0 {
                        lean_ctor_set(v___x_1057_, 0, v_fst_1052_);
                        v___x_1061_ = v___x_1057_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_fst_1052_);
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
                    v_reuseFailAlloc_1072_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_a_1066_);
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
                    v_reuseFailAlloc_1088_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_a_1082_);
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
                    v_reuseFailAlloc_1098_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_a_1092_);
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
                    v_reuseFailAlloc_1110_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_a_1104_);
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
                    v_reuseFailAlloc_1119_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_a_1113_);
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
    mut v_a_1121_: *mut LeanObject,
    mut v___x_1122_: *mut LeanObject,
    mut v___f_1123_: *mut LeanObject,
    mut v___f_1124_: *mut LeanObject,
    mut v___x_1125_: *mut LeanObject,
    mut v_tag_1126_: *mut LeanObject,
    mut v___y_1127_: *mut LeanObject,
    mut v___y_1128_: *mut LeanObject,
    mut v___y_1129_: *mut LeanObject,
    mut v___y_1130_: *mut LeanObject,
    mut v___y_1131_: *mut LeanObject,
    mut v___y_1132_: *mut LeanObject,
    mut v___y_1133_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1134_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_1128_);
    lean_dec_ref(v___y_1127_);
    lean_dec_ref(v_a_1121_);
    return v_res_1134_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalCalc___lam__3(
    mut v_steps_1135_: *mut LeanObject,
    mut v_target_1136_: *mut LeanObject,
    mut v___x_1137_: *mut LeanObject,
    mut v_tag_1138_: *mut LeanObject,
    mut v___x_1139_: *mut LeanObject,
    mut v___y_1140_: *mut LeanObject,
    mut v___y_1141_: *mut LeanObject,
    mut v___y_1142_: *mut LeanObject,
    mut v___y_1143_: *mut LeanObject,
    mut v___y_1144_: *mut LeanObject,
    mut v___y_1145_: *mut LeanObject,
    mut v___y_1146_: *mut LeanObject,
    mut v___y_1147_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: u8 = 0;
    let mut v___x_1158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1167_: u8 = 0;
    let mut v___x_1169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1171_: u8 = 0;
    let mut v_unused_1172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1176_: u8 = 0;
    let mut v___x_1178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1180_: u8 = 0;
    let mut v_a_1181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1184_: u8 = 0;
    let mut v___x_1186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1188_: u8 = 0;
    let mut v_a_1189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1192_: u8 = 0;
    let mut v___x_1194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1195_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_1149_) == 0 {
                    v_a_1150_ = lean_ctor_get(v___x_1149_, 0);
                    lean_inc_n(v_a_1150_, 3);
                    lean_dec_ref_known(v___x_1149_, 1);
                    v___x_1151_ =
                        l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalCalc_spec__1___redArg(
                            v_target_1136_,
                            v___y_1145_,
                        );
                    v_a_1152_ = lean_ctor_get(v___x_1151_, 0);
                    lean_inc(v_a_1152_);
                    lean_dec_ref(v___x_1151_);
                    v___f_1153_ = lean_alloc_closure(
                        l_Lean_Elab_Tactic_evalCalc___lam__0___boxed as *mut core::ffi::c_void,
                        9,
                        1,
                    );
                    lean_closure_set(v___f_1153_, 0, v_a_1150_);
                    v___f_1154_ = lean_alloc_closure(
                        l_Lean_Elab_Tactic_evalCalc___lam__1___boxed as *mut core::ffi::c_void,
                        9,
                        1,
                    );
                    lean_closure_set(v___f_1154_, 0, v_a_1150_);
                    v___x_1155_ = l_Lean_Expr_consumeMData(v_a_1152_);
                    lean_dec(v_a_1152_);
                    lean_inc(v_tag_1138_);
                    v___f_1156_ = lean_alloc_closure(
                        l_Lean_Elab_Tactic_evalCalc___lam__2___boxed as *mut core::ffi::c_void,
                        13,
                        6,
                    );
                    lean_closure_set(v___f_1156_, 0, v_a_1150_);
                    lean_closure_set(v___f_1156_, 1, v___x_1155_);
                    lean_closure_set(v___f_1156_, 2, v___f_1154_);
                    lean_closure_set(v___f_1156_, 3, v___f_1153_);
                    lean_closure_set(v___f_1156_, 4, v___x_1137_);
                    lean_closure_set(v___f_1156_, 5, v_tag_1138_);
                    v___x_1157_ = 0;
                    v___x_1158_ = lean_box((v___x_1157_) as usize);
                    v___x_1159_ = lean_alloc_closure(
                        l_Lean_Elab_Tactic_runTermElab___boxed as *mut core::ffi::c_void,
                        12,
                        3,
                    );
                    lean_closure_set(v___x_1159_, 0, lean_box(0));
                    lean_closure_set(v___x_1159_, 1, v___f_1156_);
                    lean_closure_set(v___x_1159_, 2, v___x_1158_);
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
                    if lean_obj_tag(v___x_1160_) == 0 {
                        v_a_1161_ = lean_ctor_get(v___x_1160_, 0);
                        lean_inc(v_a_1161_);
                        lean_dec_ref_known(v___x_1160_, 1);
                        v_fst_1162_ = lean_ctor_get(v_a_1161_, 0);
                        lean_inc(v_fst_1162_);
                        v_snd_1163_ = lean_ctor_get(v_a_1161_, 1);
                        lean_inc(v_snd_1163_);
                        lean_dec(v_a_1161_);
                        v___x_1164_ =
                            l_Lean_Elab_Tactic_pushGoals___redArg(v_snd_1163_, v___y_1141_);
                        if lean_obj_tag(v___x_1164_) == 0 {
                            v_isSharedCheck_1171_ = (!lean_is_exclusive(v___x_1164_)) as u8;
                            if v_isSharedCheck_1171_ == 0 {
                                v_unused_1172_ = lean_ctor_get(v___x_1164_, 0);
                                lean_dec(v_unused_1172_);
                                v___x_1166_ = v___x_1164_;
                                v_isShared_1167_ = v_isSharedCheck_1171_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec(v___x_1164_);
                                v___x_1166_ = lean_box(0);
                                v_isShared_1167_ = v_isSharedCheck_1171_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_fst_1162_);
                            v_a_1173_ = lean_ctor_get(v___x_1164_, 0);
                            v_isSharedCheck_1180_ = (!lean_is_exclusive(v___x_1164_)) as u8;
                            if v_isSharedCheck_1180_ == 0 {
                                v___x_1175_ = v___x_1164_;
                                v_isShared_1176_ = v_isSharedCheck_1180_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_1173_);
                                lean_dec(v___x_1164_);
                                v___x_1175_ = lean_box(0);
                                v_isShared_1176_ = v_isSharedCheck_1180_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        v_a_1181_ = lean_ctor_get(v___x_1160_, 0);
                        v_isSharedCheck_1188_ = (!lean_is_exclusive(v___x_1160_)) as u8;
                        if v_isSharedCheck_1188_ == 0 {
                            v___x_1183_ = v___x_1160_;
                            v_isShared_1184_ = v_isSharedCheck_1188_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_1181_);
                            lean_dec(v___x_1160_);
                            v___x_1183_ = lean_box(0);
                            v_isShared_1184_ = v_isSharedCheck_1188_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_1139_);
                    lean_dec(v_tag_1138_);
                    lean_dec_ref(v___x_1137_);
                    lean_dec_ref(v_target_1136_);
                    v_a_1189_ = lean_ctor_get(v___x_1149_, 0);
                    v_isSharedCheck_1196_ = (!lean_is_exclusive(v___x_1149_)) as u8;
                    if v_isSharedCheck_1196_ == 0 {
                        v___x_1191_ = v___x_1149_;
                        v_isShared_1192_ = v_isSharedCheck_1196_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_1189_);
                        lean_dec(v___x_1149_);
                        v___x_1191_ = lean_box(0);
                        v_isShared_1192_ = v_isSharedCheck_1196_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1167_ == 0 {
                    lean_ctor_set(v___x_1166_, 0, v_fst_1162_);
                    v___x_1169_ = v___x_1166_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_fst_1162_);
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
                    v_reuseFailAlloc_1179_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_a_1173_);
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
                    v_reuseFailAlloc_1187_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_a_1181_);
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
                    v_reuseFailAlloc_1195_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_a_1189_);
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
    mut v_steps_1197_: *mut LeanObject,
    mut v_target_1198_: *mut LeanObject,
    mut v___x_1199_: *mut LeanObject,
    mut v_tag_1200_: *mut LeanObject,
    mut v___x_1201_: *mut LeanObject,
    mut v___y_1202_: *mut LeanObject,
    mut v___y_1203_: *mut LeanObject,
    mut v___y_1204_: *mut LeanObject,
    mut v___y_1205_: *mut LeanObject,
    mut v___y_1206_: *mut LeanObject,
    mut v___y_1207_: *mut LeanObject,
    mut v___y_1208_: *mut LeanObject,
    mut v___y_1209_: *mut LeanObject,
    mut v___y_1210_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1211_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_1209_);
    lean_dec_ref(v___y_1208_);
    lean_dec(v___y_1207_);
    lean_dec_ref(v___y_1206_);
    lean_dec(v___y_1205_);
    lean_dec_ref(v___y_1204_);
    lean_dec(v___y_1203_);
    lean_dec_ref(v___y_1202_);
    return v_res_1211_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalCalc___lam__4(
    mut v_a_1212_: *mut LeanObject,
    mut v_trees_1213_: *mut LeanObject,
    mut v___y_1214_: *mut LeanObject,
    mut v___y_1215_: *mut LeanObject,
    mut v___y_1216_: *mut LeanObject,
    mut v___y_1217_: *mut LeanObject,
    mut v___y_1218_: *mut LeanObject,
    mut v___y_1219_: *mut LeanObject,
    mut v___y_1220_: *mut LeanObject,
    mut v___y_1221_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1227_: u8 = 0;
    let mut v___x_1228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1232_: u8 = 0;
    let mut v_a_1233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1236_: u8 = 0;
    let mut v___x_1238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1240_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_1221_);
                lean_inc_ref(v___y_1220_);
                lean_inc(v___y_1219_);
                lean_inc_ref(v___y_1218_);
                lean_inc(v___y_1217_);
                lean_inc_ref(v___y_1216_);
                lean_inc(v___y_1215_);
                lean_inc_ref(v___y_1214_);
                v___x_1223_ = lean_apply_9(
                    v_a_1212_,
                    v___y_1214_,
                    v___y_1215_,
                    v___y_1216_,
                    v___y_1217_,
                    v___y_1218_,
                    v___y_1219_,
                    v___y_1220_,
                    v___y_1221_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_1223_) == 0 {
                    v_a_1224_ = lean_ctor_get(v___x_1223_, 0);
                    v_isSharedCheck_1232_ = (!lean_is_exclusive(v___x_1223_)) as u8;
                    if v_isSharedCheck_1232_ == 0 {
                        v___x_1226_ = v___x_1223_;
                        v_isShared_1227_ = v_isSharedCheck_1232_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1224_);
                        lean_dec(v___x_1223_);
                        v___x_1226_ = lean_box(0);
                        v_isShared_1227_ = v_isSharedCheck_1232_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_trees_1213_);
                    v_a_1233_ = lean_ctor_get(v___x_1223_, 0);
                    v_isSharedCheck_1240_ = (!lean_is_exclusive(v___x_1223_)) as u8;
                    if v_isSharedCheck_1240_ == 0 {
                        v___x_1235_ = v___x_1223_;
                        v_isShared_1236_ = v_isSharedCheck_1240_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1233_);
                        lean_dec(v___x_1223_);
                        v___x_1235_ = lean_box(0);
                        v_isShared_1236_ = v_isSharedCheck_1240_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1228_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1228_, 0, v_a_1224_);
                lean_ctor_set(v___x_1228_, 1, v_trees_1213_);
                if v_isShared_1227_ == 0 {
                    lean_ctor_set(v___x_1226_, 0, v___x_1228_);
                    v___x_1230_ = v___x_1226_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1231_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1231_, 0, v___x_1228_);
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
                    v_reuseFailAlloc_1239_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_a_1233_);
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
    mut v_a_1241_: *mut LeanObject,
    mut v_trees_1242_: *mut LeanObject,
    mut v___y_1243_: *mut LeanObject,
    mut v___y_1244_: *mut LeanObject,
    mut v___y_1245_: *mut LeanObject,
    mut v___y_1246_: *mut LeanObject,
    mut v___y_1247_: *mut LeanObject,
    mut v___y_1248_: *mut LeanObject,
    mut v___y_1249_: *mut LeanObject,
    mut v___y_1250_: *mut LeanObject,
    mut v___y_1251_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1252_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_1250_);
    lean_dec_ref(v___y_1249_);
    lean_dec(v___y_1248_);
    lean_dec_ref(v___y_1247_);
    lean_dec(v___y_1246_);
    lean_dec_ref(v___y_1245_);
    lean_dec(v___y_1244_);
    lean_dec_ref(v___y_1243_);
    return v_res_1252_;
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___redArg___lam__0(
    mut v___y_1253_: *mut LeanObject,
    mut v_mkInfoTree_1254_: *mut LeanObject,
    mut v___y_1255_: *mut LeanObject,
    mut v___y_1256_: *mut LeanObject,
    mut v___y_1257_: *mut LeanObject,
    mut v___y_1258_: *mut LeanObject,
    mut v___y_1259_: *mut LeanObject,
    mut v___y_1260_: *mut LeanObject,
    mut v___y_1261_: *mut LeanObject,
    mut v_a_1262_: *mut LeanObject,
    mut v_a_x3f_1263_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_1266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trees_1267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1272_: u8 = 0;
    let mut v___x_1273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_1274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_1277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_1279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_1280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_1281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1285_: u8 = 0;
    let mut v_enabled_1286_: u8 = 0;
    let mut v_assignment_1287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_1288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1291_: u8 = 0;
    let mut v___x_1292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1304_: u8 = 0;
    let mut v_unused_1305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1306_: u8 = 0;
    let mut v_isSharedCheck_1307_: u8 = 0;
    let mut v_a_1308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1311_: u8 = 0;
    let mut v___x_1313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1315_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1265_ = lean_st_ref_get(v___y_1253_);
                v_infoState_1266_ = lean_ctor_get(v___x_1265_, 7);
                lean_inc_ref(v_infoState_1266_);
                lean_dec(v___x_1265_);
                v_trees_1267_ = lean_ctor_get(v_infoState_1266_, 2);
                lean_inc_ref(v_trees_1267_);
                lean_dec_ref(v_infoState_1266_);
                lean_inc(v___y_1253_);
                lean_inc_ref(v___y_1261_);
                lean_inc(v___y_1260_);
                lean_inc_ref(v___y_1259_);
                lean_inc(v___y_1258_);
                lean_inc_ref(v___y_1257_);
                lean_inc(v___y_1256_);
                lean_inc_ref(v___y_1255_);
                v___x_1268_ = lean_apply_10(
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
                    lean_box(0),
                );
                if lean_obj_tag(v___x_1268_) == 0 {
                    v_a_1269_ = lean_ctor_get(v___x_1268_, 0);
                    v_isSharedCheck_1307_ = (!lean_is_exclusive(v___x_1268_)) as u8;
                    if v_isSharedCheck_1307_ == 0 {
                        v___x_1271_ = v___x_1268_;
                        v_isShared_1272_ = v_isSharedCheck_1307_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1269_);
                        lean_dec(v___x_1268_);
                        v___x_1271_ = lean_box(0);
                        v_isShared_1272_ = v_isSharedCheck_1307_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_a_1262_);
                    v_a_1308_ = lean_ctor_get(v___x_1268_, 0);
                    v_isSharedCheck_1315_ = (!lean_is_exclusive(v___x_1268_)) as u8;
                    if v_isSharedCheck_1315_ == 0 {
                        v___x_1310_ = v___x_1268_;
                        v_isShared_1311_ = v_isSharedCheck_1315_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_1308_);
                        lean_dec(v___x_1268_);
                        v___x_1310_ = lean_box(0);
                        v_isShared_1311_ = v_isSharedCheck_1315_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1273_ = lean_st_ref_take(v___y_1253_);
                v_infoState_1274_ = lean_ctor_get(v___x_1273_, 7);
                v_env_1275_ = lean_ctor_get(v___x_1273_, 0);
                v_nextMacroScope_1276_ = lean_ctor_get(v___x_1273_, 1);
                v_ngen_1277_ = lean_ctor_get(v___x_1273_, 2);
                v_auxDeclNGen_1278_ = lean_ctor_get(v___x_1273_, 3);
                v_traceState_1279_ = lean_ctor_get(v___x_1273_, 4);
                v_cache_1280_ = lean_ctor_get(v___x_1273_, 5);
                v_messages_1281_ = lean_ctor_get(v___x_1273_, 6);
                v_snapshotTasks_1282_ = lean_ctor_get(v___x_1273_, 8);
                v_isSharedCheck_1306_ = (!lean_is_exclusive(v___x_1273_)) as u8;
                if v_isSharedCheck_1306_ == 0 {
                    v___x_1284_ = v___x_1273_;
                    v_isShared_1285_ = v_isSharedCheck_1306_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_1282_);
                    lean_inc(v_infoState_1274_);
                    lean_inc(v_messages_1281_);
                    lean_inc(v_cache_1280_);
                    lean_inc(v_traceState_1279_);
                    lean_inc(v_auxDeclNGen_1278_);
                    lean_inc(v_ngen_1277_);
                    lean_inc(v_nextMacroScope_1276_);
                    lean_inc(v_env_1275_);
                    lean_dec(v___x_1273_);
                    v___x_1284_ = lean_box(0);
                    v_isShared_1285_ = v_isSharedCheck_1306_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_enabled_1286_ = lean_ctor_get_uint8(
                    v_infoState_1274_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_assignment_1287_ = lean_ctor_get(v_infoState_1274_, 0);
                v_lazyAssignment_1288_ = lean_ctor_get(v_infoState_1274_, 1);
                v_isSharedCheck_1304_ = (!lean_is_exclusive(v_infoState_1274_)) as u8;
                if v_isSharedCheck_1304_ == 0 {
                    v_unused_1305_ = lean_ctor_get(v_infoState_1274_, 2);
                    lean_dec(v_unused_1305_);
                    v___x_1290_ = v_infoState_1274_;
                    v_isShared_1291_ = v_isSharedCheck_1304_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_lazyAssignment_1288_);
                    lean_inc(v_assignment_1287_);
                    lean_dec(v_infoState_1274_);
                    v___x_1290_ = lean_box(0);
                    v_isShared_1291_ = v_isSharedCheck_1304_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1292_ = l_Lean_PersistentArray_push___redArg(v_a_1262_, v_a_1269_);
                if v_isShared_1291_ == 0 {
                    lean_ctor_set(v___x_1290_, 2, v___x_1292_);
                    v___x_1294_ = v___x_1290_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1303_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1303_, 0, v_assignment_1287_);
                    lean_ctor_set(v_reuseFailAlloc_1303_, 1, v_lazyAssignment_1288_);
                    lean_ctor_set(v_reuseFailAlloc_1303_, 2, v___x_1292_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1303_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_enabled_1286_,
                    );
                    v___x_1294_ = v_reuseFailAlloc_1303_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1285_ == 0 {
                    lean_ctor_set(v___x_1284_, 7, v___x_1294_);
                    v___x_1296_ = v___x_1284_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1302_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_env_1275_);
                    lean_ctor_set(v_reuseFailAlloc_1302_, 1, v_nextMacroScope_1276_);
                    lean_ctor_set(v_reuseFailAlloc_1302_, 2, v_ngen_1277_);
                    lean_ctor_set(v_reuseFailAlloc_1302_, 3, v_auxDeclNGen_1278_);
                    lean_ctor_set(v_reuseFailAlloc_1302_, 4, v_traceState_1279_);
                    lean_ctor_set(v_reuseFailAlloc_1302_, 5, v_cache_1280_);
                    lean_ctor_set(v_reuseFailAlloc_1302_, 6, v_messages_1281_);
                    lean_ctor_set(v_reuseFailAlloc_1302_, 7, v___x_1294_);
                    lean_ctor_set(v_reuseFailAlloc_1302_, 8, v_snapshotTasks_1282_);
                    v___x_1296_ = v_reuseFailAlloc_1302_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1297_ = lean_st_ref_set(v___y_1253_, v___x_1296_);
                v___x_1298_ = lean_box(0);
                if v_isShared_1272_ == 0 {
                    lean_ctor_set(v___x_1271_, 0, v___x_1298_);
                    v___x_1300_ = v___x_1271_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1301_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1301_, 0, v___x_1298_);
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
                    v_reuseFailAlloc_1314_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1314_, 0, v_a_1308_);
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
    mut v___y_1316_: *mut LeanObject,
    mut v_mkInfoTree_1317_: *mut LeanObject,
    mut v___y_1318_: *mut LeanObject,
    mut v___y_1319_: *mut LeanObject,
    mut v___y_1320_: *mut LeanObject,
    mut v___y_1321_: *mut LeanObject,
    mut v___y_1322_: *mut LeanObject,
    mut v___y_1323_: *mut LeanObject,
    mut v___y_1324_: *mut LeanObject,
    mut v_a_1325_: *mut LeanObject,
    mut v_a_x3f_1326_: *mut LeanObject,
    mut v___y_1327_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1328_: *mut LeanObject = core::ptr::null_mut();
    v_res_1328_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___redArg___lam__0(v___y_1316_, v_mkInfoTree_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v_a_1325_, v_a_x3f_1326_);
    lean_dec(v_a_x3f_1326_);
    lean_dec_ref(v___y_1324_);
    lean_dec(v___y_1323_);
    lean_dec_ref(v___y_1322_);
    lean_dec(v___y_1321_);
    lean_dec_ref(v___y_1320_);
    lean_dec(v___y_1319_);
    lean_dec_ref(v___y_1318_);
    lean_dec(v___y_1316_);
    return v_res_1328_;
}
pub unsafe fn _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_1329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut LeanObject = core::ptr::null_mut();
    v___x_1329_ = lean_unsigned_to_nat(32);
    v___x_1330_ = lean_mk_empty_array_with_capacity(v___x_1329_);
    v___x_1331_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1331_, 0, v___x_1330_);
    return v___x_1331_;
}
pub unsafe fn _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_1332_: usize = 0;
    let mut v___x_1333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut LeanObject = core::ptr::null_mut();
    v___x_1332_ = 5usize;
    v___x_1333_ = lean_unsigned_to_nat(0);
    v___x_1334_ = lean_unsigned_to_nat(32);
    v___x_1335_ = lean_mk_empty_array_with_capacity(v___x_1334_);
    v___x_1336_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg___closed__0_once), _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg___closed__0);
    v___x_1337_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_1337_, 0, v___x_1336_);
    lean_ctor_set(v___x_1337_, 1, v___x_1335_);
    lean_ctor_set(v___x_1337_, 2, v___x_1333_);
    lean_ctor_set(v___x_1337_, 3, v___x_1333_);
    lean_ctor_set_usize(v___x_1337_, 4, v___x_1332_);
    return v___x_1337_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg(
    mut v___y_1338_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_1341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trees_1342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_1344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_1347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_1349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_1350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_1351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1355_: u8 = 0;
    let mut v_enabled_1356_: u8 = 0;
    let mut v_assignment_1357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_1358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1361_: u8 = 0;
    let mut v___x_1362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1371_: u8 = 0;
    let mut v_unused_1372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1373_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1340_ = lean_st_ref_get(v___y_1338_);
                v_infoState_1341_ = lean_ctor_get(v___x_1340_, 7);
                lean_inc_ref(v_infoState_1341_);
                lean_dec(v___x_1340_);
                v_trees_1342_ = lean_ctor_get(v_infoState_1341_, 2);
                lean_inc_ref(v_trees_1342_);
                lean_dec_ref(v_infoState_1341_);
                v___x_1343_ = lean_st_ref_take(v___y_1338_);
                v_infoState_1344_ = lean_ctor_get(v___x_1343_, 7);
                v_env_1345_ = lean_ctor_get(v___x_1343_, 0);
                v_nextMacroScope_1346_ = lean_ctor_get(v___x_1343_, 1);
                v_ngen_1347_ = lean_ctor_get(v___x_1343_, 2);
                v_auxDeclNGen_1348_ = lean_ctor_get(v___x_1343_, 3);
                v_traceState_1349_ = lean_ctor_get(v___x_1343_, 4);
                v_cache_1350_ = lean_ctor_get(v___x_1343_, 5);
                v_messages_1351_ = lean_ctor_get(v___x_1343_, 6);
                v_snapshotTasks_1352_ = lean_ctor_get(v___x_1343_, 8);
                v_isSharedCheck_1373_ = (!lean_is_exclusive(v___x_1343_)) as u8;
                if v_isSharedCheck_1373_ == 0 {
                    v___x_1354_ = v___x_1343_;
                    v_isShared_1355_ = v_isSharedCheck_1373_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_1352_);
                    lean_inc(v_infoState_1344_);
                    lean_inc(v_messages_1351_);
                    lean_inc(v_cache_1350_);
                    lean_inc(v_traceState_1349_);
                    lean_inc(v_auxDeclNGen_1348_);
                    lean_inc(v_ngen_1347_);
                    lean_inc(v_nextMacroScope_1346_);
                    lean_inc(v_env_1345_);
                    lean_dec(v___x_1343_);
                    v___x_1354_ = lean_box(0);
                    v_isShared_1355_ = v_isSharedCheck_1373_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_enabled_1356_ = lean_ctor_get_uint8(
                    v_infoState_1344_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_assignment_1357_ = lean_ctor_get(v_infoState_1344_, 0);
                v_lazyAssignment_1358_ = lean_ctor_get(v_infoState_1344_, 1);
                v_isSharedCheck_1371_ = (!lean_is_exclusive(v_infoState_1344_)) as u8;
                if v_isSharedCheck_1371_ == 0 {
                    v_unused_1372_ = lean_ctor_get(v_infoState_1344_, 2);
                    lean_dec(v_unused_1372_);
                    v___x_1360_ = v_infoState_1344_;
                    v_isShared_1361_ = v_isSharedCheck_1371_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_lazyAssignment_1358_);
                    lean_inc(v_assignment_1357_);
                    lean_dec(v_infoState_1344_);
                    v___x_1360_ = lean_box(0);
                    v_isShared_1361_ = v_isSharedCheck_1371_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1362_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg___closed__1_once), _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg___closed__1);
                if v_isShared_1361_ == 0 {
                    lean_ctor_set(v___x_1360_, 2, v___x_1362_);
                    v___x_1364_ = v___x_1360_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1370_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_assignment_1357_);
                    lean_ctor_set(v_reuseFailAlloc_1370_, 1, v_lazyAssignment_1358_);
                    lean_ctor_set(v_reuseFailAlloc_1370_, 2, v___x_1362_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1370_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_enabled_1356_,
                    );
                    v___x_1364_ = v_reuseFailAlloc_1370_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1355_ == 0 {
                    lean_ctor_set(v___x_1354_, 7, v___x_1364_);
                    v___x_1366_ = v___x_1354_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_env_1345_);
                    lean_ctor_set(v_reuseFailAlloc_1369_, 1, v_nextMacroScope_1346_);
                    lean_ctor_set(v_reuseFailAlloc_1369_, 2, v_ngen_1347_);
                    lean_ctor_set(v_reuseFailAlloc_1369_, 3, v_auxDeclNGen_1348_);
                    lean_ctor_set(v_reuseFailAlloc_1369_, 4, v_traceState_1349_);
                    lean_ctor_set(v_reuseFailAlloc_1369_, 5, v_cache_1350_);
                    lean_ctor_set(v_reuseFailAlloc_1369_, 6, v_messages_1351_);
                    lean_ctor_set(v_reuseFailAlloc_1369_, 7, v___x_1364_);
                    lean_ctor_set(v_reuseFailAlloc_1369_, 8, v_snapshotTasks_1352_);
                    v___x_1366_ = v_reuseFailAlloc_1369_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1367_ = lean_st_ref_set(v___y_1338_, v___x_1366_);
                v___x_1368_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1368_, 0, v_trees_1342_);
                return v___x_1368_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg___boxed(
    mut v___y_1374_: *mut LeanObject,
    mut v___y_1375_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1376_: *mut LeanObject = core::ptr::null_mut();
    v_res_1376_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg(v___y_1374_);
    lean_dec(v___y_1374_);
    return v_res_1376_;
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___redArg(
    mut v_x_1377_: *mut LeanObject,
    mut v_mkInfoTree_1378_: *mut LeanObject,
    mut v___y_1379_: *mut LeanObject,
    mut v___y_1380_: *mut LeanObject,
    mut v___y_1381_: *mut LeanObject,
    mut v___y_1382_: *mut LeanObject,
    mut v___y_1383_: *mut LeanObject,
    mut v___y_1384_: *mut LeanObject,
    mut v___y_1385_: *mut LeanObject,
    mut v___y_1386_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_1389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_enabled_1390_: u8 = 0;
    let mut v___x_1391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1398_: u8 = 0;
    let mut v___x_1400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1404_: u8 = 0;
    let mut v___x_1406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1408_: u8 = 0;
    let mut v_unused_1409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1413_: u8 = 0;
    let mut v___x_1415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1417_: u8 = 0;
    let mut v_reuseFailAlloc_1418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1419_: u8 = 0;
    let mut v_a_1420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1425_: u8 = 0;
    let mut v___x_1427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1429_: u8 = 0;
    let mut v_unused_1430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1434_: u8 = 0;
    let mut v___x_1436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1438_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1388_ = lean_st_ref_get(v___y_1386_);
                v_infoState_1389_ = lean_ctor_get(v___x_1388_, 7);
                lean_inc_ref(v_infoState_1389_);
                lean_dec(v___x_1388_);
                v_enabled_1390_ = lean_ctor_get_uint8(
                    v_infoState_1389_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                lean_dec_ref(v_infoState_1389_);
                if v_enabled_1390_ == 0 {
                    lean_dec_ref(v_mkInfoTree_1378_);
                    lean_inc(v___y_1386_);
                    lean_inc_ref(v___y_1385_);
                    lean_inc(v___y_1384_);
                    lean_inc_ref(v___y_1383_);
                    lean_inc(v___y_1382_);
                    lean_inc_ref(v___y_1381_);
                    lean_inc(v___y_1380_);
                    lean_inc_ref(v___y_1379_);
                    v___x_1391_ = lean_apply_9(
                        v_x_1377_,
                        v___y_1379_,
                        v___y_1380_,
                        v___y_1381_,
                        v___y_1382_,
                        v___y_1383_,
                        v___y_1384_,
                        v___y_1385_,
                        v___y_1386_,
                        lean_box(0),
                    );
                    return v___x_1391_;
                } else {
                    v___x_1392_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg(v___y_1386_);
                    v_a_1393_ = lean_ctor_get(v___x_1392_, 0);
                    lean_inc(v_a_1393_);
                    lean_dec_ref(v___x_1392_);
                    lean_inc(v___y_1386_);
                    lean_inc_ref(v___y_1385_);
                    lean_inc(v___y_1384_);
                    lean_inc_ref(v___y_1383_);
                    lean_inc(v___y_1382_);
                    lean_inc_ref(v___y_1381_);
                    lean_inc(v___y_1380_);
                    lean_inc_ref(v___y_1379_);
                    v_r_1394_ = lean_apply_9(
                        v_x_1377_,
                        v___y_1379_,
                        v___y_1380_,
                        v___y_1381_,
                        v___y_1382_,
                        v___y_1383_,
                        v___y_1384_,
                        v___y_1385_,
                        v___y_1386_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v_r_1394_) == 0 {
                        v_a_1395_ = lean_ctor_get(v_r_1394_, 0);
                        v_isSharedCheck_1419_ = (!lean_is_exclusive(v_r_1394_)) as u8;
                        if v_isSharedCheck_1419_ == 0 {
                            v___x_1397_ = v_r_1394_;
                            v_isShared_1398_ = v_isSharedCheck_1419_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1395_);
                            lean_dec(v_r_1394_);
                            v___x_1397_ = lean_box(0);
                            v_isShared_1398_ = v_isSharedCheck_1419_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1420_ = lean_ctor_get(v_r_1394_, 0);
                        lean_inc(v_a_1420_);
                        lean_dec_ref_known(v_r_1394_, 1);
                        v___x_1421_ = lean_box(0);
                        v___x_1422_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___redArg___lam__0(v___y_1386_, v_mkInfoTree_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v_a_1393_, v___x_1421_);
                        if lean_obj_tag(v___x_1422_) == 0 {
                            v_isSharedCheck_1429_ = (!lean_is_exclusive(v___x_1422_)) as u8;
                            if v_isSharedCheck_1429_ == 0 {
                                v_unused_1430_ = lean_ctor_get(v___x_1422_, 0);
                                lean_dec(v_unused_1430_);
                                v___x_1424_ = v___x_1422_;
                                v_isShared_1425_ = v_isSharedCheck_1429_;
                                state = 7;
                                continue;
                            } else {
                                lean_dec(v___x_1422_);
                                v___x_1424_ = lean_box(0);
                                v_isShared_1425_ = v_isSharedCheck_1429_;
                                state = 7;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_1420_);
                            v_a_1431_ = lean_ctor_get(v___x_1422_, 0);
                            v_isSharedCheck_1438_ = (!lean_is_exclusive(v___x_1422_)) as u8;
                            if v_isSharedCheck_1438_ == 0 {
                                v___x_1433_ = v___x_1422_;
                                v_isShared_1434_ = v_isSharedCheck_1438_;
                                state = 9;
                                continue;
                            } else {
                                lean_inc(v_a_1431_);
                                lean_dec(v___x_1422_);
                                v___x_1433_ = lean_box(0);
                                v_isShared_1434_ = v_isSharedCheck_1438_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                lean_inc(v_a_1395_);
                if v_isShared_1398_ == 0 {
                    lean_ctor_set_tag(v___x_1397_, 1);
                    v___x_1400_ = v___x_1397_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1418_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_a_1395_);
                    v___x_1400_ = v_reuseFailAlloc_1418_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1401_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___redArg___lam__0(v___y_1386_, v_mkInfoTree_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v_a_1393_, v___x_1400_);
                lean_dec_ref(v___x_1400_);
                if lean_obj_tag(v___x_1401_) == 0 {
                    v_isSharedCheck_1408_ = (!lean_is_exclusive(v___x_1401_)) as u8;
                    if v_isSharedCheck_1408_ == 0 {
                        v_unused_1409_ = lean_ctor_get(v___x_1401_, 0);
                        lean_dec(v_unused_1409_);
                        v___x_1403_ = v___x_1401_;
                        v_isShared_1404_ = v_isSharedCheck_1408_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v___x_1401_);
                        v___x_1403_ = lean_box(0);
                        v_isShared_1404_ = v_isSharedCheck_1408_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_1395_);
                    v_a_1410_ = lean_ctor_get(v___x_1401_, 0);
                    v_isSharedCheck_1417_ = (!lean_is_exclusive(v___x_1401_)) as u8;
                    if v_isSharedCheck_1417_ == 0 {
                        v___x_1412_ = v___x_1401_;
                        v_isShared_1413_ = v_isSharedCheck_1417_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_1410_);
                        lean_dec(v___x_1401_);
                        v___x_1412_ = lean_box(0);
                        v_isShared_1413_ = v_isSharedCheck_1417_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_1404_ == 0 {
                    lean_ctor_set(v___x_1403_, 0, v_a_1395_);
                    v___x_1406_ = v___x_1403_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1407_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1407_, 0, v_a_1395_);
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
                    v_reuseFailAlloc_1416_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_a_1410_);
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
                    lean_ctor_set_tag(v___x_1424_, 1);
                    lean_ctor_set(v___x_1424_, 0, v_a_1420_);
                    v___x_1427_ = v___x_1424_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1428_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_a_1420_);
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
                    v_reuseFailAlloc_1437_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_a_1431_);
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
    mut v_x_1439_: *mut LeanObject,
    mut v_mkInfoTree_1440_: *mut LeanObject,
    mut v___y_1441_: *mut LeanObject,
    mut v___y_1442_: *mut LeanObject,
    mut v___y_1443_: *mut LeanObject,
    mut v___y_1444_: *mut LeanObject,
    mut v___y_1445_: *mut LeanObject,
    mut v___y_1446_: *mut LeanObject,
    mut v___y_1447_: *mut LeanObject,
    mut v___y_1448_: *mut LeanObject,
    mut v___y_1449_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1450_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_1448_);
    lean_dec_ref(v___y_1447_);
    lean_dec(v___y_1446_);
    lean_dec_ref(v___y_1445_);
    lean_dec(v___y_1444_);
    lean_dec_ref(v___y_1443_);
    lean_dec(v___y_1442_);
    lean_dec_ref(v___y_1441_);
    return v_res_1450_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalCalc___lam__5(
    mut v_steps_1451_: *mut LeanObject,
    mut v___x_1452_: *mut LeanObject,
    mut v___x_1453_: *mut LeanObject,
    mut v_target_1454_: *mut LeanObject,
    mut v_tag_1455_: *mut LeanObject,
    mut v___y_1456_: *mut LeanObject,
    mut v___y_1457_: *mut LeanObject,
    mut v___y_1458_: *mut LeanObject,
    mut v___y_1459_: *mut LeanObject,
    mut v___y_1460_: *mut LeanObject,
    mut v___y_1461_: *mut LeanObject,
    mut v___y_1462_: *mut LeanObject,
    mut v___y_1463_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1473_: u8 = 0;
    let mut v___x_1475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1477_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_steps_1451_);
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
                if lean_obj_tag(v___x_1465_) == 0 {
                    v_a_1466_ = lean_ctor_get(v___x_1465_, 0);
                    lean_inc(v_a_1466_);
                    lean_dec_ref_known(v___x_1465_, 1);
                    v___f_1467_ = lean_alloc_closure(
                        l_Lean_Elab_Tactic_evalCalc___lam__3___boxed as *mut core::ffi::c_void,
                        14,
                        5,
                    );
                    lean_closure_set(v___f_1467_, 0, v_steps_1451_);
                    lean_closure_set(v___f_1467_, 1, v_target_1454_);
                    lean_closure_set(v___f_1467_, 2, v___x_1452_);
                    lean_closure_set(v___f_1467_, 3, v_tag_1455_);
                    lean_closure_set(v___f_1467_, 4, v___x_1453_);
                    v___f_1468_ = lean_alloc_closure(
                        l_Lean_Elab_Tactic_evalCalc___lam__4___boxed as *mut core::ffi::c_void,
                        11,
                        1,
                    );
                    lean_closure_set(v___f_1468_, 0, v_a_1466_);
                    v___x_1469_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3___redArg(v___f_1467_, v___f_1468_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
                    return v___x_1469_;
                } else {
                    lean_dec(v_tag_1455_);
                    lean_dec_ref(v_target_1454_);
                    lean_dec(v___x_1453_);
                    lean_dec_ref(v___x_1452_);
                    lean_dec(v_steps_1451_);
                    v_a_1470_ = lean_ctor_get(v___x_1465_, 0);
                    v_isSharedCheck_1477_ = (!lean_is_exclusive(v___x_1465_)) as u8;
                    if v_isSharedCheck_1477_ == 0 {
                        v___x_1472_ = v___x_1465_;
                        v_isShared_1473_ = v_isSharedCheck_1477_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1470_);
                        lean_dec(v___x_1465_);
                        v___x_1472_ = lean_box(0);
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
                    v_reuseFailAlloc_1476_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_a_1470_);
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
    mut v_steps_1478_: *mut LeanObject,
    mut v___x_1479_: *mut LeanObject,
    mut v___x_1480_: *mut LeanObject,
    mut v_target_1481_: *mut LeanObject,
    mut v_tag_1482_: *mut LeanObject,
    mut v___y_1483_: *mut LeanObject,
    mut v___y_1484_: *mut LeanObject,
    mut v___y_1485_: *mut LeanObject,
    mut v___y_1486_: *mut LeanObject,
    mut v___y_1487_: *mut LeanObject,
    mut v___y_1488_: *mut LeanObject,
    mut v___y_1489_: *mut LeanObject,
    mut v___y_1490_: *mut LeanObject,
    mut v___y_1491_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1492_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_1490_);
    lean_dec_ref(v___y_1489_);
    lean_dec(v___y_1488_);
    lean_dec_ref(v___y_1487_);
    lean_dec(v___y_1486_);
    lean_dec_ref(v___y_1485_);
    lean_dec(v___y_1484_);
    lean_dec_ref(v___y_1483_);
    return v_res_1492_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalCalc(
    mut v_x_1505_: *mut LeanObject,
    mut v_a_1506_: *mut LeanObject,
    mut v_a_1507_: *mut LeanObject,
    mut v_a_1508_: *mut LeanObject,
    mut v_a_1509_: *mut LeanObject,
    mut v_a_1510_: *mut LeanObject,
    mut v_a_1511_: *mut LeanObject,
    mut v_a_1512_: *mut LeanObject,
    mut v_a_1513_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: u8 = 0;
    v___x_1515_ = l_Lean_Elab_Tactic_evalCalc___closed__2;
    lean_inc(v_x_1505_);
    v___x_1516_ = l_Lean_Syntax_isOfKind(v_x_1505_, v___x_1515_);
    if v___x_1516_ == 0 {
        let mut v___x_1517_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_1505_);
        v___x_1517_ =
            l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0___redArg(
            );
        return v___x_1517_;
    } else {
        let mut v___x_1518_: *mut LeanObject = core::ptr::null_mut();
        let mut v_steps_1519_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1520_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1521_: u8 = 0;
        v___x_1518_ = lean_unsigned_to_nat(1);
        v_steps_1519_ = l_Lean_Syntax_getArg(v_x_1505_, v___x_1518_);
        v___x_1520_ = l_Lean_Elab_Tactic_evalCalc___closed__4;
        lean_inc(v_steps_1519_);
        v___x_1521_ = l_Lean_Syntax_isOfKind(v_steps_1519_, v___x_1520_);
        if v___x_1521_ == 0 {
            let mut v___x_1522_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_steps_1519_);
            lean_dec(v_x_1505_);
            v___x_1522_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalCalc_spec__0___redArg();
            return v___x_1522_;
        } else {
            let mut v_fileName_1523_: *mut LeanObject = core::ptr::null_mut();
            let mut v_fileMap_1524_: *mut LeanObject = core::ptr::null_mut();
            let mut v_options_1525_: *mut LeanObject = core::ptr::null_mut();
            let mut v_currRecDepth_1526_: *mut LeanObject = core::ptr::null_mut();
            let mut v_maxRecDepth_1527_: *mut LeanObject = core::ptr::null_mut();
            let mut v_ref_1528_: *mut LeanObject = core::ptr::null_mut();
            let mut v_currNamespace_1529_: *mut LeanObject = core::ptr::null_mut();
            let mut v_openDecls_1530_: *mut LeanObject = core::ptr::null_mut();
            let mut v_initHeartbeats_1531_: *mut LeanObject = core::ptr::null_mut();
            let mut v_maxHeartbeats_1532_: *mut LeanObject = core::ptr::null_mut();
            let mut v_quotContext_1533_: *mut LeanObject = core::ptr::null_mut();
            let mut v_currMacroScope_1534_: *mut LeanObject = core::ptr::null_mut();
            let mut v_diag_1535_: u8 = 0;
            let mut v_cancelTk_x3f_1536_: *mut LeanObject = core::ptr::null_mut();
            let mut v_suppressElabErrors_1537_: u8 = 0;
            let mut v_inheritedTraceOptions_1538_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1539_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tk_1540_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1541_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1542_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_1543_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1544_: u8 = 0;
            let mut v_ref_1545_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1546_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1547_: *mut LeanObject = core::ptr::null_mut();
            v_fileName_1523_ = lean_ctor_get(v_a_1512_, 0);
            v_fileMap_1524_ = lean_ctor_get(v_a_1512_, 1);
            v_options_1525_ = lean_ctor_get(v_a_1512_, 2);
            v_currRecDepth_1526_ = lean_ctor_get(v_a_1512_, 3);
            v_maxRecDepth_1527_ = lean_ctor_get(v_a_1512_, 4);
            v_ref_1528_ = lean_ctor_get(v_a_1512_, 5);
            v_currNamespace_1529_ = lean_ctor_get(v_a_1512_, 6);
            v_openDecls_1530_ = lean_ctor_get(v_a_1512_, 7);
            v_initHeartbeats_1531_ = lean_ctor_get(v_a_1512_, 8);
            v_maxHeartbeats_1532_ = lean_ctor_get(v_a_1512_, 9);
            v_quotContext_1533_ = lean_ctor_get(v_a_1512_, 10);
            v_currMacroScope_1534_ = lean_ctor_get(v_a_1512_, 11);
            v_diag_1535_ = lean_ctor_get_uint8(
                v_a_1512_,
                (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
            );
            v_cancelTk_x3f_1536_ = lean_ctor_get(v_a_1512_, 12);
            v_suppressElabErrors_1537_ = lean_ctor_get_uint8(
                v_a_1512_,
                (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
            );
            v_inheritedTraceOptions_1538_ = lean_ctor_get(v_a_1512_, 13);
            v___x_1539_ = lean_unsigned_to_nat(0);
            v_tk_1540_ = l_Lean_Syntax_getArg(v_x_1505_, v___x_1539_);
            lean_dec(v_x_1505_);
            v___x_1541_ = l_Lean_Elab_Tactic_evalCalc___closed__5;
            v___x_1542_ = l_Lean_Elab_Tactic_evalCalc___closed__6;
            v___f_1543_ = lean_alloc_closure(
                l_Lean_Elab_Tactic_evalCalc___lam__5___boxed as *mut core::ffi::c_void,
                14,
                3,
            );
            lean_closure_set(v___f_1543_, 0, v_steps_1519_);
            lean_closure_set(v___f_1543_, 1, v___x_1541_);
            lean_closure_set(v___f_1543_, 2, v___x_1542_);
            v___x_1544_ = 0;
            v_ref_1545_ = l_Lean_replaceRef(v_tk_1540_, v_ref_1528_);
            lean_dec(v_tk_1540_);
            lean_inc_ref(v_inheritedTraceOptions_1538_);
            lean_inc(v_cancelTk_x3f_1536_);
            lean_inc(v_currMacroScope_1534_);
            lean_inc(v_quotContext_1533_);
            lean_inc(v_maxHeartbeats_1532_);
            lean_inc(v_initHeartbeats_1531_);
            lean_inc(v_openDecls_1530_);
            lean_inc(v_currNamespace_1529_);
            lean_inc(v_maxRecDepth_1527_);
            lean_inc(v_currRecDepth_1526_);
            lean_inc_ref(v_options_1525_);
            lean_inc_ref(v_fileMap_1524_);
            lean_inc_ref(v_fileName_1523_);
            v___x_1546_ = lean_alloc_ctor(0, 14, (2) as u32);
            lean_ctor_set(v___x_1546_, 0, v_fileName_1523_);
            lean_ctor_set(v___x_1546_, 1, v_fileMap_1524_);
            lean_ctor_set(v___x_1546_, 2, v_options_1525_);
            lean_ctor_set(v___x_1546_, 3, v_currRecDepth_1526_);
            lean_ctor_set(v___x_1546_, 4, v_maxRecDepth_1527_);
            lean_ctor_set(v___x_1546_, 5, v_ref_1545_);
            lean_ctor_set(v___x_1546_, 6, v_currNamespace_1529_);
            lean_ctor_set(v___x_1546_, 7, v_openDecls_1530_);
            lean_ctor_set(v___x_1546_, 8, v_initHeartbeats_1531_);
            lean_ctor_set(v___x_1546_, 9, v_maxHeartbeats_1532_);
            lean_ctor_set(v___x_1546_, 10, v_quotContext_1533_);
            lean_ctor_set(v___x_1546_, 11, v_currMacroScope_1534_);
            lean_ctor_set(v___x_1546_, 12, v_cancelTk_x3f_1536_);
            lean_ctor_set(v___x_1546_, 13, v_inheritedTraceOptions_1538_);
            lean_ctor_set_uint8(
                v___x_1546_,
                (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                v_diag_1535_,
            );
            lean_ctor_set_uint8(
                v___x_1546_,
                (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
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
            lean_dec_ref_known(v___x_1546_, 14);
            return v___x_1547_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalCalc___boxed(
    mut v_x_1548_: *mut LeanObject,
    mut v_a_1549_: *mut LeanObject,
    mut v_a_1550_: *mut LeanObject,
    mut v_a_1551_: *mut LeanObject,
    mut v_a_1552_: *mut LeanObject,
    mut v_a_1553_: *mut LeanObject,
    mut v_a_1554_: *mut LeanObject,
    mut v_a_1555_: *mut LeanObject,
    mut v_a_1556_: *mut LeanObject,
    mut v_a_1557_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1558_: *mut LeanObject = core::ptr::null_mut();
    v_res_1558_ = l_Lean_Elab_Tactic_evalCalc(
        v_x_1548_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_,
        v_a_1556_,
    );
    lean_dec(v_a_1556_);
    lean_dec_ref(v_a_1555_);
    lean_dec(v_a_1554_);
    lean_dec_ref(v_a_1553_);
    lean_dec(v_a_1552_);
    lean_dec_ref(v_a_1551_);
    lean_dec(v_a_1550_);
    lean_dec_ref(v_a_1549_);
    return v_res_1558_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3(
    mut v___y_1559_: *mut LeanObject,
    mut v___y_1560_: *mut LeanObject,
    mut v___y_1561_: *mut LeanObject,
    mut v___y_1562_: *mut LeanObject,
    mut v___y_1563_: *mut LeanObject,
    mut v___y_1564_: *mut LeanObject,
    mut v___y_1565_: *mut LeanObject,
    mut v___y_1566_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1568_: *mut LeanObject = core::ptr::null_mut();
    v___x_1568_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___redArg(v___y_1566_);
    return v___x_1568_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3___boxed(
    mut v___y_1569_: *mut LeanObject,
    mut v___y_1570_: *mut LeanObject,
    mut v___y_1571_: *mut LeanObject,
    mut v___y_1572_: *mut LeanObject,
    mut v___y_1573_: *mut LeanObject,
    mut v___y_1574_: *mut LeanObject,
    mut v___y_1575_: *mut LeanObject,
    mut v___y_1576_: *mut LeanObject,
    mut v___y_1577_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1578_: *mut LeanObject = core::ptr::null_mut();
    v_res_1578_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3_spec__3(v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_);
    lean_dec(v___y_1576_);
    lean_dec_ref(v___y_1575_);
    lean_dec(v___y_1574_);
    lean_dec_ref(v___y_1573_);
    lean_dec(v___y_1572_);
    lean_dec_ref(v___y_1571_);
    lean_dec(v___y_1570_);
    lean_dec_ref(v___y_1569_);
    return v_res_1578_;
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalCalc_spec__3(
    mut v_00_u03b1_1579_: *mut LeanObject,
    mut v_x_1580_: *mut LeanObject,
    mut v_mkInfoTree_1581_: *mut LeanObject,
    mut v___y_1582_: *mut LeanObject,
    mut v___y_1583_: *mut LeanObject,
    mut v___y_1584_: *mut LeanObject,
    mut v___y_1585_: *mut LeanObject,
    mut v___y_1586_: *mut LeanObject,
    mut v___y_1587_: *mut LeanObject,
    mut v___y_1588_: *mut LeanObject,
    mut v___y_1589_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1591_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1592_: *mut LeanObject,
    mut v_x_1593_: *mut LeanObject,
    mut v_mkInfoTree_1594_: *mut LeanObject,
    mut v___y_1595_: *mut LeanObject,
    mut v___y_1596_: *mut LeanObject,
    mut v___y_1597_: *mut LeanObject,
    mut v___y_1598_: *mut LeanObject,
    mut v___y_1599_: *mut LeanObject,
    mut v___y_1600_: *mut LeanObject,
    mut v___y_1601_: *mut LeanObject,
    mut v___y_1602_: *mut LeanObject,
    mut v___y_1603_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1604_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_1602_);
    lean_dec_ref(v___y_1601_);
    lean_dec(v___y_1600_);
    lean_dec_ref(v___y_1599_);
    lean_dec(v___y_1598_);
    lean_dec_ref(v___y_1597_);
    lean_dec(v___y_1596_);
    lean_dec_ref(v___y_1595_);
    return v_res_1604_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1()
-> *mut LeanObject {
    let mut v___x_1614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut LeanObject = core::ptr::null_mut();
    v___x_1614_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_1615_ = l_Lean_Elab_Tactic_evalCalc___closed__2;
    v___x_1616_ = l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__3;
    v___x_1617_ = lean_alloc_closure(
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
    mut v_a_1619_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1620_: *mut LeanObject = core::ptr::null_mut();
    v_res_1620_ = l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1();
    return v_res_1620_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_docString__3()
-> *mut LeanObject {
    let mut v___x_1623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut LeanObject = core::ptr::null_mut();
    v___x_1623_ = l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__3;
    v___x_1624_ = l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_docString__3___closed__0;
    v___x_1625_ = l_Lean_addBuiltinDocString(v___x_1623_, v___x_1624_);
    return v___x_1625_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_docString__3___boxed(
    mut v_a_1626_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1627_: *mut LeanObject = core::ptr::null_mut();
    v_res_1627_ = l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_docString__3();
    return v_res_1627_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5()
-> *mut LeanObject {
    let mut v___x_1654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut LeanObject = core::ptr::null_mut();
    v___x_1654_ = l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1___closed__3;
    v___x_1655_ = l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___closed__6;
    v___x_1656_ = l_Lean_addBuiltinDeclarationRanges(v___x_1654_, v___x_1655_);
    return v___x_1656_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5___boxed(
    mut v_a_1657_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1658_: *mut LeanObject = core::ptr::null_mut();
    v_res_1658_ = l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5();
    return v_res_1658_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Calc(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Calc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_ElabTerm(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_docString__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Calc_0__Lean_Elab_Tactic_evalCalc___regBuiltin_Lean_Elab_Tactic_evalCalc_declRange__5();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Calc(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Calc(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Calc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_ElabTerm(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Calc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Calc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Calc(builtin);
}
