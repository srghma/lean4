// Lean compiler output
// Module: Lean.Elab.Calc
// Imports: Lean.Elab.App
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_str___override, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg,
    l_Lean_Syntax_getArgs, l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f,
    l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull, l_Lean_Syntax_node1, l_Lean_Syntax_node2,
    l_Lean_Syntax_node3, l_Lean_Syntax_node5, l_Lean_addMacroScope, l_Lean_replaceRef,
    l_String_toRawSubstring_x27,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_withFreshMacroScope___redArg, l_Lean_mkArrow, l_Lean_useDiagnosticMsg,
};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::DocString::Extension::l_Lean_addBuiltinDocString;
use crate::r#gen::Lean::Elab::App::{initialize_Lean_Elab_App, runtime_initialize_Lean_Elab_App};
use crate::r#gen::Lean::Elab::Exception::{
    l_Lean_Elab_abortTermExceptionId, l_Lean_Elab_unsupportedSyntaxExceptionId,
};
use crate::r#gen::Lean::Elab::SyntheticMVars::l_Lean_Elab_Term_synthesizeSyntheticMVarsUsingDefault;
use crate::r#gen::Lean::Elab::Term::TermElabM::{
    l_Lean_Elab_Term_elabTermEnsuringType___boxed, l_Lean_Elab_Term_elabType,
    l_Lean_Elab_Term_ensureHasTypeWithErrorMsgs, l_Lean_Elab_Term_exprToSyntax,
    l_Lean_Elab_Term_termElabAttribute, l_Lean_Elab_Term_throwTypeMismatchError___redArg,
};
use crate::r#gen::Lean::Elab::Util::{l_Lean_Elab_getBetterRef, l_Lean_Elab_pp_macroStack};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appArg_x21, l_Lean_Expr_appFn_x21, l_Lean_Expr_getAppNumArgs, l_Lean_Expr_hasMVar,
    l_Lean_Expr_headBeta, l_Lean_instInhabitedExpr, l_Lean_mkAppN, l_Lean_mkConst, l_Lean_mkSort,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag, l_Lean_MessageData_ofExpr,
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofSyntax, l_Lean_MessageLog_add,
    l_Lean_indentD, l_Lean_indentExpr, l_Lean_instBEqMessageSeverity_beq,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp,
    l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, l_Lean_Meta_isExprDefEqGuarded,
    l_Lean_Meta_mkFreshExprMVar, l_Lean_Meta_mkFreshLevelMVar,
};
use crate::r#gen::Lean::Meta::Check::l_Lean_Meta_addPPExplicitToExposeDiff;
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_getLevel;
use crate::r#gen::Lean::Meta::SynthInstance::l_Lean_Meta_trySynthInstance;
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::ffi::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset,
};
use crate::ffi::{lean_usize_add, lean_usize_dec_lt};
use crate::ffi::{
    lean_array_get_borrowed, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed,
    lean_string_dec_eq,
};
use crate::ffi::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::ffi::{lean_infer_type, lean_whnf};
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 114, 101, 108, 97, 116, 105, 111, 110,
        32, 116, 121, 112, 101, 0,
    ],
};
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_Elab_Term_mkCalcTrans_spec__1___closed__0_value:
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
    m_fun: l_Lean_Meta_instInhabitedMetaM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_Elab_Term_mkCalcTrans_spec__1___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_panic___at___00Lean_Elab_Term_mkCalcTrans_spec__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_mkCalcTrans___closed__0_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [84, 114, 97, 110, 115, 0],
    };
static mut l_Lean_Elab_Term_mkCalcTrans___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcTrans___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_mkCalcTrans___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcTrans___closed__0_value)
                as *mut crate::leanh::LeanObject,
            9315039795129837137 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_mkCalcTrans___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcTrans___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_mkCalcTrans___closed__2_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [116, 114, 97, 110, 115, 0],
    };
static mut l_Lean_Elab_Term_mkCalcTrans___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcTrans___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Term_mkCalcTrans___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcTrans___closed__0_value)
                as *mut crate::leanh::LeanObject,
            9315039795129837137 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Term_mkCalcTrans___closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcTrans___closed__3_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcTrans___closed__2_value)
                as *mut crate::leanh::LeanObject,
            1217078205006953987 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_mkCalcTrans___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcTrans___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_mkCalcTrans___closed__4_value: crate::leanh::LeanStringObject<51> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 51,
        m_capacity: 51,
        m_length: 50,
        m_data: [
            105, 110, 118, 97, 108, 105, 100, 32, 39, 99, 97, 108, 99, 39, 32, 115, 116, 101, 112,
            44, 32, 115, 116, 101, 112, 32, 114, 101, 115, 117, 108, 116, 32, 105, 115, 32, 110,
            111, 116, 32, 97, 32, 114, 101, 108, 97, 116, 105, 111, 110, 0,
        ],
    };
static mut l_Lean_Elab_Term_mkCalcTrans___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcTrans___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Term_mkCalcTrans___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Term_mkCalcTrans___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Term_mkCalcTrans___closed__6_value: crate::leanh::LeanStringObject<59> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 59,
        m_capacity: 59,
        m_length: 58,
        m_data: [
            105, 110, 118, 97, 108, 105, 100, 32, 39, 99, 97, 108, 99, 39, 32, 115, 116, 101, 112,
            44, 32, 102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 115, 121, 110, 116, 104, 101,
            115, 105, 122, 101, 32, 96, 84, 114, 97, 110, 115, 96, 32, 105, 110, 115, 116, 97, 110,
            99, 101, 0,
        ],
    };
static mut l_Lean_Elab_Term_mkCalcTrans___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcTrans___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Term_mkCalcTrans___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Term_mkCalcTrans___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Term_mkCalcTrans___closed__8_value: crate::leanh::LeanStringObject<15> =
    crate::leanh::LeanStringObject {
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
            76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 67, 97, 108, 99, 0,
        ],
    };
static mut l_Lean_Elab_Term_mkCalcTrans___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcTrans___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_mkCalcTrans___closed__9_value: crate::leanh::LeanStringObject<27> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 27,
        m_capacity: 27,
        m_length: 26,
        m_data: [
            76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 84, 101, 114, 109, 46, 109, 107, 67, 97,
            108, 99, 84, 114, 97, 110, 115, 0,
        ],
    };
static mut l_Lean_Elab_Term_mkCalcTrans___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcTrans___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_mkCalcTrans___closed__10_value: crate::leanh::LeanStringObject<34> =
    crate::leanh::LeanStringObject {
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
            117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97,
            115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0,
        ],
    };
static mut l_Lean_Elab_Term_mkCalcTrans___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcTrans___closed__10_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Term_mkCalcTrans___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Term_mkCalcTrans___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Term_mkCalcTrans___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Term_mkCalcTrans___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__3_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 111, 108, 101, 0]};
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__4_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [116, 121, 112, 101, 65, 115, 99, 114, 105, 112, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__4_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__5_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__5_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__5_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__5_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__4_value) as *mut crate::leanh::LeanObject,5346268661279150583 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__6_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0]};
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__6_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__7_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__7_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__7_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__7_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__7_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__6_value) as *mut crate::leanh::LeanObject,7306243862518720553 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__7_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__8_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__8_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__9_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0]};
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__9_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__10_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__9_value) as *mut crate::leanh::LeanObject,9871775667037945883 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__11_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__11_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__12_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__12: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__16_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__16_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__17_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__17_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__17_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__16_value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__18_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__17_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__18_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__19_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__18_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__19_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__13_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__13_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__14_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__14_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__14_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__13_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__14_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__14_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__2_value) as *mut crate::leanh::LeanObject,7892421401833366012 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__15_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__14_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__20_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__15_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__19_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__20_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__21_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [58, 0]};
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__21: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__21_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__22_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__22: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__22_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__23_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__22_value) as *mut crate::leanh::LeanObject,9855511589286918680 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__23: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__23_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__24_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__24: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__24_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_instInhabitedCalcStepView_default___closed__0_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Term_instInhabitedCalcStepView_default___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_instInhabitedCalcStepView_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_Term_instInhabitedCalcStepView_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_instInhabitedCalcStepView_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_Term_instInhabitedCalcStepView: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_instInhabitedCalcStepView_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Term_mkCalcFirstStepView___closed__0_value: crate::leanh::LeanStringObject<
    14,
> = crate::leanh::LeanStringObject {
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
        99, 97, 108, 99, 70, 105, 114, 115, 116, 83, 116, 101, 112, 0,
    ],
};
static mut l_Lean_Elab_Term_mkCalcFirstStepView___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcFirstStepView___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Term_mkCalcFirstStepView___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Term_mkCalcFirstStepView___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcFirstStepView___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcFirstStepView___closed__0_value)
                as *mut crate::leanh::LeanObject,
            7592674497018613504 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_mkCalcFirstStepView___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcFirstStepView___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_mkCalcFirstStepView___closed__2_value: crate::leanh::LeanStringObject<
    8,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [116, 101, 114, 109, 95, 61, 95, 0],
};
static mut l_Lean_Elab_Term_mkCalcFirstStepView___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcFirstStepView___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_mkCalcFirstStepView___closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcFirstStepView___closed__2_value)
                as *mut crate::leanh::LeanObject,
            5677895497334651815 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_mkCalcFirstStepView___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcFirstStepView___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_mkCalcFirstStepView___closed__4_value: crate::leanh::LeanStringObject<
    2,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [61, 0],
};
static mut l_Lean_Elab_Term_mkCalcFirstStepView___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcFirstStepView___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Term_mkCalcFirstStepView___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Term_mkCalcFirstStepView___closed__5_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcFirstStepView___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Term_mkCalcFirstStepView___closed__5_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcFirstStepView___closed__5_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Term_mkCalcFirstStepView___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcFirstStepView___closed__5_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__3_value) as *mut crate::leanh::LeanObject,3984140175429830279 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_Term_mkCalcFirstStepView___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcFirstStepView___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_mkCalcFirstStepView___closed__6_value: crate::leanh::LeanStringObject<
    2,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [95, 0],
};
static mut l_Lean_Elab_Term_mkCalcFirstStepView___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcFirstStepView___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_mkCalcFirstStepView___closed__7_value: crate::leanh::LeanStringObject<
    4,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [114, 102, 108, 0],
};
static mut l_Lean_Elab_Term_mkCalcFirstStepView___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcFirstStepView___closed__7_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Term_mkCalcFirstStepView___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Term_mkCalcFirstStepView___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Term_mkCalcFirstStepView___closed__9_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcFirstStepView___closed__7_value)
                as *mut crate::leanh::LeanObject,
            17342663138809293389 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_mkCalcFirstStepView___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcFirstStepView___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_mkCalcFirstStepView___closed__10_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcFirstStepView___closed__9_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Term_mkCalcFirstStepView___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcFirstStepView___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_mkCalcFirstStepView___closed__11_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcFirstStepView___closed__10_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Term_mkCalcFirstStepView___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcFirstStepView___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg___closed__0_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [99, 97, 108, 99, 83, 116, 101, 112, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject,12991710356565001059 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_mkCalcStepViews___closed__0_value: crate::leanh::LeanStringObject<10> =
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
static mut l_Lean_Elab_Term_mkCalcStepViews___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcStepViews___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Term_mkCalcStepViews___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Term_mkCalcStepViews___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcStepViews___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcStepViews___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11669652153185471091 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_mkCalcStepViews___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcStepViews___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_panic___at___00Lean_Elab_Term_elabCalcSteps_spec__2___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_panic___at___00Lean_Elab_Term_elabCalcSteps_spec__2___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__1_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__2_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___closed__0_value: crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__0_value: crate::leanh::LeanStringObject<39> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 39, m_capacity: 39, m_length: 38, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 39, 99, 97, 108, 99, 39, 32, 115, 116, 101, 112, 44, 32, 108, 101, 102, 116, 45, 104, 97, 110, 100, 32, 115, 105, 100, 101, 32, 105, 115, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__2_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [32, 58, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__4_value: crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [10, 98, 117, 116, 32, 112, 114, 101, 118, 105, 111, 117, 115, 32, 114, 105, 103, 104, 116, 45, 104, 97, 110, 100, 32, 115, 105, 100, 101, 32, 105, 115, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__6_value: crate::leanh::LeanStringObject<39> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 39, m_capacity: 39, m_length: 38, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 39, 99, 97, 108, 99, 39, 32, 115, 116, 101, 112, 44, 32, 114, 101, 108, 97, 116, 105, 111, 110, 32, 101, 120, 112, 101, 99, 116, 101, 100, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Term_elabCalcSteps___closed__0_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_elabCalcSteps___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_elabCalcSteps___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_elabCalcSteps___closed__1_value: crate::leanh::LeanStringObject<26> =
    crate::leanh::LeanStringObject {
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
            73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 79, 112, 116, 105, 111, 110, 46, 66, 97,
            115, 105, 99, 65, 117, 120, 0,
        ],
    };
static mut l_Lean_Elab_Term_elabCalcSteps___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_elabCalcSteps___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_elabCalcSteps___closed__2_value: crate::leanh::LeanStringObject<12> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [79, 112, 116, 105, 111, 110, 46, 103, 101, 116, 33, 0],
    };
static mut l_Lean_Elab_Term_elabCalcSteps___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_elabCalcSteps___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_elabCalcSteps___closed__3_value: crate::leanh::LeanStringObject<14> =
    crate::leanh::LeanStringObject {
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
            118, 97, 108, 117, 101, 32, 105, 115, 32, 110, 111, 110, 101, 0,
        ],
    };
static mut l_Lean_Elab_Term_elabCalcSteps___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_elabCalcSteps___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Term_elabCalcSteps___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Term_elabCalcSteps___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__0_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__1_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__2_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__3_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__4_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__5_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__6_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_throwCalcFailure___redArg___closed__0_value:
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
        39, 99, 97, 108, 99, 39, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 0,
    ],
};
static mut l_Lean_Elab_Term_throwCalcFailure___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_throwCalcFailure___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_throwCalcFailure___redArg___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Term_throwCalcFailure___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Term_throwCalcFailure___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_throwCalcFailure___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Term_throwCalcFailure___redArg___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Term_throwCalcFailure___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Term_throwCalcFailure___redArg___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Term_throwCalcFailure___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Term_throwCalcFailure___redArg___closed__4_value:
    crate::leanh::LeanStringObject<40> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 40,
    m_capacity: 40,
    m_length: 39,
    m_data: [
        105, 110, 118, 97, 108, 105, 100, 32, 39, 99, 97, 108, 99, 39, 32, 115, 116, 101, 112, 44,
        32, 114, 105, 103, 104, 116, 45, 104, 97, 110, 100, 32, 115, 105, 100, 101, 32, 105, 115,
        0,
    ],
};
static mut l_Lean_Elab_Term_throwCalcFailure___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_throwCalcFailure___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Term_throwCalcFailure___redArg___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Term_throwCalcFailure___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Term_throwCalcFailure___redArg___closed__6_value:
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
        10, 98, 117, 116, 32, 105, 115, 32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 116, 111,
        32, 98, 101, 0,
    ],
};
static mut l_Lean_Elab_Term_throwCalcFailure___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_throwCalcFailure___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Term_throwCalcFailure___redArg___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Term_throwCalcFailure___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Term_throwCalcFailure___redArg___closed__8_value:
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
        76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 84, 101, 114, 109, 46, 116, 104, 114, 111, 119,
        67, 97, 108, 99, 70, 97, 105, 108, 117, 114, 101, 0,
    ],
};
static mut l_Lean_Elab_Term_throwCalcFailure___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_throwCalcFailure___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Term_throwCalcFailure___redArg___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Term_throwCalcFailure___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Term_elabCalc___closed__0_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Lean_Elab_Term_elabCalc___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_elabCalc___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Term_elabCalc___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Term_elabCalc___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_elabCalc___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_elabCalc___closed__0_value)
                as *mut crate::leanh::LeanObject,
            2427138008637189675 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_elabCalc___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_elabCalc___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__0_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [101, 108, 97, 98, 67, 97, 108, 99, 0]};
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__13_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__2_value) as *mut crate::leanh::LeanObject,7892421401833366012 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__0_value) as *mut crate::leanh::LeanObject,5870693989401443778 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_docString__3___closed__0_value: crate::leanh::LeanStringObject<46> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 46, m_capacity: 46, m_length: 45, m_data: [69, 108, 97, 98, 111, 114, 97, 116, 111, 114, 32, 102, 111, 114, 32, 116, 104, 101, 32, 96, 99, 97, 108, 99, 96, 32, 116, 101, 114, 109, 32, 109, 111, 100, 101, 32, 118, 97, 114, 105, 97, 110, 116, 46, 32, 0]};
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_docString__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_docString__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 116 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 121 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 15 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__0_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__1_value) as *mut crate::leanh::LeanObject,((( 15 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 116 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 116 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 12 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__3_value) as *mut crate::leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__4_value) as *mut crate::leanh::LeanObject,((( 12 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__6_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Elab_Term_getCalcRelation_x3f___redArg(
    mut v_e_2419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: u8 = 0;
    v___x_2421_ = l_Lean_Expr_getAppNumArgs(v_e_2419_);
    v___x_2422_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_2423_ = lean_nat_dec_lt(v___x_2421_, v___x_2422_);
    crate::leanh::lean_dec(v___x_2421_);
    if v___x_2423_ == 0 {
        let mut v___x_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2424_ = l_Lean_Expr_appFn_x21(v_e_2419_);
        v___x_2425_ = l_Lean_Expr_appFn_x21(v___x_2424_);
        v___x_2426_ = l_Lean_Expr_appArg_x21(v___x_2424_);
        crate::leanh::lean_dec_ref(v___x_2424_);
        v___x_2427_ = l_Lean_Expr_appArg_x21(v_e_2419_);
        v___x_2428_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2428_, 0, v___x_2426_);
        crate::leanh::lean_ctor_set(v___x_2428_, 1, v___x_2427_);
        v___x_2429_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2429_, 0, v___x_2425_);
        crate::leanh::lean_ctor_set(v___x_2429_, 1, v___x_2428_);
        v___x_2430_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2430_, 0, v___x_2429_);
        v___x_2431_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2431_, 0, v___x_2430_);
        return v___x_2431_;
    } else {
        let mut v___x_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2432_ = crate::leanh::lean_box(0);
        v___x_2433_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2433_, 0, v___x_2432_);
        return v___x_2433_;
    }
}
pub unsafe fn l_Lean_Elab_Term_getCalcRelation_x3f___redArg___boxed(
    mut v_e_2434_: *mut crate::leanh::LeanObject,
    mut v_a_2435_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2436_ = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(v_e_2434_);
    crate::leanh::lean_dec_ref(v_e_2434_);
    return v_res_2436_;
}
pub unsafe fn l_Lean_Elab_Term_getCalcRelation_x3f(
    mut v_e_2437_: *mut crate::leanh::LeanObject,
    mut v_a_2438_: *mut crate::leanh::LeanObject,
    mut v_a_2439_: *mut crate::leanh::LeanObject,
    mut v_a_2440_: *mut crate::leanh::LeanObject,
    mut v_a_2441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2443_ = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(v_e_2437_);
    return v___x_2443_;
}
pub unsafe fn l_Lean_Elab_Term_getCalcRelation_x3f___boxed(
    mut v_e_2444_: *mut crate::leanh::LeanObject,
    mut v_a_2445_: *mut crate::leanh::LeanObject,
    mut v_a_2446_: *mut crate::leanh::LeanObject,
    mut v_a_2447_: *mut crate::leanh::LeanObject,
    mut v_a_2448_: *mut crate::leanh::LeanObject,
    mut v_a_2449_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2450_ =
        l_Lean_Elab_Term_getCalcRelation_x3f(v_e_2444_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_);
    crate::leanh::lean_dec(v_a_2448_);
    crate::leanh::lean_dec_ref(v_a_2447_);
    crate::leanh::lean_dec(v_a_2446_);
    crate::leanh::lean_dec_ref(v_a_2445_);
    crate::leanh::lean_dec_ref(v_e_2444_);
    return v_res_2450_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1___redArg___lam__0(
    mut v_k_2451_: *mut crate::leanh::LeanObject,
    mut v_b_2452_: *mut crate::leanh::LeanObject,
    mut v_c_2453_: *mut crate::leanh::LeanObject,
    mut v___y_2454_: *mut crate::leanh::LeanObject,
    mut v___y_2455_: *mut crate::leanh::LeanObject,
    mut v___y_2456_: *mut crate::leanh::LeanObject,
    mut v___y_2457_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_2457_);
    crate::leanh::lean_inc_ref(v___y_2456_);
    crate::leanh::lean_inc(v___y_2455_);
    crate::leanh::lean_inc_ref(v___y_2454_);
    v___x_2459_ = crate::leanh::lean_apply_7(
        v_k_2451_,
        v_b_2452_,
        v_c_2453_,
        v___y_2454_,
        v___y_2455_,
        v___y_2456_,
        v___y_2457_,
        crate::leanh::lean_box(0),
    );
    return v___x_2459_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1___redArg___lam__0___boxed(
    mut v_k_2460_: *mut crate::leanh::LeanObject,
    mut v_b_2461_: *mut crate::leanh::LeanObject,
    mut v_c_2462_: *mut crate::leanh::LeanObject,
    mut v___y_2463_: *mut crate::leanh::LeanObject,
    mut v___y_2464_: *mut crate::leanh::LeanObject,
    mut v___y_2465_: *mut crate::leanh::LeanObject,
    mut v___y_2466_: *mut crate::leanh::LeanObject,
    mut v___y_2467_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2468_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1___redArg___lam__0(v_k_2460_, v_b_2461_, v_c_2462_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_);
    crate::leanh::lean_dec(v___y_2466_);
    crate::leanh::lean_dec_ref(v___y_2465_);
    crate::leanh::lean_dec(v___y_2464_);
    crate::leanh::lean_dec_ref(v___y_2463_);
    return v_res_2468_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1___redArg(
    mut v_type_2469_: *mut crate::leanh::LeanObject,
    mut v_k_2470_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_2471_: u8,
    mut v_whnfType_2472_: u8,
    mut v___y_2473_: *mut crate::leanh::LeanObject,
    mut v___y_2474_: *mut crate::leanh::LeanObject,
    mut v___y_2475_: *mut crate::leanh::LeanObject,
    mut v___y_2476_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2483_: u8 = 0;
    let mut v___x_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2487_: u8 = 0;
    let mut v_a_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2491_: u8 = 0;
    let mut v___x_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2495_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_2478_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                crate::leanh::lean_closure_set(v___f_2478_, 0, v_k_2470_);
                v___x_2479_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(
                    crate::leanh::lean_box(0),
                    v_type_2469_,
                    v___f_2478_,
                    v_cleanupAnnotations_2471_,
                    v_whnfType_2472_,
                    v___y_2473_,
                    v___y_2474_,
                    v___y_2475_,
                    v___y_2476_,
                );
                if crate::leanh::lean_obj_tag(v___x_2479_) == 0 {
                    v_a_2480_ = crate::leanh::lean_ctor_get(v___x_2479_, 0);
                    v_isSharedCheck_2487_ = (!crate::leanh::lean_is_exclusive(v___x_2479_)) as u8;
                    if v_isSharedCheck_2487_ == 0 {
                        v___x_2482_ = v___x_2479_;
                        v_isShared_2483_ = v_isSharedCheck_2487_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2480_);
                        crate::leanh::lean_dec(v___x_2479_);
                        v___x_2482_ = crate::leanh::lean_box(0);
                        v_isShared_2483_ = v_isSharedCheck_2487_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2488_ = crate::leanh::lean_ctor_get(v___x_2479_, 0);
                    v_isSharedCheck_2495_ = (!crate::leanh::lean_is_exclusive(v___x_2479_)) as u8;
                    if v_isSharedCheck_2495_ == 0 {
                        v___x_2490_ = v___x_2479_;
                        v_isShared_2491_ = v_isSharedCheck_2495_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2488_);
                        crate::leanh::lean_dec(v___x_2479_);
                        v___x_2490_ = crate::leanh::lean_box(0);
                        v_isShared_2491_ = v_isSharedCheck_2495_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2483_ == 0 {
                    v___x_2485_ = v___x_2482_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2486_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2486_, 0, v_a_2480_);
                    v___x_2485_ = v_reuseFailAlloc_2486_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2485_;
            }
            3 => {
                if v_isShared_2491_ == 0 {
                    v___x_2493_ = v___x_2490_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2494_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2494_, 0, v_a_2488_);
                    v___x_2493_ = v_reuseFailAlloc_2494_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2493_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1___redArg___boxed(
    mut v_type_2496_: *mut crate::leanh::LeanObject,
    mut v_k_2497_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_2498_: *mut crate::leanh::LeanObject,
    mut v_whnfType_2499_: *mut crate::leanh::LeanObject,
    mut v___y_2500_: *mut crate::leanh::LeanObject,
    mut v___y_2501_: *mut crate::leanh::LeanObject,
    mut v___y_2502_: *mut crate::leanh::LeanObject,
    mut v___y_2503_: *mut crate::leanh::LeanObject,
    mut v___y_2504_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_2505_: u8 = 0;
    let mut v_whnfType_boxed_2506_: u8 = 0;
    let mut v_res_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_2505_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_2498_) as u8);
    v_whnfType_boxed_2506_ = (crate::leanh::lean_unbox(v_whnfType_2499_) as u8);
    v_res_2507_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1___redArg(v_type_2496_, v_k_2497_, v_cleanupAnnotations_boxed_2505_, v_whnfType_boxed_2506_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_);
    crate::leanh::lean_dec(v___y_2503_);
    crate::leanh::lean_dec_ref(v___y_2502_);
    crate::leanh::lean_dec(v___y_2501_);
    crate::leanh::lean_dec_ref(v___y_2500_);
    return v_res_2507_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1(
    mut v_00_u03b1_2508_: *mut crate::leanh::LeanObject,
    mut v_type_2509_: *mut crate::leanh::LeanObject,
    mut v_k_2510_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_2511_: u8,
    mut v_whnfType_2512_: u8,
    mut v___y_2513_: *mut crate::leanh::LeanObject,
    mut v___y_2514_: *mut crate::leanh::LeanObject,
    mut v___y_2515_: *mut crate::leanh::LeanObject,
    mut v___y_2516_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2518_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1___redArg(v_type_2509_, v_k_2510_, v_cleanupAnnotations_2511_, v_whnfType_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
    return v___x_2518_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1___boxed(
    mut v_00_u03b1_2519_: *mut crate::leanh::LeanObject,
    mut v_type_2520_: *mut crate::leanh::LeanObject,
    mut v_k_2521_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_2522_: *mut crate::leanh::LeanObject,
    mut v_whnfType_2523_: *mut crate::leanh::LeanObject,
    mut v___y_2524_: *mut crate::leanh::LeanObject,
    mut v___y_2525_: *mut crate::leanh::LeanObject,
    mut v___y_2526_: *mut crate::leanh::LeanObject,
    mut v___y_2527_: *mut crate::leanh::LeanObject,
    mut v___y_2528_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_2529_: u8 = 0;
    let mut v_whnfType_boxed_2530_: u8 = 0;
    let mut v_res_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_2529_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_2522_) as u8);
    v_whnfType_boxed_2530_ = (crate::leanh::lean_unbox(v_whnfType_2523_) as u8);
    v_res_2531_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1(v_00_u03b1_2519_, v_type_2520_, v_k_2521_, v_cleanupAnnotations_boxed_2529_, v_whnfType_boxed_2530_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_);
    crate::leanh::lean_dec(v___y_2527_);
    crate::leanh::lean_dec_ref(v___y_2526_);
    crate::leanh::lean_dec(v___y_2525_);
    crate::leanh::lean_dec_ref(v___y_2524_);
    return v_res_2531_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0_spec__0(
    mut v_msgData_2532_: *mut crate::leanh::LeanObject,
    mut v___y_2533_: *mut crate::leanh::LeanObject,
    mut v___y_2534_: *mut crate::leanh::LeanObject,
    mut v___y_2535_: *mut crate::leanh::LeanObject,
    mut v___y_2536_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2538_ = lean_st_ref_get(v___y_2536_);
    v_env_2539_ = crate::leanh::lean_ctor_get(v___x_2538_, 0);
    crate::leanh::lean_inc_ref(v_env_2539_);
    crate::leanh::lean_dec(v___x_2538_);
    v___x_2540_ = lean_st_ref_get(v___y_2534_);
    v_mctx_2541_ = crate::leanh::lean_ctor_get(v___x_2540_, 0);
    crate::leanh::lean_inc_ref(v_mctx_2541_);
    crate::leanh::lean_dec(v___x_2540_);
    v_lctx_2542_ = crate::leanh::lean_ctor_get(v___y_2533_, 2);
    v_options_2543_ = crate::leanh::lean_ctor_get(v___y_2535_, 2);
    crate::leanh::lean_inc_ref(v_options_2543_);
    crate::leanh::lean_inc_ref(v_lctx_2542_);
    v___x_2544_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2544_, 0, v_env_2539_);
    crate::leanh::lean_ctor_set(v___x_2544_, 1, v_mctx_2541_);
    crate::leanh::lean_ctor_set(v___x_2544_, 2, v_lctx_2542_);
    crate::leanh::lean_ctor_set(v___x_2544_, 3, v_options_2543_);
    v___x_2545_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2545_, 0, v___x_2544_);
    crate::leanh::lean_ctor_set(v___x_2545_, 1, v_msgData_2532_);
    v___x_2546_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2546_, 0, v___x_2545_);
    return v___x_2546_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0_spec__0___boxed(
    mut v_msgData_2547_: *mut crate::leanh::LeanObject,
    mut v___y_2548_: *mut crate::leanh::LeanObject,
    mut v___y_2549_: *mut crate::leanh::LeanObject,
    mut v___y_2550_: *mut crate::leanh::LeanObject,
    mut v___y_2551_: *mut crate::leanh::LeanObject,
    mut v___y_2552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2553_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0_spec__0(v_msgData_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_);
    crate::leanh::lean_dec(v___y_2551_);
    crate::leanh::lean_dec_ref(v___y_2550_);
    crate::leanh::lean_dec(v___y_2549_);
    crate::leanh::lean_dec_ref(v___y_2548_);
    return v_res_2553_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0___redArg(
    mut v_msg_2554_: *mut crate::leanh::LeanObject,
    mut v___y_2555_: *mut crate::leanh::LeanObject,
    mut v___y_2556_: *mut crate::leanh::LeanObject,
    mut v___y_2557_: *mut crate::leanh::LeanObject,
    mut v___y_2558_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2565_: u8 = 0;
    let mut v___x_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2570_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2560_ = crate::leanh::lean_ctor_get(v___y_2557_, 5);
                v___x_2561_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0_spec__0(v_msg_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_);
                v_a_2562_ = crate::leanh::lean_ctor_get(v___x_2561_, 0);
                v_isSharedCheck_2570_ = (!crate::leanh::lean_is_exclusive(v___x_2561_)) as u8;
                if v_isSharedCheck_2570_ == 0 {
                    v___x_2564_ = v___x_2561_;
                    v_isShared_2565_ = v_isSharedCheck_2570_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2562_);
                    crate::leanh::lean_dec(v___x_2561_);
                    v___x_2564_ = crate::leanh::lean_box(0);
                    v_isShared_2565_ = v_isSharedCheck_2570_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_2560_);
                v___x_2566_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2566_, 0, v_ref_2560_);
                crate::leanh::lean_ctor_set(v___x_2566_, 1, v_a_2562_);
                if v_isShared_2565_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2564_, 1);
                    crate::leanh::lean_ctor_set(v___x_2564_, 0, v___x_2566_);
                    v___x_2568_ = v___x_2564_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2569_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2569_, 0, v___x_2566_);
                    v___x_2568_ = v_reuseFailAlloc_2569_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2568_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0___redArg___boxed(
    mut v_msg_2571_: *mut crate::leanh::LeanObject,
    mut v___y_2572_: *mut crate::leanh::LeanObject,
    mut v___y_2573_: *mut crate::leanh::LeanObject,
    mut v___y_2574_: *mut crate::leanh::LeanObject,
    mut v___y_2575_: *mut crate::leanh::LeanObject,
    mut v___y_2576_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2577_ = l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0___redArg(v_msg_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
    crate::leanh::lean_dec(v___y_2575_);
    crate::leanh::lean_dec_ref(v___y_2574_);
    crate::leanh::lean_dec(v___y_2573_);
    crate::leanh::lean_dec_ref(v___y_2572_);
    return v_res_2577_;
}
pub unsafe fn _init_l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2579_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0___closed__0;
    v___x_2580_ = l_Lean_stringToMessageData(v___x_2579_);
    return v___x_2580_;
}
pub unsafe fn l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0(
    mut v_a_2581_: *mut crate::leanh::LeanObject,
    mut v_x_2582_: *mut crate::leanh::LeanObject,
    mut v_sort_2583_: *mut crate::leanh::LeanObject,
    mut v___y_2584_: *mut crate::leanh::LeanObject,
    mut v___y_2585_: *mut crate::leanh::LeanObject,
    mut v___y_2586_: *mut crate::leanh::LeanObject,
    mut v___y_2587_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2593_: u8 = 0;
    let mut v_u_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2602_: u8 = 0;
    let mut v_a_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2606_: u8 = 0;
    let mut v___x_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2610_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_2587_);
                crate::leanh::lean_inc_ref(v___y_2586_);
                crate::leanh::lean_inc(v___y_2585_);
                crate::leanh::lean_inc_ref(v___y_2584_);
                v___x_2589_ = lean_whnf(
                    v_sort_2583_,
                    v___y_2584_,
                    v___y_2585_,
                    v___y_2586_,
                    v___y_2587_,
                );
                if crate::leanh::lean_obj_tag(v___x_2589_) == 0 {
                    v_a_2590_ = crate::leanh::lean_ctor_get(v___x_2589_, 0);
                    v_isSharedCheck_2602_ = (!crate::leanh::lean_is_exclusive(v___x_2589_)) as u8;
                    if v_isSharedCheck_2602_ == 0 {
                        v___x_2592_ = v___x_2589_;
                        v_isShared_2593_ = v_isSharedCheck_2602_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2590_);
                        crate::leanh::lean_dec(v___x_2589_);
                        v___x_2592_ = crate::leanh::lean_box(0);
                        v_isShared_2593_ = v_isSharedCheck_2602_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_a_2581_);
                    v_a_2603_ = crate::leanh::lean_ctor_get(v___x_2589_, 0);
                    v_isSharedCheck_2610_ = (!crate::leanh::lean_is_exclusive(v___x_2589_)) as u8;
                    if v_isSharedCheck_2610_ == 0 {
                        v___x_2605_ = v___x_2589_;
                        v_isShared_2606_ = v_isSharedCheck_2610_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2603_);
                        crate::leanh::lean_dec(v___x_2589_);
                        v___x_2605_ = crate::leanh::lean_box(0);
                        v_isShared_2606_ = v_isSharedCheck_2610_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_2590_) == 3 {
                    crate::leanh::lean_dec_ref(v_a_2581_);
                    v_u_2594_ = crate::leanh::lean_ctor_get(v_a_2590_, 0);
                    crate::leanh::lean_inc(v_u_2594_);
                    crate::leanh::lean_dec_ref_known(v_a_2590_, 1);
                    if v_isShared_2593_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2592_, 0, v_u_2594_);
                        v___x_2596_ = v___x_2592_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2597_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2597_, 0, v_u_2594_);
                        v___x_2596_ = v_reuseFailAlloc_2597_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2592_);
                    crate::leanh::lean_dec(v_a_2590_);
                    v___x_2598_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0___closed__1_once), _init_l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0___closed__1);
                    v___x_2599_ = l_Lean_indentExpr(v_a_2581_);
                    v___x_2600_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2600_, 0, v___x_2598_);
                    crate::leanh::lean_ctor_set(v___x_2600_, 1, v___x_2599_);
                    v___x_2601_ = l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0___redArg(v___x_2600_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_);
                    return v___x_2601_;
                }
            }
            2 => {
                return v___x_2596_;
            }
            3 => {
                if v_isShared_2606_ == 0 {
                    v___x_2608_ = v___x_2605_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2609_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2609_, 0, v_a_2603_);
                    v___x_2608_ = v_reuseFailAlloc_2609_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2608_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0___boxed(
    mut v_a_2611_: *mut crate::leanh::LeanObject,
    mut v_x_2612_: *mut crate::leanh::LeanObject,
    mut v_sort_2613_: *mut crate::leanh::LeanObject,
    mut v___y_2614_: *mut crate::leanh::LeanObject,
    mut v___y_2615_: *mut crate::leanh::LeanObject,
    mut v___y_2616_: *mut crate::leanh::LeanObject,
    mut v___y_2617_: *mut crate::leanh::LeanObject,
    mut v___y_2618_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2619_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0(
        v_a_2611_,
        v_x_2612_,
        v_sort_2613_,
        v___y_2614_,
        v___y_2615_,
        v___y_2616_,
        v___y_2617_,
    );
    crate::leanh::lean_dec(v___y_2617_);
    crate::leanh::lean_dec_ref(v___y_2616_);
    crate::leanh::lean_dec(v___y_2615_);
    crate::leanh::lean_dec_ref(v___y_2614_);
    crate::leanh::lean_dec_ref(v_x_2612_);
    return v_res_2619_;
}
pub unsafe fn l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(
    mut v_r_2620_: *mut crate::leanh::LeanObject,
    mut v_a_2621_: *mut crate::leanh::LeanObject,
    mut v_a_2622_: *mut crate::leanh::LeanObject,
    mut v_a_2623_: *mut crate::leanh::LeanObject,
    mut v_a_2624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: u8 = 0;
    let mut v___x_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2634_: u8 = 0;
    let mut v___x_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2638_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_2624_);
                crate::leanh::lean_inc_ref(v_a_2623_);
                crate::leanh::lean_inc(v_a_2622_);
                crate::leanh::lean_inc_ref(v_a_2621_);
                v___x_2626_ =
                    lean_infer_type(v_r_2620_, v_a_2621_, v_a_2622_, v_a_2623_, v_a_2624_);
                if crate::leanh::lean_obj_tag(v___x_2626_) == 0 {
                    v_a_2627_ = crate::leanh::lean_ctor_get(v___x_2626_, 0);
                    crate::leanh::lean_inc_n(v_a_2627_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_2626_, 1);
                    v___f_2628_ = crate::leanh::lean_alloc_closure(
                        l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0___boxed
                            as *mut core::ffi::c_void,
                        8,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_2628_, 0, v_a_2627_);
                    v___x_2629_ = 0;
                    v___x_2630_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1___redArg(v_a_2627_, v___f_2628_, v___x_2629_, v___x_2629_, v_a_2621_, v_a_2622_, v_a_2623_, v_a_2624_);
                    return v___x_2630_;
                } else {
                    v_a_2631_ = crate::leanh::lean_ctor_get(v___x_2626_, 0);
                    v_isSharedCheck_2638_ = (!crate::leanh::lean_is_exclusive(v___x_2626_)) as u8;
                    if v_isSharedCheck_2638_ == 0 {
                        v___x_2633_ = v___x_2626_;
                        v_isShared_2634_ = v_isSharedCheck_2638_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2631_);
                        crate::leanh::lean_dec(v___x_2626_);
                        v___x_2633_ = crate::leanh::lean_box(0);
                        v_isShared_2634_ = v_isSharedCheck_2638_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2634_ == 0 {
                    v___x_2636_ = v___x_2633_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2637_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2637_, 0, v_a_2631_);
                    v___x_2636_ = v_reuseFailAlloc_2637_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2636_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___boxed(
    mut v_r_2639_: *mut crate::leanh::LeanObject,
    mut v_a_2640_: *mut crate::leanh::LeanObject,
    mut v_a_2641_: *mut crate::leanh::LeanObject,
    mut v_a_2642_: *mut crate::leanh::LeanObject,
    mut v_a_2643_: *mut crate::leanh::LeanObject,
    mut v_a_2644_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2645_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(
        v_r_2639_, v_a_2640_, v_a_2641_, v_a_2642_, v_a_2643_,
    );
    crate::leanh::lean_dec(v_a_2643_);
    crate::leanh::lean_dec_ref(v_a_2642_);
    crate::leanh::lean_dec(v_a_2641_);
    crate::leanh::lean_dec_ref(v_a_2640_);
    return v_res_2645_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0(
    mut v_00_u03b1_2646_: *mut crate::leanh::LeanObject,
    mut v_msg_2647_: *mut crate::leanh::LeanObject,
    mut v___y_2648_: *mut crate::leanh::LeanObject,
    mut v___y_2649_: *mut crate::leanh::LeanObject,
    mut v___y_2650_: *mut crate::leanh::LeanObject,
    mut v___y_2651_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2653_ = l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0___redArg(v_msg_2647_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_);
    return v___x_2653_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0___boxed(
    mut v_00_u03b1_2654_: *mut crate::leanh::LeanObject,
    mut v_msg_2655_: *mut crate::leanh::LeanObject,
    mut v___y_2656_: *mut crate::leanh::LeanObject,
    mut v___y_2657_: *mut crate::leanh::LeanObject,
    mut v___y_2658_: *mut crate::leanh::LeanObject,
    mut v___y_2659_: *mut crate::leanh::LeanObject,
    mut v___y_2660_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2661_ =
        l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0(
            v_00_u03b1_2654_,
            v_msg_2655_,
            v___y_2656_,
            v___y_2657_,
            v___y_2658_,
            v___y_2659_,
        );
    crate::leanh::lean_dec(v___y_2659_);
    crate::leanh::lean_dec_ref(v___y_2658_);
    crate::leanh::lean_dec(v___y_2657_);
    crate::leanh::lean_dec_ref(v___y_2656_);
    return v_res_2661_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0___redArg(
    mut v_e_2662_: *mut crate::leanh::LeanObject,
    mut v___y_2663_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2665_: u8 = 0;
    let mut v___x_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2679_: u8 = 0;
    let mut v___x_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2685_: u8 = 0;
    let mut v_unused_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2665_ = l_Lean_Expr_hasMVar(v_e_2662_);
                if v___x_2665_ == 0 {
                    v___x_2666_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2666_, 0, v_e_2662_);
                    return v___x_2666_;
                } else {
                    v___x_2667_ = lean_st_ref_get(v___y_2663_);
                    v_mctx_2668_ = crate::leanh::lean_ctor_get(v___x_2667_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_2668_);
                    crate::leanh::lean_dec(v___x_2667_);
                    v___x_2669_ = l_Lean_instantiateMVarsCore(v_mctx_2668_, v_e_2662_);
                    v_fst_2670_ = crate::leanh::lean_ctor_get(v___x_2669_, 0);
                    crate::leanh::lean_inc(v_fst_2670_);
                    v_snd_2671_ = crate::leanh::lean_ctor_get(v___x_2669_, 1);
                    crate::leanh::lean_inc(v_snd_2671_);
                    crate::leanh::lean_dec_ref(v___x_2669_);
                    v___x_2672_ = lean_st_ref_take(v___y_2663_);
                    v_cache_2673_ = crate::leanh::lean_ctor_get(v___x_2672_, 1);
                    v_zetaDeltaFVarIds_2674_ = crate::leanh::lean_ctor_get(v___x_2672_, 2);
                    v_postponed_2675_ = crate::leanh::lean_ctor_get(v___x_2672_, 3);
                    v_diag_2676_ = crate::leanh::lean_ctor_get(v___x_2672_, 4);
                    v_isSharedCheck_2685_ = (!crate::leanh::lean_is_exclusive(v___x_2672_)) as u8;
                    if v_isSharedCheck_2685_ == 0 {
                        v_unused_2686_ = crate::leanh::lean_ctor_get(v___x_2672_, 0);
                        crate::leanh::lean_dec(v_unused_2686_);
                        v___x_2678_ = v___x_2672_;
                        v_isShared_2679_ = v_isSharedCheck_2685_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_2676_);
                        crate::leanh::lean_inc(v_postponed_2675_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_2674_);
                        crate::leanh::lean_inc(v_cache_2673_);
                        crate::leanh::lean_dec(v___x_2672_);
                        v___x_2678_ = crate::leanh::lean_box(0);
                        v_isShared_2679_ = v_isSharedCheck_2685_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2679_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2678_, 0, v_snd_2671_);
                    v___x_2681_ = v___x_2678_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2684_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2684_, 0, v_snd_2671_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2684_, 1, v_cache_2673_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2684_,
                        2,
                        v_zetaDeltaFVarIds_2674_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2684_, 3, v_postponed_2675_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2684_, 4, v_diag_2676_);
                    v___x_2681_ = v_reuseFailAlloc_2684_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2682_ = lean_st_ref_set(v___y_2663_, v___x_2681_);
                v___x_2683_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2683_, 0, v_fst_2670_);
                return v___x_2683_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0___redArg___boxed(
    mut v_e_2687_: *mut crate::leanh::LeanObject,
    mut v___y_2688_: *mut crate::leanh::LeanObject,
    mut v___y_2689_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2690_ = l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0___redArg(
        v_e_2687_,
        v___y_2688_,
    );
    crate::leanh::lean_dec(v___y_2688_);
    return v_res_2690_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0(
    mut v_e_2691_: *mut crate::leanh::LeanObject,
    mut v___y_2692_: *mut crate::leanh::LeanObject,
    mut v___y_2693_: *mut crate::leanh::LeanObject,
    mut v___y_2694_: *mut crate::leanh::LeanObject,
    mut v___y_2695_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2697_ = l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0___redArg(
        v_e_2691_,
        v___y_2693_,
    );
    return v___x_2697_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0___boxed(
    mut v_e_2698_: *mut crate::leanh::LeanObject,
    mut v___y_2699_: *mut crate::leanh::LeanObject,
    mut v___y_2700_: *mut crate::leanh::LeanObject,
    mut v___y_2701_: *mut crate::leanh::LeanObject,
    mut v___y_2702_: *mut crate::leanh::LeanObject,
    mut v___y_2703_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2704_ = l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0(
        v_e_2698_,
        v___y_2699_,
        v___y_2700_,
        v___y_2701_,
        v___y_2702_,
    );
    crate::leanh::lean_dec(v___y_2702_);
    crate::leanh::lean_dec_ref(v___y_2701_);
    crate::leanh::lean_dec(v___y_2700_);
    crate::leanh::lean_dec_ref(v___y_2699_);
    return v_res_2704_;
}
pub unsafe fn l_panic___at___00Lean_Elab_Term_mkCalcTrans_spec__1(
    mut v_msg_2706_: *mut crate::leanh::LeanObject,
    mut v___y_2707_: *mut crate::leanh::LeanObject,
    mut v___y_2708_: *mut crate::leanh::LeanObject,
    mut v___y_2709_: *mut crate::leanh::LeanObject,
    mut v___y_2710_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7424__overap_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2712_ = l_panic___at___00Lean_Elab_Term_mkCalcTrans_spec__1___closed__0;
    v___x_7424__overap_2713_ = lean_panic_fn_borrowed(v___f_2712_, v_msg_2706_);
    crate::leanh::lean_inc(v___y_2710_);
    crate::leanh::lean_inc_ref(v___y_2709_);
    crate::leanh::lean_inc(v___y_2708_);
    crate::leanh::lean_inc_ref(v___y_2707_);
    v___x_2714_ = crate::leanh::lean_apply_5(
        v___x_7424__overap_2713_,
        v___y_2707_,
        v___y_2708_,
        v___y_2709_,
        v___y_2710_,
        crate::leanh::lean_box(0),
    );
    return v___x_2714_;
}
pub unsafe fn l_panic___at___00Lean_Elab_Term_mkCalcTrans_spec__1___boxed(
    mut v_msg_2715_: *mut crate::leanh::LeanObject,
    mut v___y_2716_: *mut crate::leanh::LeanObject,
    mut v___y_2717_: *mut crate::leanh::LeanObject,
    mut v___y_2718_: *mut crate::leanh::LeanObject,
    mut v___y_2719_: *mut crate::leanh::LeanObject,
    mut v___y_2720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2721_ = l_panic___at___00Lean_Elab_Term_mkCalcTrans_spec__1(
        v_msg_2715_,
        v___y_2716_,
        v___y_2717_,
        v___y_2718_,
        v___y_2719_,
    );
    crate::leanh::lean_dec(v___y_2719_);
    crate::leanh::lean_dec_ref(v___y_2718_);
    crate::leanh::lean_dec(v___y_2717_);
    crate::leanh::lean_dec_ref(v___y_2716_);
    return v_res_2721_;
}
pub unsafe fn _init_l_Lean_Elab_Term_mkCalcTrans___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2730_ = l_Lean_Elab_Term_mkCalcTrans___closed__4;
    v___x_2731_ = l_Lean_stringToMessageData(v___x_2730_);
    return v___x_2731_;
}
pub unsafe fn _init_l_Lean_Elab_Term_mkCalcTrans___closed__7() -> *mut crate::leanh::LeanObject {
    let mut v___x_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2733_ = l_Lean_Elab_Term_mkCalcTrans___closed__6;
    v___x_2734_ = l_Lean_stringToMessageData(v___x_2733_);
    return v___x_2734_;
}
pub unsafe fn _init_l_Lean_Elab_Term_mkCalcTrans___closed__11() -> *mut crate::leanh::LeanObject {
    let mut v___x_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2738_ = l_Lean_Elab_Term_mkCalcTrans___closed__10;
    v___x_2739_ = crate::leanh::lean_unsigned_to_nat(72);
    v___x_2740_ = crate::leanh::lean_unsigned_to_nat(35);
    v___x_2741_ = l_Lean_Elab_Term_mkCalcTrans___closed__9;
    v___x_2742_ = l_Lean_Elab_Term_mkCalcTrans___closed__8;
    v___x_2743_ = l_mkPanicMessageWithDecl(
        v___x_2742_,
        v___x_2741_,
        v___x_2740_,
        v___x_2739_,
        v___x_2738_,
    );
    return v___x_2743_;
}
pub unsafe fn _init_l_Lean_Elab_Term_mkCalcTrans___closed__12() -> *mut crate::leanh::LeanObject {
    let mut v___x_2744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2744_ = l_Lean_Elab_Term_mkCalcTrans___closed__10;
    v___x_2745_ = crate::leanh::lean_unsigned_to_nat(53);
    v___x_2746_ = crate::leanh::lean_unsigned_to_nat(34);
    v___x_2747_ = l_Lean_Elab_Term_mkCalcTrans___closed__9;
    v___x_2748_ = l_Lean_Elab_Term_mkCalcTrans___closed__8;
    v___x_2749_ = l_mkPanicMessageWithDecl(
        v___x_2748_,
        v___x_2747_,
        v___x_2746_,
        v___x_2745_,
        v___x_2744_,
    );
    return v___x_2749_;
}
pub unsafe fn l_Lean_Elab_Term_mkCalcTrans(
    mut v_result_2750_: *mut crate::leanh::LeanObject,
    mut v_resultType_2751_: *mut crate::leanh::LeanObject,
    mut v_step_2752_: *mut crate::leanh::LeanObject,
    mut v_stepType_2753_: *mut crate::leanh::LeanObject,
    mut v_a_2754_: *mut crate::leanh::LeanObject,
    mut v_a_2755_: *mut crate::leanh::LeanObject,
    mut v_a_2756_: *mut crate::leanh::LeanObject,
    mut v_a_2757_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2766_: u8 = 0;
    let mut v_fst_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2771_: u8 = 0;
    let mut v___x_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2779_: u8 = 0;
    let mut v_snd_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2784_: u8 = 0;
    let mut v_snd_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2788_: u8 = 0;
    let mut v___x_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: u8 = 0;
    let mut v___x_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2866_: u8 = 0;
    let mut v___x_2867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2884_: u8 = 0;
    let mut v___x_2886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2888_: u8 = 0;
    let mut v_isSharedCheck_2889_: u8 = 0;
    let mut v_a_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2893_: u8 = 0;
    let mut v___x_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2897_: u8 = 0;
    let mut v___x_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2907_: u8 = 0;
    let mut v___x_2909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2911_: u8 = 0;
    let mut v_reuseFailAlloc_2912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2918_: u8 = 0;
    let mut v___x_2920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2922_: u8 = 0;
    let mut v_reuseFailAlloc_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2927_: u8 = 0;
    let mut v___x_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2931_: u8 = 0;
    let mut v_a_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2935_: u8 = 0;
    let mut v___x_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2939_: u8 = 0;
    let mut v_a_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2943_: u8 = 0;
    let mut v___x_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2947_: u8 = 0;
    let mut v_a_2948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2951_: u8 = 0;
    let mut v___x_2953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2955_: u8 = 0;
    let mut v_a_2956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2959_: u8 = 0;
    let mut v___x_2961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2963_: u8 = 0;
    let mut v_a_2964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2967_: u8 = 0;
    let mut v___x_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2971_: u8 = 0;
    let mut v_a_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2975_: u8 = 0;
    let mut v___x_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2979_: u8 = 0;
    let mut v_a_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2983_: u8 = 0;
    let mut v___x_2985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2987_: u8 = 0;
    let mut v_a_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2991_: u8 = 0;
    let mut v___x_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2995_: u8 = 0;
    let mut v_a_2996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2999_: u8 = 0;
    let mut v___x_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3003_: u8 = 0;
    let mut v_a_3004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3007_: u8 = 0;
    let mut v___x_3009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3011_: u8 = 0;
    let mut v_isSharedCheck_3012_: u8 = 0;
    let mut v_unused_3013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3014_: u8 = 0;
    let mut v_isSharedCheck_3015_: u8 = 0;
    let mut v___x_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3018_: u8 = 0;
    let mut v_isSharedCheck_3019_: u8 = 0;
    let mut v___x_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2759_ = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(v_resultType_2751_);
                v_a_2760_ = crate::leanh::lean_ctor_get(v___x_2759_, 0);
                crate::leanh::lean_inc(v_a_2760_);
                crate::leanh::lean_dec_ref(v___x_2759_);
                if crate::leanh::lean_obj_tag(v_a_2760_) == 1 {
                    v_val_2761_ = crate::leanh::lean_ctor_get(v_a_2760_, 0);
                    crate::leanh::lean_inc(v_val_2761_);
                    crate::leanh::lean_dec_ref_known(v_a_2760_, 1);
                    v_snd_2762_ = crate::leanh::lean_ctor_get(v_val_2761_, 1);
                    v_fst_2763_ = crate::leanh::lean_ctor_get(v_val_2761_, 0);
                    v_isSharedCheck_3019_ = (!crate::leanh::lean_is_exclusive(v_val_2761_)) as u8;
                    if v_isSharedCheck_3019_ == 0 {
                        v___x_2765_ = v_val_2761_;
                        v_isShared_2766_ = v_isSharedCheck_3019_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2762_);
                        crate::leanh::lean_inc(v_fst_2763_);
                        crate::leanh::lean_dec(v_val_2761_);
                        v___x_2765_ = crate::leanh::lean_box(0);
                        v_isShared_2766_ = v_isSharedCheck_3019_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2760_);
                    crate::leanh::lean_dec_ref(v_stepType_2753_);
                    crate::leanh::lean_dec_ref(v_step_2752_);
                    crate::leanh::lean_dec_ref(v_result_2750_);
                    v___x_3020_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_Term_mkCalcTrans___closed__12),
                        core::ptr::addr_of_mut!(l_Lean_Elab_Term_mkCalcTrans___closed__12_once),
                        _init_l_Lean_Elab_Term_mkCalcTrans___closed__12,
                    );
                    v___x_3021_ = l_panic___at___00Lean_Elab_Term_mkCalcTrans_spec__1(
                        v___x_3020_,
                        v_a_2754_,
                        v_a_2755_,
                        v_a_2756_,
                        v_a_2757_,
                    );
                    return v___x_3021_;
                }
            }
            1 => {
                v_fst_2767_ = crate::leanh::lean_ctor_get(v_snd_2762_, 0);
                v_snd_2768_ = crate::leanh::lean_ctor_get(v_snd_2762_, 1);
                v_isSharedCheck_3018_ = (!crate::leanh::lean_is_exclusive(v_snd_2762_)) as u8;
                if v_isSharedCheck_3018_ == 0 {
                    v___x_2770_ = v_snd_2762_;
                    v_isShared_2771_ = v_isSharedCheck_3018_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2768_);
                    crate::leanh::lean_inc(v_fst_2767_);
                    crate::leanh::lean_dec(v_snd_2762_);
                    v___x_2770_ = crate::leanh::lean_box(0);
                    v_isShared_2771_ = v_isSharedCheck_3018_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2772_ =
                    l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0___redArg(
                        v_stepType_2753_,
                        v_a_2755_,
                    );
                v_a_2773_ = crate::leanh::lean_ctor_get(v___x_2772_, 0);
                crate::leanh::lean_inc(v_a_2773_);
                crate::leanh::lean_dec_ref(v___x_2772_);
                v___x_2774_ = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(v_a_2773_);
                crate::leanh::lean_dec(v_a_2773_);
                v_a_2775_ = crate::leanh::lean_ctor_get(v___x_2774_, 0);
                crate::leanh::lean_inc(v_a_2775_);
                crate::leanh::lean_dec_ref(v___x_2774_);
                if crate::leanh::lean_obj_tag(v_a_2775_) == 1 {
                    v_val_2776_ = crate::leanh::lean_ctor_get(v_a_2775_, 0);
                    v_isSharedCheck_3015_ = (!crate::leanh::lean_is_exclusive(v_a_2775_)) as u8;
                    if v_isSharedCheck_3015_ == 0 {
                        v___x_2778_ = v_a_2775_;
                        v_isShared_2779_ = v_isSharedCheck_3015_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2776_);
                        crate::leanh::lean_dec(v_a_2775_);
                        v___x_2778_ = crate::leanh::lean_box(0);
                        v_isShared_2779_ = v_isSharedCheck_3015_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2775_);
                    crate::leanh::lean_del_object(v___x_2770_);
                    crate::leanh::lean_dec(v_snd_2768_);
                    crate::leanh::lean_dec(v_fst_2767_);
                    crate::leanh::lean_del_object(v___x_2765_);
                    crate::leanh::lean_dec(v_fst_2763_);
                    crate::leanh::lean_dec_ref(v_step_2752_);
                    crate::leanh::lean_dec_ref(v_result_2750_);
                    v___x_3016_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_Term_mkCalcTrans___closed__11),
                        core::ptr::addr_of_mut!(l_Lean_Elab_Term_mkCalcTrans___closed__11_once),
                        _init_l_Lean_Elab_Term_mkCalcTrans___closed__11,
                    );
                    v___x_3017_ = l_panic___at___00Lean_Elab_Term_mkCalcTrans_spec__1(
                        v___x_3016_,
                        v_a_2754_,
                        v_a_2755_,
                        v_a_2756_,
                        v_a_2757_,
                    );
                    return v___x_3017_;
                }
            }
            3 => {
                v_snd_2780_ = crate::leanh::lean_ctor_get(v_val_2776_, 1);
                v_fst_2781_ = crate::leanh::lean_ctor_get(v_val_2776_, 0);
                v_isSharedCheck_3014_ = (!crate::leanh::lean_is_exclusive(v_val_2776_)) as u8;
                if v_isSharedCheck_3014_ == 0 {
                    v___x_2783_ = v_val_2776_;
                    v_isShared_2784_ = v_isSharedCheck_3014_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2780_);
                    crate::leanh::lean_inc(v_fst_2781_);
                    crate::leanh::lean_dec(v_val_2776_);
                    v___x_2783_ = crate::leanh::lean_box(0);
                    v_isShared_2784_ = v_isSharedCheck_3014_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_snd_2785_ = crate::leanh::lean_ctor_get(v_snd_2780_, 1);
                v_isSharedCheck_3012_ = (!crate::leanh::lean_is_exclusive(v_snd_2780_)) as u8;
                if v_isSharedCheck_3012_ == 0 {
                    v_unused_3013_ = crate::leanh::lean_ctor_get(v_snd_2780_, 0);
                    crate::leanh::lean_dec(v_unused_3013_);
                    v___x_2787_ = v_snd_2780_;
                    v_isShared_2788_ = v_isSharedCheck_3012_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2785_);
                    crate::leanh::lean_dec(v_snd_2780_);
                    v___x_2787_ = crate::leanh::lean_box(0);
                    v_isShared_2788_ = v_isSharedCheck_3012_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc(v_fst_2763_);
                v___x_2789_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(
                    v_fst_2763_,
                    v_a_2754_,
                    v_a_2755_,
                    v_a_2756_,
                    v_a_2757_,
                );
                if crate::leanh::lean_obj_tag(v___x_2789_) == 0 {
                    v_a_2790_ = crate::leanh::lean_ctor_get(v___x_2789_, 0);
                    crate::leanh::lean_inc(v_a_2790_);
                    crate::leanh::lean_dec_ref_known(v___x_2789_, 1);
                    crate::leanh::lean_inc(v_fst_2781_);
                    v___x_2791_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(
                        v_fst_2781_,
                        v_a_2754_,
                        v_a_2755_,
                        v_a_2756_,
                        v_a_2757_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2791_) == 0 {
                        v_a_2792_ = crate::leanh::lean_ctor_get(v___x_2791_, 0);
                        crate::leanh::lean_inc(v_a_2792_);
                        crate::leanh::lean_dec_ref_known(v___x_2791_, 1);
                        crate::leanh::lean_inc(v_a_2757_);
                        crate::leanh::lean_inc_ref(v_a_2756_);
                        crate::leanh::lean_inc(v_a_2755_);
                        crate::leanh::lean_inc_ref(v_a_2754_);
                        crate::leanh::lean_inc(v_fst_2767_);
                        v___x_2793_ = lean_infer_type(
                            v_fst_2767_,
                            v_a_2754_,
                            v_a_2755_,
                            v_a_2756_,
                            v_a_2757_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2793_) == 0 {
                            v_a_2794_ = crate::leanh::lean_ctor_get(v___x_2793_, 0);
                            crate::leanh::lean_inc(v_a_2794_);
                            crate::leanh::lean_dec_ref_known(v___x_2793_, 1);
                            crate::leanh::lean_inc(v_a_2757_);
                            crate::leanh::lean_inc_ref(v_a_2756_);
                            crate::leanh::lean_inc(v_a_2755_);
                            crate::leanh::lean_inc_ref(v_a_2754_);
                            crate::leanh::lean_inc(v_snd_2768_);
                            v___x_2795_ = lean_infer_type(
                                v_snd_2768_,
                                v_a_2754_,
                                v_a_2755_,
                                v_a_2756_,
                                v_a_2757_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_2795_) == 0 {
                                v_a_2796_ = crate::leanh::lean_ctor_get(v___x_2795_, 0);
                                crate::leanh::lean_inc(v_a_2796_);
                                crate::leanh::lean_dec_ref_known(v___x_2795_, 1);
                                crate::leanh::lean_inc(v_a_2757_);
                                crate::leanh::lean_inc_ref(v_a_2756_);
                                crate::leanh::lean_inc(v_a_2755_);
                                crate::leanh::lean_inc_ref(v_a_2754_);
                                crate::leanh::lean_inc(v_snd_2785_);
                                v___x_2797_ = lean_infer_type(
                                    v_snd_2785_,
                                    v_a_2754_,
                                    v_a_2755_,
                                    v_a_2756_,
                                    v_a_2757_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_2797_) == 0 {
                                    v_a_2798_ = crate::leanh::lean_ctor_get(v___x_2797_, 0);
                                    crate::leanh::lean_inc(v_a_2798_);
                                    crate::leanh::lean_dec_ref_known(v___x_2797_, 1);
                                    crate::leanh::lean_inc(v_a_2794_);
                                    v___x_2799_ = l_Lean_Meta_getLevel(
                                        v_a_2794_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_2799_) == 0 {
                                        v_a_2800_ = crate::leanh::lean_ctor_get(v___x_2799_, 0);
                                        crate::leanh::lean_inc(v_a_2800_);
                                        crate::leanh::lean_dec_ref_known(v___x_2799_, 1);
                                        crate::leanh::lean_inc(v_a_2796_);
                                        v___x_2801_ = l_Lean_Meta_getLevel(
                                            v_a_2796_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_,
                                        );
                                        if crate::leanh::lean_obj_tag(v___x_2801_) == 0 {
                                            v_a_2802_ = crate::leanh::lean_ctor_get(v___x_2801_, 0);
                                            crate::leanh::lean_inc(v_a_2802_);
                                            crate::leanh::lean_dec_ref_known(v___x_2801_, 1);
                                            crate::leanh::lean_inc(v_a_2798_);
                                            v___x_2803_ = l_Lean_Meta_getLevel(
                                                v_a_2798_, v_a_2754_, v_a_2755_, v_a_2756_,
                                                v_a_2757_,
                                            );
                                            if crate::leanh::lean_obj_tag(v___x_2803_) == 0 {
                                                v_a_2804_ =
                                                    crate::leanh::lean_ctor_get(v___x_2803_, 0);
                                                crate::leanh::lean_inc(v_a_2804_);
                                                crate::leanh::lean_dec_ref_known(v___x_2803_, 1);
                                                v___x_2805_ = l_Lean_Meta_mkFreshLevelMVar(
                                                    v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_,
                                                );
                                                if crate::leanh::lean_obj_tag(v___x_2805_) == 0 {
                                                    v_a_2806_ =
                                                        crate::leanh::lean_ctor_get(v___x_2805_, 0);
                                                    crate::leanh::lean_inc_n(v_a_2806_, 2);
                                                    crate::leanh::lean_dec_ref_known(
                                                        v___x_2805_,
                                                        1,
                                                    );
                                                    v___x_2807_ = l_Lean_mkSort(v_a_2806_);
                                                    crate::leanh::lean_inc(v_a_2798_);
                                                    v___x_2808_ = l_Lean_mkArrow(
                                                        v_a_2798_,
                                                        v___x_2807_,
                                                        v_a_2756_,
                                                        v_a_2757_,
                                                    );
                                                    if crate::leanh::lean_obj_tag(v___x_2808_) == 0
                                                    {
                                                        v_a_2809_ = crate::leanh::lean_ctor_get(
                                                            v___x_2808_,
                                                            0,
                                                        );
                                                        crate::leanh::lean_inc(v_a_2809_);
                                                        crate::leanh::lean_dec_ref_known(
                                                            v___x_2808_,
                                                            1,
                                                        );
                                                        crate::leanh::lean_inc(v_a_2794_);
                                                        v___x_2810_ = l_Lean_mkArrow(
                                                            v_a_2794_, v_a_2809_, v_a_2756_,
                                                            v_a_2757_,
                                                        );
                                                        if crate::leanh::lean_obj_tag(v___x_2810_)
                                                            == 0
                                                        {
                                                            v_a_2811_ = crate::leanh::lean_ctor_get(
                                                                v___x_2810_,
                                                                0,
                                                            );
                                                            crate::leanh::lean_inc(v_a_2811_);
                                                            crate::leanh::lean_dec_ref_known(
                                                                v___x_2810_,
                                                                1,
                                                            );
                                                            if v_isShared_2779_ == 0 {
                                                                crate::leanh::lean_ctor_set(
                                                                    v___x_2778_,
                                                                    0,
                                                                    v_a_2811_,
                                                                );
                                                                v___x_2813_ = v___x_2778_;
                                                                state = 6;
                                                                continue;
                                                            } else {
                                                                v_reuseFailAlloc_2923_ =
                                                                    crate::leanh::lean_alloc_ctor(
                                                                        1,
                                                                        1,
                                                                        (0) as u32,
                                                                    );
                                                                crate::leanh::lean_ctor_set(
                                                                    v_reuseFailAlloc_2923_,
                                                                    0,
                                                                    v_a_2811_,
                                                                );
                                                                v___x_2813_ =
                                                                    v_reuseFailAlloc_2923_;
                                                                state = 6;
                                                                continue;
                                                            }
                                                        } else {
                                                            crate::leanh::lean_dec(v_a_2806_);
                                                            crate::leanh::lean_dec(v_a_2804_);
                                                            crate::leanh::lean_dec(v_a_2802_);
                                                            crate::leanh::lean_dec(v_a_2800_);
                                                            crate::leanh::lean_dec(v_a_2798_);
                                                            crate::leanh::lean_dec(v_a_2796_);
                                                            crate::leanh::lean_dec(v_a_2794_);
                                                            crate::leanh::lean_dec(v_a_2792_);
                                                            crate::leanh::lean_dec(v_a_2790_);
                                                            crate::leanh::lean_del_object(
                                                                v___x_2787_,
                                                            );
                                                            crate::leanh::lean_dec(v_snd_2785_);
                                                            crate::leanh::lean_del_object(
                                                                v___x_2783_,
                                                            );
                                                            crate::leanh::lean_dec(v_fst_2781_);
                                                            crate::leanh::lean_del_object(
                                                                v___x_2778_,
                                                            );
                                                            crate::leanh::lean_del_object(
                                                                v___x_2770_,
                                                            );
                                                            crate::leanh::lean_dec(v_snd_2768_);
                                                            crate::leanh::lean_dec(v_fst_2767_);
                                                            crate::leanh::lean_del_object(
                                                                v___x_2765_,
                                                            );
                                                            crate::leanh::lean_dec(v_fst_2763_);
                                                            crate::leanh::lean_dec_ref(
                                                                v_step_2752_,
                                                            );
                                                            crate::leanh::lean_dec_ref(
                                                                v_result_2750_,
                                                            );
                                                            v_a_2924_ = crate::leanh::lean_ctor_get(
                                                                v___x_2810_,
                                                                0,
                                                            );
                                                            v_isSharedCheck_2931_ =
                                                                (!crate::leanh::lean_is_exclusive(
                                                                    v___x_2810_,
                                                                ))
                                                                    as u8;
                                                            if v_isSharedCheck_2931_ == 0 {
                                                                v___x_2926_ = v___x_2810_;
                                                                v_isShared_2927_ =
                                                                    v_isSharedCheck_2931_;
                                                                state = 22;
                                                                continue;
                                                            } else {
                                                                crate::leanh::lean_inc(v_a_2924_);
                                                                crate::leanh::lean_dec(v___x_2810_);
                                                                v___x_2926_ =
                                                                    crate::leanh::lean_box(0);
                                                                v_isShared_2927_ =
                                                                    v_isSharedCheck_2931_;
                                                                state = 22;
                                                                continue;
                                                            }
                                                        }
                                                    } else {
                                                        crate::leanh::lean_dec(v_a_2806_);
                                                        crate::leanh::lean_dec(v_a_2804_);
                                                        crate::leanh::lean_dec(v_a_2802_);
                                                        crate::leanh::lean_dec(v_a_2800_);
                                                        crate::leanh::lean_dec(v_a_2798_);
                                                        crate::leanh::lean_dec(v_a_2796_);
                                                        crate::leanh::lean_dec(v_a_2794_);
                                                        crate::leanh::lean_dec(v_a_2792_);
                                                        crate::leanh::lean_dec(v_a_2790_);
                                                        crate::leanh::lean_del_object(v___x_2787_);
                                                        crate::leanh::lean_dec(v_snd_2785_);
                                                        crate::leanh::lean_del_object(v___x_2783_);
                                                        crate::leanh::lean_dec(v_fst_2781_);
                                                        crate::leanh::lean_del_object(v___x_2778_);
                                                        crate::leanh::lean_del_object(v___x_2770_);
                                                        crate::leanh::lean_dec(v_snd_2768_);
                                                        crate::leanh::lean_dec(v_fst_2767_);
                                                        crate::leanh::lean_del_object(v___x_2765_);
                                                        crate::leanh::lean_dec(v_fst_2763_);
                                                        crate::leanh::lean_dec_ref(v_step_2752_);
                                                        crate::leanh::lean_dec_ref(v_result_2750_);
                                                        v_a_2932_ = crate::leanh::lean_ctor_get(
                                                            v___x_2808_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_2939_ =
                                                            (!crate::leanh::lean_is_exclusive(
                                                                v___x_2808_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_2939_ == 0 {
                                                            v___x_2934_ = v___x_2808_;
                                                            v_isShared_2935_ =
                                                                v_isSharedCheck_2939_;
                                                            state = 24;
                                                            continue;
                                                        } else {
                                                            crate::leanh::lean_inc(v_a_2932_);
                                                            crate::leanh::lean_dec(v___x_2808_);
                                                            v___x_2934_ = crate::leanh::lean_box(0);
                                                            v_isShared_2935_ =
                                                                v_isSharedCheck_2939_;
                                                            state = 24;
                                                            continue;
                                                        }
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec(v_a_2804_);
                                                    crate::leanh::lean_dec(v_a_2802_);
                                                    crate::leanh::lean_dec(v_a_2800_);
                                                    crate::leanh::lean_dec(v_a_2798_);
                                                    crate::leanh::lean_dec(v_a_2796_);
                                                    crate::leanh::lean_dec(v_a_2794_);
                                                    crate::leanh::lean_dec(v_a_2792_);
                                                    crate::leanh::lean_dec(v_a_2790_);
                                                    crate::leanh::lean_del_object(v___x_2787_);
                                                    crate::leanh::lean_dec(v_snd_2785_);
                                                    crate::leanh::lean_del_object(v___x_2783_);
                                                    crate::leanh::lean_dec(v_fst_2781_);
                                                    crate::leanh::lean_del_object(v___x_2778_);
                                                    crate::leanh::lean_del_object(v___x_2770_);
                                                    crate::leanh::lean_dec(v_snd_2768_);
                                                    crate::leanh::lean_dec(v_fst_2767_);
                                                    crate::leanh::lean_del_object(v___x_2765_);
                                                    crate::leanh::lean_dec(v_fst_2763_);
                                                    crate::leanh::lean_dec_ref(v_step_2752_);
                                                    crate::leanh::lean_dec_ref(v_result_2750_);
                                                    v_a_2940_ =
                                                        crate::leanh::lean_ctor_get(v___x_2805_, 0);
                                                    v_isSharedCheck_2947_ =
                                                        (!crate::leanh::lean_is_exclusive(
                                                            v___x_2805_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_2947_ == 0 {
                                                        v___x_2942_ = v___x_2805_;
                                                        v_isShared_2943_ = v_isSharedCheck_2947_;
                                                        state = 26;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_inc(v_a_2940_);
                                                        crate::leanh::lean_dec(v___x_2805_);
                                                        v___x_2942_ = crate::leanh::lean_box(0);
                                                        v_isShared_2943_ = v_isSharedCheck_2947_;
                                                        state = 26;
                                                        continue;
                                                    }
                                                }
                                            } else {
                                                crate::leanh::lean_dec(v_a_2802_);
                                                crate::leanh::lean_dec(v_a_2800_);
                                                crate::leanh::lean_dec(v_a_2798_);
                                                crate::leanh::lean_dec(v_a_2796_);
                                                crate::leanh::lean_dec(v_a_2794_);
                                                crate::leanh::lean_dec(v_a_2792_);
                                                crate::leanh::lean_dec(v_a_2790_);
                                                crate::leanh::lean_del_object(v___x_2787_);
                                                crate::leanh::lean_dec(v_snd_2785_);
                                                crate::leanh::lean_del_object(v___x_2783_);
                                                crate::leanh::lean_dec(v_fst_2781_);
                                                crate::leanh::lean_del_object(v___x_2778_);
                                                crate::leanh::lean_del_object(v___x_2770_);
                                                crate::leanh::lean_dec(v_snd_2768_);
                                                crate::leanh::lean_dec(v_fst_2767_);
                                                crate::leanh::lean_del_object(v___x_2765_);
                                                crate::leanh::lean_dec(v_fst_2763_);
                                                crate::leanh::lean_dec_ref(v_step_2752_);
                                                crate::leanh::lean_dec_ref(v_result_2750_);
                                                v_a_2948_ =
                                                    crate::leanh::lean_ctor_get(v___x_2803_, 0);
                                                v_isSharedCheck_2955_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_2803_))
                                                        as u8;
                                                if v_isSharedCheck_2955_ == 0 {
                                                    v___x_2950_ = v___x_2803_;
                                                    v_isShared_2951_ = v_isSharedCheck_2955_;
                                                    state = 28;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_2948_);
                                                    crate::leanh::lean_dec(v___x_2803_);
                                                    v___x_2950_ = crate::leanh::lean_box(0);
                                                    v_isShared_2951_ = v_isSharedCheck_2955_;
                                                    state = 28;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            crate::leanh::lean_dec(v_a_2800_);
                                            crate::leanh::lean_dec(v_a_2798_);
                                            crate::leanh::lean_dec(v_a_2796_);
                                            crate::leanh::lean_dec(v_a_2794_);
                                            crate::leanh::lean_dec(v_a_2792_);
                                            crate::leanh::lean_dec(v_a_2790_);
                                            crate::leanh::lean_del_object(v___x_2787_);
                                            crate::leanh::lean_dec(v_snd_2785_);
                                            crate::leanh::lean_del_object(v___x_2783_);
                                            crate::leanh::lean_dec(v_fst_2781_);
                                            crate::leanh::lean_del_object(v___x_2778_);
                                            crate::leanh::lean_del_object(v___x_2770_);
                                            crate::leanh::lean_dec(v_snd_2768_);
                                            crate::leanh::lean_dec(v_fst_2767_);
                                            crate::leanh::lean_del_object(v___x_2765_);
                                            crate::leanh::lean_dec(v_fst_2763_);
                                            crate::leanh::lean_dec_ref(v_step_2752_);
                                            crate::leanh::lean_dec_ref(v_result_2750_);
                                            v_a_2956_ = crate::leanh::lean_ctor_get(v___x_2801_, 0);
                                            v_isSharedCheck_2963_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_2801_))
                                                    as u8;
                                            if v_isSharedCheck_2963_ == 0 {
                                                v___x_2958_ = v___x_2801_;
                                                v_isShared_2959_ = v_isSharedCheck_2963_;
                                                state = 30;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_2956_);
                                                crate::leanh::lean_dec(v___x_2801_);
                                                v___x_2958_ = crate::leanh::lean_box(0);
                                                v_isShared_2959_ = v_isSharedCheck_2963_;
                                                state = 30;
                                                continue;
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_a_2798_);
                                        crate::leanh::lean_dec(v_a_2796_);
                                        crate::leanh::lean_dec(v_a_2794_);
                                        crate::leanh::lean_dec(v_a_2792_);
                                        crate::leanh::lean_dec(v_a_2790_);
                                        crate::leanh::lean_del_object(v___x_2787_);
                                        crate::leanh::lean_dec(v_snd_2785_);
                                        crate::leanh::lean_del_object(v___x_2783_);
                                        crate::leanh::lean_dec(v_fst_2781_);
                                        crate::leanh::lean_del_object(v___x_2778_);
                                        crate::leanh::lean_del_object(v___x_2770_);
                                        crate::leanh::lean_dec(v_snd_2768_);
                                        crate::leanh::lean_dec(v_fst_2767_);
                                        crate::leanh::lean_del_object(v___x_2765_);
                                        crate::leanh::lean_dec(v_fst_2763_);
                                        crate::leanh::lean_dec_ref(v_step_2752_);
                                        crate::leanh::lean_dec_ref(v_result_2750_);
                                        v_a_2964_ = crate::leanh::lean_ctor_get(v___x_2799_, 0);
                                        v_isSharedCheck_2971_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2799_)) as u8;
                                        if v_isSharedCheck_2971_ == 0 {
                                            v___x_2966_ = v___x_2799_;
                                            v_isShared_2967_ = v_isSharedCheck_2971_;
                                            state = 32;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_2964_);
                                            crate::leanh::lean_dec(v___x_2799_);
                                            v___x_2966_ = crate::leanh::lean_box(0);
                                            v_isShared_2967_ = v_isSharedCheck_2971_;
                                            state = 32;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_2796_);
                                    crate::leanh::lean_dec(v_a_2794_);
                                    crate::leanh::lean_dec(v_a_2792_);
                                    crate::leanh::lean_dec(v_a_2790_);
                                    crate::leanh::lean_del_object(v___x_2787_);
                                    crate::leanh::lean_dec(v_snd_2785_);
                                    crate::leanh::lean_del_object(v___x_2783_);
                                    crate::leanh::lean_dec(v_fst_2781_);
                                    crate::leanh::lean_del_object(v___x_2778_);
                                    crate::leanh::lean_del_object(v___x_2770_);
                                    crate::leanh::lean_dec(v_snd_2768_);
                                    crate::leanh::lean_dec(v_fst_2767_);
                                    crate::leanh::lean_del_object(v___x_2765_);
                                    crate::leanh::lean_dec(v_fst_2763_);
                                    crate::leanh::lean_dec_ref(v_step_2752_);
                                    crate::leanh::lean_dec_ref(v_result_2750_);
                                    v_a_2972_ = crate::leanh::lean_ctor_get(v___x_2797_, 0);
                                    v_isSharedCheck_2979_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2797_)) as u8;
                                    if v_isSharedCheck_2979_ == 0 {
                                        v___x_2974_ = v___x_2797_;
                                        v_isShared_2975_ = v_isSharedCheck_2979_;
                                        state = 34;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2972_);
                                        crate::leanh::lean_dec(v___x_2797_);
                                        v___x_2974_ = crate::leanh::lean_box(0);
                                        v_isShared_2975_ = v_isSharedCheck_2979_;
                                        state = 34;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_2794_);
                                crate::leanh::lean_dec(v_a_2792_);
                                crate::leanh::lean_dec(v_a_2790_);
                                crate::leanh::lean_del_object(v___x_2787_);
                                crate::leanh::lean_dec(v_snd_2785_);
                                crate::leanh::lean_del_object(v___x_2783_);
                                crate::leanh::lean_dec(v_fst_2781_);
                                crate::leanh::lean_del_object(v___x_2778_);
                                crate::leanh::lean_del_object(v___x_2770_);
                                crate::leanh::lean_dec(v_snd_2768_);
                                crate::leanh::lean_dec(v_fst_2767_);
                                crate::leanh::lean_del_object(v___x_2765_);
                                crate::leanh::lean_dec(v_fst_2763_);
                                crate::leanh::lean_dec_ref(v_step_2752_);
                                crate::leanh::lean_dec_ref(v_result_2750_);
                                v_a_2980_ = crate::leanh::lean_ctor_get(v___x_2795_, 0);
                                v_isSharedCheck_2987_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2795_)) as u8;
                                if v_isSharedCheck_2987_ == 0 {
                                    v___x_2982_ = v___x_2795_;
                                    v_isShared_2983_ = v_isSharedCheck_2987_;
                                    state = 36;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2980_);
                                    crate::leanh::lean_dec(v___x_2795_);
                                    v___x_2982_ = crate::leanh::lean_box(0);
                                    v_isShared_2983_ = v_isSharedCheck_2987_;
                                    state = 36;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_2792_);
                            crate::leanh::lean_dec(v_a_2790_);
                            crate::leanh::lean_del_object(v___x_2787_);
                            crate::leanh::lean_dec(v_snd_2785_);
                            crate::leanh::lean_del_object(v___x_2783_);
                            crate::leanh::lean_dec(v_fst_2781_);
                            crate::leanh::lean_del_object(v___x_2778_);
                            crate::leanh::lean_del_object(v___x_2770_);
                            crate::leanh::lean_dec(v_snd_2768_);
                            crate::leanh::lean_dec(v_fst_2767_);
                            crate::leanh::lean_del_object(v___x_2765_);
                            crate::leanh::lean_dec(v_fst_2763_);
                            crate::leanh::lean_dec_ref(v_step_2752_);
                            crate::leanh::lean_dec_ref(v_result_2750_);
                            v_a_2988_ = crate::leanh::lean_ctor_get(v___x_2793_, 0);
                            v_isSharedCheck_2995_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2793_)) as u8;
                            if v_isSharedCheck_2995_ == 0 {
                                v___x_2990_ = v___x_2793_;
                                v_isShared_2991_ = v_isSharedCheck_2995_;
                                state = 38;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2988_);
                                crate::leanh::lean_dec(v___x_2793_);
                                v___x_2990_ = crate::leanh::lean_box(0);
                                v_isShared_2991_ = v_isSharedCheck_2995_;
                                state = 38;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2790_);
                        crate::leanh::lean_del_object(v___x_2787_);
                        crate::leanh::lean_dec(v_snd_2785_);
                        crate::leanh::lean_del_object(v___x_2783_);
                        crate::leanh::lean_dec(v_fst_2781_);
                        crate::leanh::lean_del_object(v___x_2778_);
                        crate::leanh::lean_del_object(v___x_2770_);
                        crate::leanh::lean_dec(v_snd_2768_);
                        crate::leanh::lean_dec(v_fst_2767_);
                        crate::leanh::lean_del_object(v___x_2765_);
                        crate::leanh::lean_dec(v_fst_2763_);
                        crate::leanh::lean_dec_ref(v_step_2752_);
                        crate::leanh::lean_dec_ref(v_result_2750_);
                        v_a_2996_ = crate::leanh::lean_ctor_get(v___x_2791_, 0);
                        v_isSharedCheck_3003_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2791_)) as u8;
                        if v_isSharedCheck_3003_ == 0 {
                            v___x_2998_ = v___x_2791_;
                            v_isShared_2999_ = v_isSharedCheck_3003_;
                            state = 40;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2996_);
                            crate::leanh::lean_dec(v___x_2791_);
                            v___x_2998_ = crate::leanh::lean_box(0);
                            v_isShared_2999_ = v_isSharedCheck_3003_;
                            state = 40;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2787_);
                    crate::leanh::lean_dec(v_snd_2785_);
                    crate::leanh::lean_del_object(v___x_2783_);
                    crate::leanh::lean_dec(v_fst_2781_);
                    crate::leanh::lean_del_object(v___x_2778_);
                    crate::leanh::lean_del_object(v___x_2770_);
                    crate::leanh::lean_dec(v_snd_2768_);
                    crate::leanh::lean_dec(v_fst_2767_);
                    crate::leanh::lean_del_object(v___x_2765_);
                    crate::leanh::lean_dec(v_fst_2763_);
                    crate::leanh::lean_dec_ref(v_step_2752_);
                    crate::leanh::lean_dec_ref(v_result_2750_);
                    v_a_3004_ = crate::leanh::lean_ctor_get(v___x_2789_, 0);
                    v_isSharedCheck_3011_ = (!crate::leanh::lean_is_exclusive(v___x_2789_)) as u8;
                    if v_isSharedCheck_3011_ == 0 {
                        v___x_3006_ = v___x_2789_;
                        v_isShared_3007_ = v_isSharedCheck_3011_;
                        state = 42;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3004_);
                        crate::leanh::lean_dec(v___x_2789_);
                        v___x_3006_ = crate::leanh::lean_box(0);
                        v_isShared_3007_ = v_isSharedCheck_3011_;
                        state = 42;
                        continue;
                    }
                }
            }
            6 => {
                v___x_2814_ = 0;
                v___x_2815_ = crate::leanh::lean_box(0);
                v___x_2816_ = l_Lean_Meta_mkFreshExprMVar(
                    v___x_2813_,
                    v___x_2814_,
                    v___x_2815_,
                    v_a_2754_,
                    v_a_2755_,
                    v_a_2756_,
                    v_a_2757_,
                );
                if crate::leanh::lean_obj_tag(v___x_2816_) == 0 {
                    v_a_2817_ = crate::leanh::lean_ctor_get(v___x_2816_, 0);
                    crate::leanh::lean_inc(v_a_2817_);
                    crate::leanh::lean_dec_ref_known(v___x_2816_, 1);
                    v___x_2818_ = l_Lean_Elab_Term_mkCalcTrans___closed__1;
                    v___x_2819_ = crate::leanh::lean_box(0);
                    if v_isShared_2784_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_2783_, 1);
                        crate::leanh::lean_ctor_set(v___x_2783_, 1, v___x_2819_);
                        crate::leanh::lean_ctor_set(v___x_2783_, 0, v_a_2804_);
                        v___x_2821_ = v___x_2783_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_2914_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2914_, 0, v_a_2804_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2914_, 1, v___x_2819_);
                        v___x_2821_ = v_reuseFailAlloc_2914_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2806_);
                    crate::leanh::lean_dec(v_a_2804_);
                    crate::leanh::lean_dec(v_a_2802_);
                    crate::leanh::lean_dec(v_a_2800_);
                    crate::leanh::lean_dec(v_a_2798_);
                    crate::leanh::lean_dec(v_a_2796_);
                    crate::leanh::lean_dec(v_a_2794_);
                    crate::leanh::lean_dec(v_a_2792_);
                    crate::leanh::lean_dec(v_a_2790_);
                    crate::leanh::lean_del_object(v___x_2787_);
                    crate::leanh::lean_dec(v_snd_2785_);
                    crate::leanh::lean_del_object(v___x_2783_);
                    crate::leanh::lean_dec(v_fst_2781_);
                    crate::leanh::lean_del_object(v___x_2770_);
                    crate::leanh::lean_dec(v_snd_2768_);
                    crate::leanh::lean_dec(v_fst_2767_);
                    crate::leanh::lean_del_object(v___x_2765_);
                    crate::leanh::lean_dec(v_fst_2763_);
                    crate::leanh::lean_dec_ref(v_step_2752_);
                    crate::leanh::lean_dec_ref(v_result_2750_);
                    v_a_2915_ = crate::leanh::lean_ctor_get(v___x_2816_, 0);
                    v_isSharedCheck_2922_ = (!crate::leanh::lean_is_exclusive(v___x_2816_)) as u8;
                    if v_isSharedCheck_2922_ == 0 {
                        v___x_2917_ = v___x_2816_;
                        v_isShared_2918_ = v_isSharedCheck_2922_;
                        state = 20;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2915_);
                        crate::leanh::lean_dec(v___x_2816_);
                        v___x_2917_ = crate::leanh::lean_box(0);
                        v_isShared_2918_ = v_isSharedCheck_2922_;
                        state = 20;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_2771_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2770_, 1);
                    crate::leanh::lean_ctor_set(v___x_2770_, 1, v___x_2821_);
                    crate::leanh::lean_ctor_set(v___x_2770_, 0, v_a_2802_);
                    v___x_2823_ = v___x_2770_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2913_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2913_, 0, v_a_2802_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2913_, 1, v___x_2821_);
                    v___x_2823_ = v_reuseFailAlloc_2913_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_2766_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2765_, 1);
                    crate::leanh::lean_ctor_set(v___x_2765_, 1, v___x_2823_);
                    crate::leanh::lean_ctor_set(v___x_2765_, 0, v_a_2800_);
                    v___x_2825_ = v___x_2765_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2912_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_a_2800_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2912_, 1, v___x_2823_);
                    v___x_2825_ = v_reuseFailAlloc_2912_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_2826_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2826_, 0, v_a_2806_);
                crate::leanh::lean_ctor_set(v___x_2826_, 1, v___x_2825_);
                v___x_2827_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2827_, 0, v_a_2792_);
                crate::leanh::lean_ctor_set(v___x_2827_, 1, v___x_2826_);
                v___x_2828_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2828_, 0, v_a_2790_);
                crate::leanh::lean_ctor_set(v___x_2828_, 1, v___x_2827_);
                crate::leanh::lean_inc_ref(v___x_2828_);
                v___x_2829_ = l_Lean_mkConst(v___x_2818_, v___x_2828_);
                v___x_2830_ = crate::leanh::lean_unsigned_to_nat(6);
                v___x_2831_ = lean_mk_empty_array_with_capacity(v___x_2830_);
                crate::leanh::lean_inc(v_a_2794_);
                v___x_2832_ = lean_array_push(v___x_2831_, v_a_2794_);
                crate::leanh::lean_inc(v_a_2796_);
                v___x_2833_ = lean_array_push(v___x_2832_, v_a_2796_);
                crate::leanh::lean_inc(v_a_2798_);
                v___x_2834_ = lean_array_push(v___x_2833_, v_a_2798_);
                crate::leanh::lean_inc(v_fst_2763_);
                v___x_2835_ = lean_array_push(v___x_2834_, v_fst_2763_);
                crate::leanh::lean_inc(v_fst_2781_);
                v___x_2836_ = lean_array_push(v___x_2835_, v_fst_2781_);
                crate::leanh::lean_inc(v_a_2817_);
                v___x_2837_ = lean_array_push(v___x_2836_, v_a_2817_);
                v___x_2838_ = l_Lean_mkAppN(v___x_2829_, v___x_2837_);
                crate::leanh::lean_dec_ref(v___x_2837_);
                v___x_2839_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc_ref(v___x_2838_);
                v___x_2840_ = l_Lean_Meta_trySynthInstance(
                    v___x_2838_,
                    v___x_2839_,
                    v_a_2754_,
                    v_a_2755_,
                    v_a_2756_,
                    v_a_2757_,
                );
                if crate::leanh::lean_obj_tag(v___x_2840_) == 0 {
                    v_a_2841_ = crate::leanh::lean_ctor_get(v___x_2840_, 0);
                    crate::leanh::lean_inc(v_a_2841_);
                    crate::leanh::lean_dec_ref_known(v___x_2840_, 1);
                    if crate::leanh::lean_obj_tag(v_a_2841_) == 1 {
                        crate::leanh::lean_dec_ref(v___x_2838_);
                        v_a_2842_ = crate::leanh::lean_ctor_get(v_a_2841_, 0);
                        crate::leanh::lean_inc(v_a_2842_);
                        crate::leanh::lean_dec_ref_known(v_a_2841_, 1);
                        v___x_2843_ = l_Lean_Elab_Term_mkCalcTrans___closed__3;
                        v___x_2844_ = l_Lean_mkConst(v___x_2843_, v___x_2828_);
                        v___x_2845_ = crate::leanh::lean_unsigned_to_nat(12);
                        v___x_2846_ = lean_mk_empty_array_with_capacity(v___x_2845_);
                        v___x_2847_ = lean_array_push(v___x_2846_, v_a_2794_);
                        v___x_2848_ = lean_array_push(v___x_2847_, v_a_2796_);
                        v___x_2849_ = lean_array_push(v___x_2848_, v_a_2798_);
                        v___x_2850_ = lean_array_push(v___x_2849_, v_fst_2763_);
                        v___x_2851_ = lean_array_push(v___x_2850_, v_fst_2781_);
                        v___x_2852_ = lean_array_push(v___x_2851_, v_a_2817_);
                        v___x_2853_ = lean_array_push(v___x_2852_, v_a_2842_);
                        v___x_2854_ = lean_array_push(v___x_2853_, v_fst_2767_);
                        v___x_2855_ = lean_array_push(v___x_2854_, v_snd_2768_);
                        v___x_2856_ = lean_array_push(v___x_2855_, v_snd_2785_);
                        v___x_2857_ = lean_array_push(v___x_2856_, v_result_2750_);
                        v___x_2858_ = lean_array_push(v___x_2857_, v_step_2752_);
                        v___x_2859_ = l_Lean_mkAppN(v___x_2844_, v___x_2858_);
                        crate::leanh::lean_dec_ref(v___x_2858_);
                        crate::leanh::lean_inc(v_a_2757_);
                        crate::leanh::lean_inc_ref(v_a_2756_);
                        crate::leanh::lean_inc(v_a_2755_);
                        crate::leanh::lean_inc_ref(v_a_2754_);
                        crate::leanh::lean_inc_ref(v___x_2859_);
                        v___x_2860_ = lean_infer_type(
                            v___x_2859_,
                            v_a_2754_,
                            v_a_2755_,
                            v_a_2756_,
                            v_a_2757_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2860_) == 0 {
                            v_a_2861_ = crate::leanh::lean_ctor_get(v___x_2860_, 0);
                            crate::leanh::lean_inc(v_a_2861_);
                            crate::leanh::lean_dec_ref_known(v___x_2860_, 1);
                            v___x_2862_ = l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0___redArg(v_a_2861_, v_a_2755_);
                            v_a_2863_ = crate::leanh::lean_ctor_get(v___x_2862_, 0);
                            v_isSharedCheck_2889_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2862_)) as u8;
                            if v_isSharedCheck_2889_ == 0 {
                                v___x_2865_ = v___x_2862_;
                                v_isShared_2866_ = v_isSharedCheck_2889_;
                                state = 10;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2863_);
                                crate::leanh::lean_dec(v___x_2862_);
                                v___x_2865_ = crate::leanh::lean_box(0);
                                v_isShared_2866_ = v_isSharedCheck_2889_;
                                state = 10;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_2859_);
                            crate::leanh::lean_del_object(v___x_2787_);
                            v_a_2890_ = crate::leanh::lean_ctor_get(v___x_2860_, 0);
                            v_isSharedCheck_2897_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2860_)) as u8;
                            if v_isSharedCheck_2897_ == 0 {
                                v___x_2892_ = v___x_2860_;
                                v_isShared_2893_ = v_isSharedCheck_2897_;
                                state = 16;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2890_);
                                crate::leanh::lean_dec(v___x_2860_);
                                v___x_2892_ = crate::leanh::lean_box(0);
                                v_isShared_2893_ = v_isSharedCheck_2897_;
                                state = 16;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2841_);
                        crate::leanh::lean_dec_ref_known(v___x_2828_, 2);
                        crate::leanh::lean_dec(v_a_2817_);
                        crate::leanh::lean_dec(v_a_2798_);
                        crate::leanh::lean_dec(v_a_2796_);
                        crate::leanh::lean_dec(v_a_2794_);
                        crate::leanh::lean_del_object(v___x_2787_);
                        crate::leanh::lean_dec(v_snd_2785_);
                        crate::leanh::lean_dec(v_fst_2781_);
                        crate::leanh::lean_dec(v_snd_2768_);
                        crate::leanh::lean_dec(v_fst_2767_);
                        crate::leanh::lean_dec(v_fst_2763_);
                        crate::leanh::lean_dec_ref(v_step_2752_);
                        crate::leanh::lean_dec_ref(v_result_2750_);
                        v___x_2898_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Elab_Term_mkCalcTrans___closed__7),
                            core::ptr::addr_of_mut!(l_Lean_Elab_Term_mkCalcTrans___closed__7_once),
                            _init_l_Lean_Elab_Term_mkCalcTrans___closed__7,
                        );
                        v___x_2899_ = l_Lean_indentExpr(v___x_2838_);
                        v___x_2900_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2900_, 0, v___x_2898_);
                        crate::leanh::lean_ctor_set(v___x_2900_, 1, v___x_2899_);
                        v___x_2901_ = l_Lean_useDiagnosticMsg;
                        v___x_2902_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2902_, 0, v___x_2900_);
                        crate::leanh::lean_ctor_set(v___x_2902_, 1, v___x_2901_);
                        v___x_2903_ = l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0___redArg(v___x_2902_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_);
                        return v___x_2903_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_2838_);
                    crate::leanh::lean_dec_ref_known(v___x_2828_, 2);
                    crate::leanh::lean_dec(v_a_2817_);
                    crate::leanh::lean_dec(v_a_2798_);
                    crate::leanh::lean_dec(v_a_2796_);
                    crate::leanh::lean_dec(v_a_2794_);
                    crate::leanh::lean_del_object(v___x_2787_);
                    crate::leanh::lean_dec(v_snd_2785_);
                    crate::leanh::lean_dec(v_fst_2781_);
                    crate::leanh::lean_dec(v_snd_2768_);
                    crate::leanh::lean_dec(v_fst_2767_);
                    crate::leanh::lean_dec(v_fst_2763_);
                    crate::leanh::lean_dec_ref(v_step_2752_);
                    crate::leanh::lean_dec_ref(v_result_2750_);
                    v_a_2904_ = crate::leanh::lean_ctor_get(v___x_2840_, 0);
                    v_isSharedCheck_2911_ = (!crate::leanh::lean_is_exclusive(v___x_2840_)) as u8;
                    if v_isSharedCheck_2911_ == 0 {
                        v___x_2906_ = v___x_2840_;
                        v_isShared_2907_ = v_isSharedCheck_2911_;
                        state = 18;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2904_);
                        crate::leanh::lean_dec(v___x_2840_);
                        v___x_2906_ = crate::leanh::lean_box(0);
                        v_isShared_2907_ = v_isSharedCheck_2911_;
                        state = 18;
                        continue;
                    }
                }
            }
            10 => {
                v___x_2867_ = l_Lean_Expr_headBeta(v_a_2863_);
                v___x_2875_ = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(v___x_2867_);
                v_a_2876_ = crate::leanh::lean_ctor_get(v___x_2875_, 0);
                crate::leanh::lean_inc(v_a_2876_);
                crate::leanh::lean_dec_ref(v___x_2875_);
                if crate::leanh::lean_obj_tag(v_a_2876_) == 0 {
                    crate::leanh::lean_del_object(v___x_2865_);
                    crate::leanh::lean_dec_ref(v___x_2859_);
                    crate::leanh::lean_del_object(v___x_2787_);
                    v___x_2877_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_Term_mkCalcTrans___closed__5),
                        core::ptr::addr_of_mut!(l_Lean_Elab_Term_mkCalcTrans___closed__5_once),
                        _init_l_Lean_Elab_Term_mkCalcTrans___closed__5,
                    );
                    v___x_2878_ = l_Lean_indentExpr(v___x_2867_);
                    v___x_2879_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2879_, 0, v___x_2877_);
                    crate::leanh::lean_ctor_set(v___x_2879_, 1, v___x_2878_);
                    v___x_2880_ = l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0___redArg(v___x_2879_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_);
                    v_a_2881_ = crate::leanh::lean_ctor_get(v___x_2880_, 0);
                    v_isSharedCheck_2888_ = (!crate::leanh::lean_is_exclusive(v___x_2880_)) as u8;
                    if v_isSharedCheck_2888_ == 0 {
                        v___x_2883_ = v___x_2880_;
                        v_isShared_2884_ = v_isSharedCheck_2888_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2881_);
                        crate::leanh::lean_dec(v___x_2880_);
                        v___x_2883_ = crate::leanh::lean_box(0);
                        v_isShared_2884_ = v_isSharedCheck_2888_;
                        state = 14;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_a_2876_, 1);
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_2788_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2787_, 1, v___x_2867_);
                    crate::leanh::lean_ctor_set(v___x_2787_, 0, v___x_2859_);
                    v___x_2870_ = v___x_2787_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2874_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2874_, 0, v___x_2859_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2874_, 1, v___x_2867_);
                    v___x_2870_ = v_reuseFailAlloc_2874_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_2866_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2865_, 0, v___x_2870_);
                    v___x_2872_ = v___x_2865_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2873_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2873_, 0, v___x_2870_);
                    v___x_2872_ = v_reuseFailAlloc_2873_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2872_;
            }
            14 => {
                if v_isShared_2884_ == 0 {
                    v___x_2886_ = v___x_2883_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2887_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2887_, 0, v_a_2881_);
                    v___x_2886_ = v_reuseFailAlloc_2887_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2886_;
            }
            16 => {
                if v_isShared_2893_ == 0 {
                    v___x_2895_ = v___x_2892_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_2896_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2896_, 0, v_a_2890_);
                    v___x_2895_ = v_reuseFailAlloc_2896_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_2895_;
            }
            18 => {
                if v_isShared_2907_ == 0 {
                    v___x_2909_ = v___x_2906_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2910_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2910_, 0, v_a_2904_);
                    v___x_2909_ = v_reuseFailAlloc_2910_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_2909_;
            }
            20 => {
                if v_isShared_2918_ == 0 {
                    v___x_2920_ = v___x_2917_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_2921_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2921_, 0, v_a_2915_);
                    v___x_2920_ = v_reuseFailAlloc_2921_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_2920_;
            }
            22 => {
                if v_isShared_2927_ == 0 {
                    v___x_2929_ = v___x_2926_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_2930_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2930_, 0, v_a_2924_);
                    v___x_2929_ = v_reuseFailAlloc_2930_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_2929_;
            }
            24 => {
                if v_isShared_2935_ == 0 {
                    v___x_2937_ = v___x_2934_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_2938_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2938_, 0, v_a_2932_);
                    v___x_2937_ = v_reuseFailAlloc_2938_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_2937_;
            }
            26 => {
                if v_isShared_2943_ == 0 {
                    v___x_2945_ = v___x_2942_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_2946_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2946_, 0, v_a_2940_);
                    v___x_2945_ = v_reuseFailAlloc_2946_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_2945_;
            }
            28 => {
                if v_isShared_2951_ == 0 {
                    v___x_2953_ = v___x_2950_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_2954_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2954_, 0, v_a_2948_);
                    v___x_2953_ = v_reuseFailAlloc_2954_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_2953_;
            }
            30 => {
                if v_isShared_2959_ == 0 {
                    v___x_2961_ = v___x_2958_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_2962_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2962_, 0, v_a_2956_);
                    v___x_2961_ = v_reuseFailAlloc_2962_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_2961_;
            }
            32 => {
                if v_isShared_2967_ == 0 {
                    v___x_2969_ = v___x_2966_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_2970_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2970_, 0, v_a_2964_);
                    v___x_2969_ = v_reuseFailAlloc_2970_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_2969_;
            }
            34 => {
                if v_isShared_2975_ == 0 {
                    v___x_2977_ = v___x_2974_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_2978_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2978_, 0, v_a_2972_);
                    v___x_2977_ = v_reuseFailAlloc_2978_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_2977_;
            }
            36 => {
                if v_isShared_2983_ == 0 {
                    v___x_2985_ = v___x_2982_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_2986_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2986_, 0, v_a_2980_);
                    v___x_2985_ = v_reuseFailAlloc_2986_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_2985_;
            }
            38 => {
                if v_isShared_2991_ == 0 {
                    v___x_2993_ = v___x_2990_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_2994_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2994_, 0, v_a_2988_);
                    v___x_2993_ = v_reuseFailAlloc_2994_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_2993_;
            }
            40 => {
                if v_isShared_2999_ == 0 {
                    v___x_3001_ = v___x_2998_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_3002_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3002_, 0, v_a_2996_);
                    v___x_3001_ = v_reuseFailAlloc_3002_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_3001_;
            }
            42 => {
                if v_isShared_3007_ == 0 {
                    v___x_3009_ = v___x_3006_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_3010_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3010_, 0, v_a_3004_);
                    v___x_3009_ = v_reuseFailAlloc_3010_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                return v___x_3009_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_mkCalcTrans___boxed(
    mut v_result_3022_: *mut crate::leanh::LeanObject,
    mut v_resultType_3023_: *mut crate::leanh::LeanObject,
    mut v_step_3024_: *mut crate::leanh::LeanObject,
    mut v_stepType_3025_: *mut crate::leanh::LeanObject,
    mut v_a_3026_: *mut crate::leanh::LeanObject,
    mut v_a_3027_: *mut crate::leanh::LeanObject,
    mut v_a_3028_: *mut crate::leanh::LeanObject,
    mut v_a_3029_: *mut crate::leanh::LeanObject,
    mut v_a_3030_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3031_ = l_Lean_Elab_Term_mkCalcTrans(
        v_result_3022_,
        v_resultType_3023_,
        v_step_3024_,
        v_stepType_3025_,
        v_a_3026_,
        v_a_3027_,
        v_a_3028_,
        v_a_3029_,
    );
    crate::leanh::lean_dec(v_a_3029_);
    crate::leanh::lean_dec_ref(v_a_3028_);
    crate::leanh::lean_dec(v_a_3027_);
    crate::leanh::lean_dec_ref(v_a_3026_);
    crate::leanh::lean_dec_ref(v_resultType_3023_);
    return v_res_3031_;
}
pub unsafe fn _init_l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3053_ =
        l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__11;
    v___x_3054_ = l_String_toRawSubstring_x27(v___x_3053_);
    return v___x_3054_;
}
pub unsafe fn l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go(
    mut v_type_3079_: *mut crate::leanh::LeanObject,
    mut v_t_3080_: *mut crate::leanh::LeanObject,
    mut v_a_3081_: u8,
    mut v_a_3082_: *mut crate::leanh::LeanObject,
    mut v_a_3083_: *mut crate::leanh::LeanObject,
    mut v_a_3084_: *mut crate::leanh::LeanObject,
    mut v_a_3085_: *mut crate::leanh::LeanObject,
    mut v_a_3086_: *mut crate::leanh::LeanObject,
    mut v_a_3087_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_3092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3097_: u8 = 0;
    let mut v___y_3098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3104_: usize = 0;
    let mut v___x_3105_: usize = 0;
    let mut v___x_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3110_: u8 = 0;
    let mut v_fst_3111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3115_: u8 = 0;
    let mut v___x_3116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3123_: u8 = 0;
    let mut v_isSharedCheck_3124_: u8 = 0;
    let mut v_a_3125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3128_: u8 = 0;
    let mut v___x_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3132_: u8 = 0;
    let mut v_pre_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_3134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_3135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_3136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_3137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_3139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_3140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: u8 = 0;
    let mut v___x_3143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: u8 = 0;
    let mut v___x_3145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: u8 = 0;
    let mut v___x_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: u8 = 0;
    let mut v___x_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3165_: u8 = 0;
    let mut v_ref_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: u8 = 0;
    let mut v___x_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3194_: u8 = 0;
    let mut v_a_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3198_: u8 = 0;
    let mut v___x_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3202_: u8 = 0;
    let mut v___x_3203_: u8 = 0;
    let mut v___x_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_a_3081_ == 0 {
                    crate::leanh::lean_dec_ref(v_type_3079_);
                    v___x_3089_ = crate::leanh::lean_box((v_a_3081_) as usize);
                    v___x_3090_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3090_, 0, v_t_3080_);
                    crate::leanh::lean_ctor_set(v___x_3090_, 1, v___x_3089_);
                    v___x_3091_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3091_, 0, v___x_3090_);
                    return v___x_3091_;
                } else {
                    if crate::leanh::lean_obj_tag(v_t_3080_) == 1 {
                        v_info_3092_ = crate::leanh::lean_ctor_get(v_t_3080_, 0);
                        v_kind_3093_ = crate::leanh::lean_ctor_get(v_t_3080_, 1);
                        v_args_3094_ = crate::leanh::lean_ctor_get(v_t_3080_, 2);
                        if crate::leanh::lean_obj_tag(v_kind_3093_) == 1 {
                            v_pre_3133_ = crate::leanh::lean_ctor_get(v_kind_3093_, 0);
                            if crate::leanh::lean_obj_tag(v_pre_3133_) == 1 {
                                v_pre_3134_ = crate::leanh::lean_ctor_get(v_pre_3133_, 0);
                                if crate::leanh::lean_obj_tag(v_pre_3134_) == 1 {
                                    v_pre_3135_ = crate::leanh::lean_ctor_get(v_pre_3134_, 0);
                                    if crate::leanh::lean_obj_tag(v_pre_3135_) == 1 {
                                        v_pre_3136_ = crate::leanh::lean_ctor_get(v_pre_3135_, 0);
                                        if crate::leanh::lean_obj_tag(v_pre_3136_) == 0 {
                                            v_str_3137_ =
                                                crate::leanh::lean_ctor_get(v_kind_3093_, 1);
                                            v_str_3138_ =
                                                crate::leanh::lean_ctor_get(v_pre_3133_, 1);
                                            v_str_3139_ =
                                                crate::leanh::lean_ctor_get(v_pre_3134_, 1);
                                            v_str_3140_ =
                                                crate::leanh::lean_ctor_get(v_pre_3135_, 1);
                                            v___x_3141_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__0;
                                            v___x_3142_ =
                                                lean_string_dec_eq(v_str_3140_, v___x_3141_);
                                            if v___x_3142_ == 0 {
                                                crate::leanh::lean_inc_ref(v_kind_3093_);
                                                crate::leanh::lean_inc_ref(v_args_3094_);
                                                crate::leanh::lean_inc(v_info_3092_);
                                                crate::leanh::lean_dec_ref_known(v_t_3080_, 3);
                                                v_k_3096_ = v_kind_3093_;
                                                v___y_3097_ = v_a_3081_;
                                                v___y_3098_ = v_a_3082_;
                                                v___y_3099_ = v_a_3083_;
                                                v___y_3100_ = v_a_3084_;
                                                v___y_3101_ = v_a_3085_;
                                                v___y_3102_ = v_a_3086_;
                                                v___y_3103_ = v_a_3087_;
                                                state = 1;
                                                continue;
                                            } else {
                                                v___x_3143_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__1;
                                                v___x_3144_ =
                                                    lean_string_dec_eq(v_str_3139_, v___x_3143_);
                                                if v___x_3144_ == 0 {
                                                    crate::leanh::lean_inc_ref(v_str_3139_);
                                                    crate::leanh::lean_inc_ref(v_str_3138_);
                                                    crate::leanh::lean_inc(v_pre_3136_);
                                                    crate::leanh::lean_inc_ref(v_str_3137_);
                                                    crate::leanh::lean_inc_ref(v_args_3094_);
                                                    crate::leanh::lean_inc(v_info_3092_);
                                                    crate::leanh::lean_dec_ref_known(v_t_3080_, 3);
                                                    v___x_3145_ = l_Lean_Name_str___override(
                                                        v_pre_3136_,
                                                        v___x_3141_,
                                                    );
                                                    v___x_3146_ = l_Lean_Name_str___override(
                                                        v___x_3145_,
                                                        v_str_3139_,
                                                    );
                                                    v___x_3147_ = l_Lean_Name_str___override(
                                                        v___x_3146_,
                                                        v_str_3138_,
                                                    );
                                                    v___x_3148_ = l_Lean_Name_str___override(
                                                        v___x_3147_,
                                                        v_str_3137_,
                                                    );
                                                    v_k_3096_ = v___x_3148_;
                                                    v___y_3097_ = v_a_3081_;
                                                    v___y_3098_ = v_a_3082_;
                                                    v___y_3099_ = v_a_3083_;
                                                    v___y_3100_ = v_a_3084_;
                                                    v___y_3101_ = v_a_3085_;
                                                    v___y_3102_ = v_a_3086_;
                                                    v___y_3103_ = v_a_3087_;
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    v___x_3149_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__2;
                                                    v___x_3150_ = lean_string_dec_eq(
                                                        v_str_3138_,
                                                        v___x_3149_,
                                                    );
                                                    if v___x_3150_ == 0 {
                                                        crate::leanh::lean_inc_ref(v_str_3138_);
                                                        crate::leanh::lean_inc(v_pre_3136_);
                                                        crate::leanh::lean_inc_ref(v_str_3137_);
                                                        crate::leanh::lean_inc_ref(v_args_3094_);
                                                        crate::leanh::lean_inc(v_info_3092_);
                                                        crate::leanh::lean_dec_ref_known(
                                                            v_t_3080_, 3,
                                                        );
                                                        v___x_3151_ = l_Lean_Name_str___override(
                                                            v_pre_3136_,
                                                            v___x_3141_,
                                                        );
                                                        v___x_3152_ = l_Lean_Name_str___override(
                                                            v___x_3151_,
                                                            v___x_3143_,
                                                        );
                                                        v___x_3153_ = l_Lean_Name_str___override(
                                                            v___x_3152_,
                                                            v_str_3138_,
                                                        );
                                                        v___x_3154_ = l_Lean_Name_str___override(
                                                            v___x_3153_,
                                                            v_str_3137_,
                                                        );
                                                        v_k_3096_ = v___x_3154_;
                                                        v___y_3097_ = v_a_3081_;
                                                        v___y_3098_ = v_a_3082_;
                                                        v___y_3099_ = v_a_3083_;
                                                        v___y_3100_ = v_a_3084_;
                                                        v___y_3101_ = v_a_3085_;
                                                        v___y_3102_ = v_a_3086_;
                                                        v___y_3103_ = v_a_3087_;
                                                        state = 1;
                                                        continue;
                                                    } else {
                                                        v___x_3155_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__3;
                                                        v___x_3156_ = lean_string_dec_eq(
                                                            v_str_3137_,
                                                            v___x_3155_,
                                                        );
                                                        if v___x_3156_ == 0 {
                                                            crate::leanh::lean_inc_ref(v_str_3137_);
                                                            crate::leanh::lean_inc(v_pre_3136_);
                                                            crate::leanh::lean_inc_ref(
                                                                v_args_3094_,
                                                            );
                                                            crate::leanh::lean_inc(v_info_3092_);
                                                            crate::leanh::lean_dec_ref_known(
                                                                v_t_3080_, 3,
                                                            );
                                                            v___x_3157_ =
                                                                l_Lean_Name_str___override(
                                                                    v_pre_3136_,
                                                                    v___x_3141_,
                                                                );
                                                            v___x_3158_ =
                                                                l_Lean_Name_str___override(
                                                                    v___x_3157_,
                                                                    v___x_3143_,
                                                                );
                                                            v___x_3159_ =
                                                                l_Lean_Name_str___override(
                                                                    v___x_3158_,
                                                                    v___x_3149_,
                                                                );
                                                            v___x_3160_ =
                                                                l_Lean_Name_str___override(
                                                                    v___x_3159_,
                                                                    v_str_3137_,
                                                                );
                                                            v_k_3096_ = v___x_3160_;
                                                            v___y_3097_ = v_a_3081_;
                                                            v___y_3098_ = v_a_3082_;
                                                            v___y_3099_ = v_a_3083_;
                                                            v___y_3100_ = v_a_3084_;
                                                            v___y_3101_ = v_a_3085_;
                                                            v___y_3102_ = v_a_3086_;
                                                            v___y_3103_ = v_a_3087_;
                                                            state = 1;
                                                            continue;
                                                        } else {
                                                            v___x_3161_ =
                                                                l_Lean_Elab_Term_exprToSyntax(
                                                                    v_type_3079_,
                                                                    v_a_3082_,
                                                                    v_a_3083_,
                                                                    v_a_3084_,
                                                                    v_a_3085_,
                                                                    v_a_3086_,
                                                                    v_a_3087_,
                                                                );
                                                            if crate::leanh::lean_obj_tag(
                                                                v___x_3161_,
                                                            ) == 0
                                                            {
                                                                v_a_3162_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v___x_3161_,
                                                                        0,
                                                                    );
                                                                v_isSharedCheck_3194_ = (!crate::leanh::lean_is_exclusive(v___x_3161_)) as u8;
                                                                if v_isSharedCheck_3194_ == 0 {
                                                                    v___x_3164_ = v___x_3161_;
                                                                    v_isShared_3165_ =
                                                                        v_isSharedCheck_3194_;
                                                                    state = 8;
                                                                    continue;
                                                                } else {
                                                                    crate::leanh::lean_inc(
                                                                        v_a_3162_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v___x_3161_,
                                                                    );
                                                                    v___x_3164_ =
                                                                        crate::leanh::lean_box(0);
                                                                    v_isShared_3165_ =
                                                                        v_isSharedCheck_3194_;
                                                                    state = 8;
                                                                    continue;
                                                                }
                                                            } else {
                                                                crate::leanh::lean_dec_ref_known(
                                                                    v_t_3080_, 3,
                                                                );
                                                                v_a_3195_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v___x_3161_,
                                                                        0,
                                                                    );
                                                                v_isSharedCheck_3202_ = (!crate::leanh::lean_is_exclusive(v___x_3161_)) as u8;
                                                                if v_isSharedCheck_3202_ == 0 {
                                                                    v___x_3197_ = v___x_3161_;
                                                                    v_isShared_3198_ =
                                                                        v_isSharedCheck_3202_;
                                                                    state = 10;
                                                                    continue;
                                                                } else {
                                                                    crate::leanh::lean_inc(
                                                                        v_a_3195_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v___x_3161_,
                                                                    );
                                                                    v___x_3197_ =
                                                                        crate::leanh::lean_box(0);
                                                                    v_isShared_3198_ =
                                                                        v_isSharedCheck_3202_;
                                                                    state = 10;
                                                                    continue;
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        } else {
                                            crate::leanh::lean_inc_ref(v_kind_3093_);
                                            crate::leanh::lean_inc_ref(v_args_3094_);
                                            crate::leanh::lean_inc(v_info_3092_);
                                            crate::leanh::lean_dec_ref_known(v_t_3080_, 3);
                                            v_k_3096_ = v_kind_3093_;
                                            v___y_3097_ = v_a_3081_;
                                            v___y_3098_ = v_a_3082_;
                                            v___y_3099_ = v_a_3083_;
                                            v___y_3100_ = v_a_3084_;
                                            v___y_3101_ = v_a_3085_;
                                            v___y_3102_ = v_a_3086_;
                                            v___y_3103_ = v_a_3087_;
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_inc_ref(v_kind_3093_);
                                        crate::leanh::lean_inc_ref(v_args_3094_);
                                        crate::leanh::lean_inc(v_info_3092_);
                                        crate::leanh::lean_dec_ref_known(v_t_3080_, 3);
                                        v_k_3096_ = v_kind_3093_;
                                        v___y_3097_ = v_a_3081_;
                                        v___y_3098_ = v_a_3082_;
                                        v___y_3099_ = v_a_3083_;
                                        v___y_3100_ = v_a_3084_;
                                        v___y_3101_ = v_a_3085_;
                                        v___y_3102_ = v_a_3086_;
                                        v___y_3103_ = v_a_3087_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_inc_ref(v_kind_3093_);
                                    crate::leanh::lean_inc_ref(v_args_3094_);
                                    crate::leanh::lean_inc(v_info_3092_);
                                    crate::leanh::lean_dec_ref_known(v_t_3080_, 3);
                                    v_k_3096_ = v_kind_3093_;
                                    v___y_3097_ = v_a_3081_;
                                    v___y_3098_ = v_a_3082_;
                                    v___y_3099_ = v_a_3083_;
                                    v___y_3100_ = v_a_3084_;
                                    v___y_3101_ = v_a_3085_;
                                    v___y_3102_ = v_a_3086_;
                                    v___y_3103_ = v_a_3087_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_inc_ref(v_kind_3093_);
                                crate::leanh::lean_inc_ref(v_args_3094_);
                                crate::leanh::lean_inc(v_info_3092_);
                                crate::leanh::lean_dec_ref_known(v_t_3080_, 3);
                                v_k_3096_ = v_kind_3093_;
                                v___y_3097_ = v_a_3081_;
                                v___y_3098_ = v_a_3082_;
                                v___y_3099_ = v_a_3083_;
                                v___y_3100_ = v_a_3084_;
                                v___y_3101_ = v_a_3085_;
                                v___y_3102_ = v_a_3086_;
                                v___y_3103_ = v_a_3087_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_inc_ref(v_args_3094_);
                            crate::leanh::lean_inc(v_kind_3093_);
                            crate::leanh::lean_inc(v_info_3092_);
                            crate::leanh::lean_dec_ref_known(v_t_3080_, 3);
                            v_k_3096_ = v_kind_3093_;
                            v___y_3097_ = v_a_3081_;
                            v___y_3098_ = v_a_3082_;
                            v___y_3099_ = v_a_3083_;
                            v___y_3100_ = v_a_3084_;
                            v___y_3101_ = v_a_3085_;
                            v___y_3102_ = v_a_3086_;
                            v___y_3103_ = v_a_3087_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_type_3079_);
                        v___x_3203_ = 0;
                        v___x_3204_ = crate::leanh::lean_box((v___x_3203_) as usize);
                        v___x_3205_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3205_, 0, v_t_3080_);
                        crate::leanh::lean_ctor_set(v___x_3205_, 1, v___x_3204_);
                        v___x_3206_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3206_, 0, v___x_3205_);
                        return v___x_3206_;
                    }
                }
            }
            1 => {
                v_sz_3104_ = lean_array_size(v_args_3094_);
                v___x_3105_ = 0usize;
                v___x_3106_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go_spec__0(v_type_3079_, v_sz_3104_, v___x_3105_, v_args_3094_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_);
                if crate::leanh::lean_obj_tag(v___x_3106_) == 0 {
                    v_a_3107_ = crate::leanh::lean_ctor_get(v___x_3106_, 0);
                    v_isSharedCheck_3124_ = (!crate::leanh::lean_is_exclusive(v___x_3106_)) as u8;
                    if v_isSharedCheck_3124_ == 0 {
                        v___x_3109_ = v___x_3106_;
                        v_isShared_3110_ = v_isSharedCheck_3124_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3107_);
                        crate::leanh::lean_dec(v___x_3106_);
                        v___x_3109_ = crate::leanh::lean_box(0);
                        v_isShared_3110_ = v_isSharedCheck_3124_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_k_3096_);
                    crate::leanh::lean_dec(v_info_3092_);
                    v_a_3125_ = crate::leanh::lean_ctor_get(v___x_3106_, 0);
                    v_isSharedCheck_3132_ = (!crate::leanh::lean_is_exclusive(v___x_3106_)) as u8;
                    if v_isSharedCheck_3132_ == 0 {
                        v___x_3127_ = v___x_3106_;
                        v_isShared_3128_ = v_isSharedCheck_3132_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3125_);
                        crate::leanh::lean_dec(v___x_3106_);
                        v___x_3127_ = crate::leanh::lean_box(0);
                        v_isShared_3128_ = v_isSharedCheck_3132_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_3111_ = crate::leanh::lean_ctor_get(v_a_3107_, 0);
                v_snd_3112_ = crate::leanh::lean_ctor_get(v_a_3107_, 1);
                v_isSharedCheck_3123_ = (!crate::leanh::lean_is_exclusive(v_a_3107_)) as u8;
                if v_isSharedCheck_3123_ == 0 {
                    v___x_3114_ = v_a_3107_;
                    v_isShared_3115_ = v_isSharedCheck_3123_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3112_);
                    crate::leanh::lean_inc(v_fst_3111_);
                    crate::leanh::lean_dec(v_a_3107_);
                    v___x_3114_ = crate::leanh::lean_box(0);
                    v_isShared_3115_ = v_isSharedCheck_3123_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3116_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3116_, 0, v_info_3092_);
                crate::leanh::lean_ctor_set(v___x_3116_, 1, v_k_3096_);
                crate::leanh::lean_ctor_set(v___x_3116_, 2, v_fst_3111_);
                if v_isShared_3115_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3114_, 0, v___x_3116_);
                    v___x_3118_ = v___x_3114_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3122_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3122_, 0, v___x_3116_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3122_, 1, v_snd_3112_);
                    v___x_3118_ = v_reuseFailAlloc_3122_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3110_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3109_, 0, v___x_3118_);
                    v___x_3120_ = v___x_3109_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3121_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3121_, 0, v___x_3118_);
                    v___x_3120_ = v_reuseFailAlloc_3121_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3120_;
            }
            6 => {
                if v_isShared_3128_ == 0 {
                    v___x_3130_ = v___x_3127_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3131_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3131_, 0, v_a_3125_);
                    v___x_3130_ = v_reuseFailAlloc_3131_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3130_;
            }
            8 => {
                v_ref_3166_ = crate::leanh::lean_ctor_get(v_a_3086_, 5);
                v_quotContext_3167_ = crate::leanh::lean_ctor_get(v_a_3086_, 10);
                v_currMacroScope_3168_ = crate::leanh::lean_ctor_get(v_a_3086_, 11);
                v___x_3169_ = 0;
                v___x_3170_ = l_Lean_SourceInfo_fromRef(v_ref_3166_, v___x_3169_);
                v___x_3171_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__5;
                v___x_3172_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__7;
                v___x_3173_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__8;
                crate::leanh::lean_inc_n(v___x_3170_, 7);
                v___x_3174_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3174_, 0, v___x_3170_);
                crate::leanh::lean_ctor_set(v___x_3174_, 1, v___x_3173_);
                v___x_3175_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__10;
                v___x_3176_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__12), core::ptr::addr_of_mut!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__12_once), _init_l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__12);
                crate::leanh::lean_inc(v_currMacroScope_3168_);
                crate::leanh::lean_inc(v_quotContext_3167_);
                v___x_3177_ =
                    l_Lean_addMacroScope(v_quotContext_3167_, v_pre_3136_, v_currMacroScope_3168_);
                v___x_3178_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__20;
                v___x_3179_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3179_, 0, v___x_3170_);
                crate::leanh::lean_ctor_set(v___x_3179_, 1, v___x_3176_);
                crate::leanh::lean_ctor_set(v___x_3179_, 2, v___x_3177_);
                crate::leanh::lean_ctor_set(v___x_3179_, 3, v___x_3178_);
                v___x_3180_ = l_Lean_Syntax_node1(v___x_3170_, v___x_3175_, v___x_3179_);
                v___x_3181_ =
                    l_Lean_Syntax_node2(v___x_3170_, v___x_3172_, v___x_3174_, v___x_3180_);
                v___x_3182_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__21;
                v___x_3183_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3183_, 0, v___x_3170_);
                crate::leanh::lean_ctor_set(v___x_3183_, 1, v___x_3182_);
                v___x_3184_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__23;
                v___x_3185_ = l_Lean_Syntax_node1(v___x_3170_, v___x_3184_, v_a_3162_);
                v___x_3186_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__24;
                v___x_3187_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3187_, 0, v___x_3170_);
                crate::leanh::lean_ctor_set(v___x_3187_, 1, v___x_3186_);
                v___x_3188_ = l_Lean_Syntax_node5(
                    v___x_3170_,
                    v___x_3171_,
                    v___x_3181_,
                    v_t_3080_,
                    v___x_3183_,
                    v___x_3185_,
                    v___x_3187_,
                );
                v___x_3189_ = crate::leanh::lean_box((v___x_3169_) as usize);
                v___x_3190_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3190_, 0, v___x_3188_);
                crate::leanh::lean_ctor_set(v___x_3190_, 1, v___x_3189_);
                if v_isShared_3165_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3164_, 0, v___x_3190_);
                    v___x_3192_ = v___x_3164_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3193_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3193_, 0, v___x_3190_);
                    v___x_3192_ = v_reuseFailAlloc_3193_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3192_;
            }
            10 => {
                if v_isShared_3198_ == 0 {
                    v___x_3200_ = v___x_3197_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3201_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3201_, 0, v_a_3195_);
                    v___x_3200_ = v_reuseFailAlloc_3201_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3200_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go_spec__0(
    mut v_type_3207_: *mut crate::leanh::LeanObject,
    mut v_sz_3208_: usize,
    mut v_i_3209_: usize,
    mut v_bs_3210_: *mut crate::leanh::LeanObject,
    mut v___y_3211_: u8,
    mut v___y_3212_: *mut crate::leanh::LeanObject,
    mut v___y_3213_: *mut crate::leanh::LeanObject,
    mut v___y_3214_: *mut crate::leanh::LeanObject,
    mut v___y_3215_: *mut crate::leanh::LeanObject,
    mut v___y_3216_: *mut crate::leanh::LeanObject,
    mut v___y_3217_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3219_: u8 = 0;
    let mut v___x_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: usize = 0;
    let mut v___x_3231_: usize = 0;
    let mut v___x_3232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: u8 = 0;
    let mut v_a_3235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3238_: u8 = 0;
    let mut v___x_3240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3242_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3219_ = lean_usize_dec_lt(v_i_3209_, v_sz_3208_);
                if v___x_3219_ == 0 {
                    crate::leanh::lean_dec_ref(v_type_3207_);
                    v___x_3220_ = crate::leanh::lean_box((v___y_3211_) as usize);
                    v___x_3221_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3221_, 0, v_bs_3210_);
                    crate::leanh::lean_ctor_set(v___x_3221_, 1, v___x_3220_);
                    v___x_3222_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3222_, 0, v___x_3221_);
                    return v___x_3222_;
                } else {
                    v_v_3223_ = lean_array_uget_borrowed(v_bs_3210_, v_i_3209_);
                    crate::leanh::lean_inc(v_v_3223_);
                    crate::leanh::lean_inc_ref(v_type_3207_);
                    v___x_3224_ =
                        l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go(
                            v_type_3207_,
                            v_v_3223_,
                            v___y_3211_,
                            v___y_3212_,
                            v___y_3213_,
                            v___y_3214_,
                            v___y_3215_,
                            v___y_3216_,
                            v___y_3217_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_3224_) == 0 {
                        v_a_3225_ = crate::leanh::lean_ctor_get(v___x_3224_, 0);
                        crate::leanh::lean_inc(v_a_3225_);
                        crate::leanh::lean_dec_ref_known(v___x_3224_, 1);
                        v_fst_3226_ = crate::leanh::lean_ctor_get(v_a_3225_, 0);
                        crate::leanh::lean_inc(v_fst_3226_);
                        v_snd_3227_ = crate::leanh::lean_ctor_get(v_a_3225_, 1);
                        crate::leanh::lean_inc(v_snd_3227_);
                        crate::leanh::lean_dec(v_a_3225_);
                        v___x_3228_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_3229_ = lean_array_uset(v_bs_3210_, v_i_3209_, v___x_3228_);
                        v___x_3230_ = 1usize;
                        v___x_3231_ = lean_usize_add(v_i_3209_, v___x_3230_);
                        v___x_3232_ = lean_array_uset(v_bs_x27_3229_, v_i_3209_, v_fst_3226_);
                        v___x_3233_ = (crate::leanh::lean_unbox(v_snd_3227_) as u8);
                        crate::leanh::lean_dec(v_snd_3227_);
                        v_i_3209_ = v___x_3231_;
                        v_bs_3210_ = v___x_3232_;
                        v___y_3211_ = v___x_3233_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_bs_3210_);
                        crate::leanh::lean_dec_ref(v_type_3207_);
                        v_a_3235_ = crate::leanh::lean_ctor_get(v___x_3224_, 0);
                        v_isSharedCheck_3242_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3224_)) as u8;
                        if v_isSharedCheck_3242_ == 0 {
                            v___x_3237_ = v___x_3224_;
                            v_isShared_3238_ = v_isSharedCheck_3242_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3235_);
                            crate::leanh::lean_dec(v___x_3224_);
                            v___x_3237_ = crate::leanh::lean_box(0);
                            v_isShared_3238_ = v_isSharedCheck_3242_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3238_ == 0 {
                    v___x_3240_ = v___x_3237_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3241_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3241_, 0, v_a_3235_);
                    v___x_3240_ = v_reuseFailAlloc_3241_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3240_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go_spec__0___boxed(
    mut v_type_3243_: *mut crate::leanh::LeanObject,
    mut v_sz_3244_: *mut crate::leanh::LeanObject,
    mut v_i_3245_: *mut crate::leanh::LeanObject,
    mut v_bs_3246_: *mut crate::leanh::LeanObject,
    mut v___y_3247_: *mut crate::leanh::LeanObject,
    mut v___y_3248_: *mut crate::leanh::LeanObject,
    mut v___y_3249_: *mut crate::leanh::LeanObject,
    mut v___y_3250_: *mut crate::leanh::LeanObject,
    mut v___y_3251_: *mut crate::leanh::LeanObject,
    mut v___y_3252_: *mut crate::leanh::LeanObject,
    mut v___y_3253_: *mut crate::leanh::LeanObject,
    mut v___y_3254_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3255_: usize = 0;
    let mut v_i_boxed_3256_: usize = 0;
    let mut v___y_7883__boxed_3257_: u8 = 0;
    let mut v_res_3258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3255_ = crate::leanh::lean_unbox_usize(v_sz_3244_);
    crate::leanh::lean_dec(v_sz_3244_);
    v_i_boxed_3256_ = crate::leanh::lean_unbox_usize(v_i_3245_);
    crate::leanh::lean_dec(v_i_3245_);
    v___y_7883__boxed_3257_ = (crate::leanh::lean_unbox(v___y_3247_) as u8);
    v_res_3258_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go_spec__0(v_type_3243_, v_sz_boxed_3255_, v_i_boxed_3256_, v_bs_3246_, v___y_7883__boxed_3257_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_);
    crate::leanh::lean_dec(v___y_3253_);
    crate::leanh::lean_dec_ref(v___y_3252_);
    crate::leanh::lean_dec(v___y_3251_);
    crate::leanh::lean_dec_ref(v___y_3250_);
    crate::leanh::lean_dec(v___y_3249_);
    crate::leanh::lean_dec_ref(v___y_3248_);
    return v_res_3258_;
}
pub unsafe fn l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___boxed(
    mut v_type_3259_: *mut crate::leanh::LeanObject,
    mut v_t_3260_: *mut crate::leanh::LeanObject,
    mut v_a_3261_: *mut crate::leanh::LeanObject,
    mut v_a_3262_: *mut crate::leanh::LeanObject,
    mut v_a_3263_: *mut crate::leanh::LeanObject,
    mut v_a_3264_: *mut crate::leanh::LeanObject,
    mut v_a_3265_: *mut crate::leanh::LeanObject,
    mut v_a_3266_: *mut crate::leanh::LeanObject,
    mut v_a_3267_: *mut crate::leanh::LeanObject,
    mut v_a_3268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_7952__boxed_3269_: u8 = 0;
    let mut v_res_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_7952__boxed_3269_ = (crate::leanh::lean_unbox(v_a_3261_) as u8);
    v_res_3270_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go(
        v_type_3259_,
        v_t_3260_,
        v_a_7952__boxed_3269_,
        v_a_3262_,
        v_a_3263_,
        v_a_3264_,
        v_a_3265_,
        v_a_3266_,
        v_a_3267_,
    );
    crate::leanh::lean_dec(v_a_3267_);
    crate::leanh::lean_dec_ref(v_a_3266_);
    crate::leanh::lean_dec(v_a_3265_);
    crate::leanh::lean_dec_ref(v_a_3264_);
    crate::leanh::lean_dec(v_a_3263_);
    crate::leanh::lean_dec_ref(v_a_3262_);
    return v_res_3270_;
}
pub unsafe fn l_Lean_Elab_Term_annotateFirstHoleWithType(
    mut v_t_3271_: *mut crate::leanh::LeanObject,
    mut v_type_3272_: *mut crate::leanh::LeanObject,
    mut v_a_3273_: *mut crate::leanh::LeanObject,
    mut v_a_3274_: *mut crate::leanh::LeanObject,
    mut v_a_3275_: *mut crate::leanh::LeanObject,
    mut v_a_3276_: *mut crate::leanh::LeanObject,
    mut v_a_3277_: *mut crate::leanh::LeanObject,
    mut v_a_3278_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3280_: u8 = 0;
    let mut v___x_3281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3285_: u8 = 0;
    let mut v_fst_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3290_: u8 = 0;
    let mut v_a_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3294_: u8 = 0;
    let mut v___x_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3298_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3280_ = 1;
                v___x_3281_ =
                    l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go(
                        v_type_3272_,
                        v_t_3271_,
                        v___x_3280_,
                        v_a_3273_,
                        v_a_3274_,
                        v_a_3275_,
                        v_a_3276_,
                        v_a_3277_,
                        v_a_3278_,
                    );
                if crate::leanh::lean_obj_tag(v___x_3281_) == 0 {
                    v_a_3282_ = crate::leanh::lean_ctor_get(v___x_3281_, 0);
                    v_isSharedCheck_3290_ = (!crate::leanh::lean_is_exclusive(v___x_3281_)) as u8;
                    if v_isSharedCheck_3290_ == 0 {
                        v___x_3284_ = v___x_3281_;
                        v_isShared_3285_ = v_isSharedCheck_3290_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3282_);
                        crate::leanh::lean_dec(v___x_3281_);
                        v___x_3284_ = crate::leanh::lean_box(0);
                        v_isShared_3285_ = v_isSharedCheck_3290_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3291_ = crate::leanh::lean_ctor_get(v___x_3281_, 0);
                    v_isSharedCheck_3298_ = (!crate::leanh::lean_is_exclusive(v___x_3281_)) as u8;
                    if v_isSharedCheck_3298_ == 0 {
                        v___x_3293_ = v___x_3281_;
                        v_isShared_3294_ = v_isSharedCheck_3298_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3291_);
                        crate::leanh::lean_dec(v___x_3281_);
                        v___x_3293_ = crate::leanh::lean_box(0);
                        v_isShared_3294_ = v_isSharedCheck_3298_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3286_ = crate::leanh::lean_ctor_get(v_a_3282_, 0);
                crate::leanh::lean_inc(v_fst_3286_);
                crate::leanh::lean_dec(v_a_3282_);
                if v_isShared_3285_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3284_, 0, v_fst_3286_);
                    v___x_3288_ = v___x_3284_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3289_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3289_, 0, v_fst_3286_);
                    v___x_3288_ = v_reuseFailAlloc_3289_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3288_;
            }
            3 => {
                if v_isShared_3294_ == 0 {
                    v___x_3296_ = v___x_3293_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3297_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3297_, 0, v_a_3291_);
                    v___x_3296_ = v_reuseFailAlloc_3297_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3296_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_annotateFirstHoleWithType___boxed(
    mut v_t_3299_: *mut crate::leanh::LeanObject,
    mut v_type_3300_: *mut crate::leanh::LeanObject,
    mut v_a_3301_: *mut crate::leanh::LeanObject,
    mut v_a_3302_: *mut crate::leanh::LeanObject,
    mut v_a_3303_: *mut crate::leanh::LeanObject,
    mut v_a_3304_: *mut crate::leanh::LeanObject,
    mut v_a_3305_: *mut crate::leanh::LeanObject,
    mut v_a_3306_: *mut crate::leanh::LeanObject,
    mut v_a_3307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3308_ = l_Lean_Elab_Term_annotateFirstHoleWithType(
        v_t_3299_,
        v_type_3300_,
        v_a_3301_,
        v_a_3302_,
        v_a_3303_,
        v_a_3304_,
        v_a_3305_,
        v_a_3306_,
    );
    crate::leanh::lean_dec(v_a_3306_);
    crate::leanh::lean_dec_ref(v_a_3305_);
    crate::leanh::lean_dec(v_a_3304_);
    crate::leanh::lean_dec_ref(v_a_3303_);
    crate::leanh::lean_dec(v_a_3302_);
    crate::leanh::lean_dec_ref(v_a_3301_);
    return v_res_3308_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3313_ = crate::leanh::lean_box(0);
    v___x_3314_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_3315_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3315_, 0, v___x_3314_);
    crate::leanh::lean_ctor_set(v___x_3315_, 1, v___x_3313_);
    return v___x_3315_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3317_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg___closed__0);
    v___x_3318_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3318_, 0, v___x_3317_);
    return v___x_3318_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg___boxed(
    mut v___y_3319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3320_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
    return v_res_3320_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0(
    mut v_00_u03b1_3321_: *mut crate::leanh::LeanObject,
    mut v___y_3322_: *mut crate::leanh::LeanObject,
    mut v___y_3323_: *mut crate::leanh::LeanObject,
    mut v___y_3324_: *mut crate::leanh::LeanObject,
    mut v___y_3325_: *mut crate::leanh::LeanObject,
    mut v___y_3326_: *mut crate::leanh::LeanObject,
    mut v___y_3327_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3329_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
    return v___x_3329_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___boxed(
    mut v_00_u03b1_3330_: *mut crate::leanh::LeanObject,
    mut v___y_3331_: *mut crate::leanh::LeanObject,
    mut v___y_3332_: *mut crate::leanh::LeanObject,
    mut v___y_3333_: *mut crate::leanh::LeanObject,
    mut v___y_3334_: *mut crate::leanh::LeanObject,
    mut v___y_3335_: *mut crate::leanh::LeanObject,
    mut v___y_3336_: *mut crate::leanh::LeanObject,
    mut v___y_3337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3338_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0(
            v_00_u03b1_3330_,
            v___y_3331_,
            v___y_3332_,
            v___y_3333_,
            v___y_3334_,
            v___y_3335_,
            v___y_3336_,
        );
    crate::leanh::lean_dec(v___y_3336_);
    crate::leanh::lean_dec_ref(v___y_3335_);
    crate::leanh::lean_dec(v___y_3334_);
    crate::leanh::lean_dec_ref(v___y_3333_);
    crate::leanh::lean_dec(v___y_3332_);
    crate::leanh::lean_dec_ref(v___y_3331_);
    return v_res_3338_;
}
pub unsafe fn _init_l_Lean_Elab_Term_mkCalcFirstStepView___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3354_ = l_Lean_Elab_Term_mkCalcFirstStepView___closed__7;
    v___x_3355_ = l_String_toRawSubstring_x27(v___x_3354_);
    return v___x_3355_;
}
pub unsafe fn l_Lean_Elab_Term_mkCalcFirstStepView(
    mut v_step0_3364_: *mut crate::leanh::LeanObject,
    mut v_a_3365_: *mut crate::leanh::LeanObject,
    mut v_a_3366_: *mut crate::leanh::LeanObject,
    mut v_a_3367_: *mut crate::leanh::LeanObject,
    mut v_a_3368_: *mut crate::leanh::LeanObject,
    mut v_a_3369_: *mut crate::leanh::LeanObject,
    mut v_a_3370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_3372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: u8 = 0;
    v_ref_3372_ = crate::leanh::lean_ctor_get(v_a_3369_, 5);
    v_quotContext_3373_ = crate::leanh::lean_ctor_get(v_a_3369_, 10);
    v_currMacroScope_3374_ = crate::leanh::lean_ctor_get(v_a_3369_, 11);
    v___x_3375_ = l_Lean_Elab_Term_mkCalcFirstStepView___closed__1;
    crate::leanh::lean_inc(v_step0_3364_);
    v___x_3376_ = l_Lean_Syntax_isOfKind(v_step0_3364_, v___x_3375_);
    if v___x_3376_ == 0 {
        let mut v___x_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_step0_3364_);
        v___x_3377_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
        return v___x_3377_;
    } else {
        let mut v___x_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_term_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3382_: u8 = 0;
        v___x_3378_ = crate::leanh::lean_unsigned_to_nat(0);
        v_term_3379_ = l_Lean_Syntax_getArg(v_step0_3364_, v___x_3378_);
        v___x_3380_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_3381_ = l_Lean_Syntax_getArg(v_step0_3364_, v___x_3380_);
        crate::leanh::lean_inc(v___x_3381_);
        v___x_3382_ = l_Lean_Syntax_matchesNull(v___x_3381_, v___x_3378_);
        if v___x_3382_ == 0 {
            let mut v___x_3383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3384_: u8 = 0;
            v___x_3383_ = crate::leanh::lean_unsigned_to_nat(2);
            crate::leanh::lean_inc(v___x_3381_);
            v___x_3384_ = l_Lean_Syntax_matchesNull(v___x_3381_, v___x_3383_);
            if v___x_3384_ == 0 {
                let mut v___x_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v___x_3381_);
                crate::leanh::lean_dec(v_term_3379_);
                crate::leanh::lean_dec(v_step0_3364_);
                v___x_3385_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
                return v___x_3385_;
            } else {
                let mut v_proof_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_proof_3386_ = l_Lean_Syntax_getArg(v___x_3381_, v___x_3380_);
                crate::leanh::lean_dec(v___x_3381_);
                v___x_3387_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3387_, 0, v_step0_3364_);
                crate::leanh::lean_ctor_set(v___x_3387_, 1, v_term_3379_);
                crate::leanh::lean_ctor_set(v___x_3387_, 2, v_proof_3386_);
                v___x_3388_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3388_, 0, v___x_3387_);
                return v___x_3388_;
            }
        } else {
            let mut v_ref_3389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3390_: u8 = 0;
            let mut v___x_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_3381_);
            v_ref_3389_ = l_Lean_replaceRef(v_step0_3364_, v_ref_3372_);
            v___x_3390_ = 0;
            v___x_3391_ = l_Lean_SourceInfo_fromRef(v_ref_3389_, v___x_3390_);
            crate::leanh::lean_dec(v_ref_3389_);
            v___x_3392_ = l_Lean_Elab_Term_mkCalcFirstStepView___closed__3;
            v___x_3393_ = l_Lean_Elab_Term_mkCalcFirstStepView___closed__4;
            crate::leanh::lean_inc_n(v___x_3391_, 4);
            v___x_3394_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_3394_, 0, v___x_3391_);
            crate::leanh::lean_ctor_set(v___x_3394_, 1, v___x_3393_);
            v___x_3395_ = l_Lean_Elab_Term_mkCalcFirstStepView___closed__5;
            v___x_3396_ = l_Lean_Elab_Term_mkCalcFirstStepView___closed__6;
            v___x_3397_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_3397_, 0, v___x_3391_);
            crate::leanh::lean_ctor_set(v___x_3397_, 1, v___x_3396_);
            v___x_3398_ = l_Lean_Syntax_node1(v___x_3391_, v___x_3395_, v___x_3397_);
            v___x_3399_ = l_Lean_Syntax_node3(
                v___x_3391_,
                v___x_3392_,
                v_term_3379_,
                v___x_3394_,
                v___x_3398_,
            );
            v___x_3400_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Elab_Term_mkCalcFirstStepView___closed__8),
                core::ptr::addr_of_mut!(l_Lean_Elab_Term_mkCalcFirstStepView___closed__8_once),
                _init_l_Lean_Elab_Term_mkCalcFirstStepView___closed__8,
            );
            v___x_3401_ = l_Lean_Elab_Term_mkCalcFirstStepView___closed__9;
            crate::leanh::lean_inc(v_currMacroScope_3374_);
            crate::leanh::lean_inc(v_quotContext_3373_);
            v___x_3402_ =
                l_Lean_addMacroScope(v_quotContext_3373_, v___x_3401_, v_currMacroScope_3374_);
            v___x_3403_ = l_Lean_Elab_Term_mkCalcFirstStepView___closed__11;
            v___x_3404_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_3404_, 0, v___x_3391_);
            crate::leanh::lean_ctor_set(v___x_3404_, 1, v___x_3400_);
            crate::leanh::lean_ctor_set(v___x_3404_, 2, v___x_3402_);
            crate::leanh::lean_ctor_set(v___x_3404_, 3, v___x_3403_);
            v___x_3405_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_3405_, 0, v_step0_3364_);
            crate::leanh::lean_ctor_set(v___x_3405_, 1, v___x_3399_);
            crate::leanh::lean_ctor_set(v___x_3405_, 2, v___x_3404_);
            v___x_3406_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_3406_, 0, v___x_3405_);
            return v___x_3406_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_mkCalcFirstStepView___boxed(
    mut v_step0_3407_: *mut crate::leanh::LeanObject,
    mut v_a_3408_: *mut crate::leanh::LeanObject,
    mut v_a_3409_: *mut crate::leanh::LeanObject,
    mut v_a_3410_: *mut crate::leanh::LeanObject,
    mut v_a_3411_: *mut crate::leanh::LeanObject,
    mut v_a_3412_: *mut crate::leanh::LeanObject,
    mut v_a_3413_: *mut crate::leanh::LeanObject,
    mut v_a_3414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3415_ = l_Lean_Elab_Term_mkCalcFirstStepView(
        v_step0_3407_,
        v_a_3408_,
        v_a_3409_,
        v_a_3410_,
        v_a_3411_,
        v_a_3412_,
        v_a_3413_,
    );
    crate::leanh::lean_dec(v_a_3413_);
    crate::leanh::lean_dec_ref(v_a_3412_);
    crate::leanh::lean_dec(v_a_3411_);
    crate::leanh::lean_dec_ref(v_a_3410_);
    crate::leanh::lean_dec(v_a_3409_);
    crate::leanh::lean_dec_ref(v_a_3408_);
    return v_res_3415_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg(
    mut v_as_3420_: *mut crate::leanh::LeanObject,
    mut v_sz_3421_: usize,
    mut v_i_3422_: usize,
    mut v_b_3423_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: usize = 0;
    let mut v___x_3428_: usize = 0;
    let mut v___x_3430_: u8 = 0;
    let mut v___x_3431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: u8 = 0;
    let mut v___x_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3439_: u8 = 0;
    let mut v___x_3441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3443_: u8 = 0;
    let mut v___x_3444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3430_ = lean_usize_dec_lt(v_i_3422_, v_sz_3421_);
                if v___x_3430_ == 0 {
                    v___x_3431_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3431_, 0, v_b_3423_);
                    return v___x_3431_;
                } else {
                    v___x_3432_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg___closed__1;
                    v_a_3433_ = lean_array_uget_borrowed(v_as_3420_, v_i_3422_);
                    crate::leanh::lean_inc(v_a_3433_);
                    v___x_3434_ = l_Lean_Syntax_isOfKind(v_a_3433_, v___x_3432_);
                    if v___x_3434_ == 0 {
                        v___x_3435_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
                        if crate::leanh::lean_obj_tag(v___x_3435_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_3435_, 1);
                            v_a_3426_ = v_b_3423_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_b_3423_);
                            v_a_3436_ = crate::leanh::lean_ctor_get(v___x_3435_, 0);
                            v_isSharedCheck_3443_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3435_)) as u8;
                            if v_isSharedCheck_3443_ == 0 {
                                v___x_3438_ = v___x_3435_;
                                v_isShared_3439_ = v_isSharedCheck_3443_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3436_);
                                crate::leanh::lean_dec(v___x_3435_);
                                v___x_3438_ = crate::leanh::lean_box(0);
                                v_isShared_3439_ = v_isSharedCheck_3443_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        v___x_3444_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_3445_ = l_Lean_Syntax_getArg(v_a_3433_, v___x_3444_);
                        v___x_3446_ = crate::leanh::lean_unsigned_to_nat(2);
                        v___x_3447_ = l_Lean_Syntax_getArg(v_a_3433_, v___x_3446_);
                        crate::leanh::lean_inc(v_a_3433_);
                        v___x_3448_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3448_, 0, v_a_3433_);
                        crate::leanh::lean_ctor_set(v___x_3448_, 1, v___x_3445_);
                        crate::leanh::lean_ctor_set(v___x_3448_, 2, v___x_3447_);
                        v___x_3449_ = lean_array_push(v_b_3423_, v___x_3448_);
                        v_a_3426_ = v___x_3449_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3427_ = 1usize;
                v___x_3428_ = lean_usize_add(v_i_3422_, v___x_3427_);
                v_i_3422_ = v___x_3428_;
                v_b_3423_ = v_a_3426_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_3439_ == 0 {
                    v___x_3441_ = v___x_3438_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3442_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3442_, 0, v_a_3436_);
                    v___x_3441_ = v_reuseFailAlloc_3442_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3441_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg___boxed(
    mut v_as_3450_: *mut crate::leanh::LeanObject,
    mut v_sz_3451_: *mut crate::leanh::LeanObject,
    mut v_i_3452_: *mut crate::leanh::LeanObject,
    mut v_b_3453_: *mut crate::leanh::LeanObject,
    mut v___y_3454_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3455_: usize = 0;
    let mut v_i_boxed_3456_: usize = 0;
    let mut v_res_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3455_ = crate::leanh::lean_unbox_usize(v_sz_3451_);
    crate::leanh::lean_dec(v_sz_3451_);
    v_i_boxed_3456_ = crate::leanh::lean_unbox_usize(v_i_3452_);
    crate::leanh::lean_dec(v_i_3452_);
    v_res_3457_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg(v_as_3450_, v_sz_boxed_3455_, v_i_boxed_3456_, v_b_3453_);
    crate::leanh::lean_dec_ref(v_as_3450_);
    return v_res_3457_;
}
pub unsafe fn l_Lean_Elab_Term_mkCalcStepViews(
    mut v_steps_3462_: *mut crate::leanh::LeanObject,
    mut v_a_3463_: *mut crate::leanh::LeanObject,
    mut v_a_3464_: *mut crate::leanh::LeanObject,
    mut v_a_3465_: *mut crate::leanh::LeanObject,
    mut v_a_3466_: *mut crate::leanh::LeanObject,
    mut v_a_3467_: *mut crate::leanh::LeanObject,
    mut v_a_3468_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: u8 = 0;
    let mut v___x_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_step0_3474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: u8 = 0;
    let mut v___x_3477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rest_3482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3485_: usize = 0;
    let mut v___x_3486_: usize = 0;
    let mut v___x_3487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3491_: u8 = 0;
    let mut v___x_3493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3495_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3470_ = l_Lean_Elab_Term_mkCalcStepViews___closed__1;
                crate::leanh::lean_inc(v_steps_3462_);
                v___x_3471_ = l_Lean_Syntax_isOfKind(v_steps_3462_, v___x_3470_);
                if v___x_3471_ == 0 {
                    crate::leanh::lean_dec(v_steps_3462_);
                    v___x_3472_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
                    return v___x_3472_;
                } else {
                    v___x_3473_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_step0_3474_ = l_Lean_Syntax_getArg(v_steps_3462_, v___x_3473_);
                    v___x_3475_ = l_Lean_Elab_Term_mkCalcFirstStepView___closed__1;
                    crate::leanh::lean_inc(v_step0_3474_);
                    v___x_3476_ = l_Lean_Syntax_isOfKind(v_step0_3474_, v___x_3475_);
                    if v___x_3476_ == 0 {
                        crate::leanh::lean_dec(v_step0_3474_);
                        crate::leanh::lean_dec(v_steps_3462_);
                        v___x_3477_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
                        return v___x_3477_;
                    } else {
                        v___x_3478_ = l_Lean_Elab_Term_mkCalcFirstStepView(
                            v_step0_3474_,
                            v_a_3463_,
                            v_a_3464_,
                            v_a_3465_,
                            v_a_3466_,
                            v_a_3467_,
                            v_a_3468_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3478_) == 0 {
                            v_a_3479_ = crate::leanh::lean_ctor_get(v___x_3478_, 0);
                            crate::leanh::lean_inc(v_a_3479_);
                            crate::leanh::lean_dec_ref_known(v___x_3478_, 1);
                            v___x_3480_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_3481_ = l_Lean_Syntax_getArg(v_steps_3462_, v___x_3480_);
                            crate::leanh::lean_dec(v_steps_3462_);
                            v_rest_3482_ = l_Lean_Syntax_getArgs(v___x_3481_);
                            crate::leanh::lean_dec(v___x_3481_);
                            v___x_3483_ = lean_mk_empty_array_with_capacity(v___x_3480_);
                            v___x_3484_ = lean_array_push(v___x_3483_, v_a_3479_);
                            v_sz_3485_ = lean_array_size(v_rest_3482_);
                            v___x_3486_ = 0usize;
                            v___x_3487_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg(v_rest_3482_, v_sz_3485_, v___x_3486_, v___x_3484_);
                            crate::leanh::lean_dec_ref(v_rest_3482_);
                            return v___x_3487_;
                        } else {
                            crate::leanh::lean_dec(v_steps_3462_);
                            v_a_3488_ = crate::leanh::lean_ctor_get(v___x_3478_, 0);
                            v_isSharedCheck_3495_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3478_)) as u8;
                            if v_isSharedCheck_3495_ == 0 {
                                v___x_3490_ = v___x_3478_;
                                v_isShared_3491_ = v_isSharedCheck_3495_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3488_);
                                crate::leanh::lean_dec(v___x_3478_);
                                v___x_3490_ = crate::leanh::lean_box(0);
                                v_isShared_3491_ = v_isSharedCheck_3495_;
                                state = 1;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3491_ == 0 {
                    v___x_3493_ = v___x_3490_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3494_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3494_, 0, v_a_3488_);
                    v___x_3493_ = v_reuseFailAlloc_3494_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3493_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_mkCalcStepViews___boxed(
    mut v_steps_3496_: *mut crate::leanh::LeanObject,
    mut v_a_3497_: *mut crate::leanh::LeanObject,
    mut v_a_3498_: *mut crate::leanh::LeanObject,
    mut v_a_3499_: *mut crate::leanh::LeanObject,
    mut v_a_3500_: *mut crate::leanh::LeanObject,
    mut v_a_3501_: *mut crate::leanh::LeanObject,
    mut v_a_3502_: *mut crate::leanh::LeanObject,
    mut v_a_3503_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3504_ = l_Lean_Elab_Term_mkCalcStepViews(
        v_steps_3496_,
        v_a_3497_,
        v_a_3498_,
        v_a_3499_,
        v_a_3500_,
        v_a_3501_,
        v_a_3502_,
    );
    crate::leanh::lean_dec(v_a_3502_);
    crate::leanh::lean_dec_ref(v_a_3501_);
    crate::leanh::lean_dec(v_a_3500_);
    crate::leanh::lean_dec_ref(v_a_3499_);
    crate::leanh::lean_dec(v_a_3498_);
    crate::leanh::lean_dec_ref(v_a_3497_);
    return v_res_3504_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0(
    mut v_as_3505_: *mut crate::leanh::LeanObject,
    mut v_sz_3506_: usize,
    mut v_i_3507_: usize,
    mut v_b_3508_: *mut crate::leanh::LeanObject,
    mut v___y_3509_: *mut crate::leanh::LeanObject,
    mut v___y_3510_: *mut crate::leanh::LeanObject,
    mut v___y_3511_: *mut crate::leanh::LeanObject,
    mut v___y_3512_: *mut crate::leanh::LeanObject,
    mut v___y_3513_: *mut crate::leanh::LeanObject,
    mut v___y_3514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3516_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg(v_as_3505_, v_sz_3506_, v_i_3507_, v_b_3508_);
    return v___x_3516_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___boxed(
    mut v_as_3517_: *mut crate::leanh::LeanObject,
    mut v_sz_3518_: *mut crate::leanh::LeanObject,
    mut v_i_3519_: *mut crate::leanh::LeanObject,
    mut v_b_3520_: *mut crate::leanh::LeanObject,
    mut v___y_3521_: *mut crate::leanh::LeanObject,
    mut v___y_3522_: *mut crate::leanh::LeanObject,
    mut v___y_3523_: *mut crate::leanh::LeanObject,
    mut v___y_3524_: *mut crate::leanh::LeanObject,
    mut v___y_3525_: *mut crate::leanh::LeanObject,
    mut v___y_3526_: *mut crate::leanh::LeanObject,
    mut v___y_3527_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3528_: usize = 0;
    let mut v_i_boxed_3529_: usize = 0;
    let mut v_res_3530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3528_ = crate::leanh::lean_unbox_usize(v_sz_3518_);
    crate::leanh::lean_dec(v_sz_3518_);
    v_i_boxed_3529_ = crate::leanh::lean_unbox_usize(v_i_3519_);
    crate::leanh::lean_dec(v_i_3519_);
    v_res_3530_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0(v_as_3517_, v_sz_boxed_3528_, v_i_boxed_3529_, v_b_3520_, v___y_3521_, v___y_3522_, v___y_3523_, v___y_3524_, v___y_3525_, v___y_3526_);
    crate::leanh::lean_dec(v___y_3526_);
    crate::leanh::lean_dec_ref(v___y_3525_);
    crate::leanh::lean_dec(v___y_3524_);
    crate::leanh::lean_dec_ref(v___y_3523_);
    crate::leanh::lean_dec(v___y_3522_);
    crate::leanh::lean_dec_ref(v___y_3521_);
    crate::leanh::lean_dec_ref(v_as_3517_);
    return v_res_3530_;
}
pub unsafe fn _init_l_panic___at___00Lean_Elab_Term_elabCalcSteps_spec__2___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3531_ = l_Lean_instInhabitedExpr;
    v___x_3532_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3532_, 0, v___x_3531_);
    crate::leanh::lean_ctor_set(v___x_3532_, 1, v___x_3531_);
    return v___x_3532_;
}
pub unsafe fn l_panic___at___00Lean_Elab_Term_elabCalcSteps_spec__2(
    mut v_msg_3533_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3534_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_panic___at___00Lean_Elab_Term_elabCalcSteps_spec__2___closed__0),
        core::ptr::addr_of_mut!(
            l_panic___at___00Lean_Elab_Term_elabCalcSteps_spec__2___closed__0_once
        ),
        _init_l_panic___at___00Lean_Elab_Term_elabCalcSteps_spec__2___closed__0,
    );
    v___x_3535_ = lean_panic_fn_borrowed(v___x_3534_, v_msg_3533_);
    return v___x_3535_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__4(
    mut v_opts_3536_: *mut crate::leanh::LeanObject,
    mut v_opt_3537_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_3539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_3538_ = crate::leanh::lean_ctor_get(v_opt_3537_, 0);
    v_defValue_3539_ = crate::leanh::lean_ctor_get(v_opt_3537_, 1);
    v_map_3540_ = crate::leanh::lean_ctor_get(v_opts_3536_, 0);
    v___x_3541_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3540_,
            v_name_3538_,
        );
    if crate::leanh::lean_obj_tag(v___x_3541_) == 0 {
        let mut v___x_3542_: u8 = 0;
        v___x_3542_ = (crate::leanh::lean_unbox(v_defValue_3539_) as u8);
        return v___x_3542_;
    } else {
        let mut v_val_3543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3543_ = crate::leanh::lean_ctor_get(v___x_3541_, 0);
        crate::leanh::lean_inc(v_val_3543_);
        crate::leanh::lean_dec_ref_known(v___x_3541_, 1);
        if crate::leanh::lean_obj_tag(v_val_3543_) == 1 {
            let mut v_v_3544_: u8 = 0;
            v_v_3544_ = crate::leanh::lean_ctor_get_uint8(v_val_3543_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_3543_, 0);
            return v_v_3544_;
        } else {
            let mut v___x_3545_: u8 = 0;
            crate::leanh::lean_dec(v_val_3543_);
            v___x_3545_ = (crate::leanh::lean_unbox(v_defValue_3539_) as u8);
            return v___x_3545_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__4___boxed(
    mut v_opts_3546_: *mut crate::leanh::LeanObject,
    mut v_opt_3547_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3548_: u8 = 0;
    let mut v_r_3549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3548_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__4(v_opts_3546_, v_opt_3547_);
    crate::leanh::lean_dec_ref(v_opt_3547_);
    crate::leanh::lean_dec_ref(v_opts_3546_);
    v_r_3549_ = crate::leanh::lean_box((v_res_3548_) as usize);
    return v_r_3549_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3550_ = crate::leanh::lean_box(1);
    v___x_3551_ = l_Lean_MessageData_ofFormat(v___x_3550_);
    return v___x_3551_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3555_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__2;
    v___x_3556_ = l_Lean_MessageData_ofFormat(v___x_3555_);
    return v___x_3556_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5(
    mut v_x_3557_: *mut crate::leanh::LeanObject,
    mut v_x_3558_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_3559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3563_: u8 = 0;
    let mut v_before_3564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3567_: u8 = 0;
    let mut v___x_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3580_: u8 = 0;
    let mut v_unused_3581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3582_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3558_) == 0 {
                    return v_x_3557_;
                } else {
                    v_head_3559_ = crate::leanh::lean_ctor_get(v_x_3558_, 0);
                    v_tail_3560_ = crate::leanh::lean_ctor_get(v_x_3558_, 1);
                    v_isSharedCheck_3582_ = (!crate::leanh::lean_is_exclusive(v_x_3558_)) as u8;
                    if v_isSharedCheck_3582_ == 0 {
                        v___x_3562_ = v_x_3558_;
                        v_isShared_3563_ = v_isSharedCheck_3582_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3560_);
                        crate::leanh::lean_inc(v_head_3559_);
                        crate::leanh::lean_dec(v_x_3558_);
                        v___x_3562_ = crate::leanh::lean_box(0);
                        v_isShared_3563_ = v_isSharedCheck_3582_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_3564_ = crate::leanh::lean_ctor_get(v_head_3559_, 0);
                v_isSharedCheck_3580_ = (!crate::leanh::lean_is_exclusive(v_head_3559_)) as u8;
                if v_isSharedCheck_3580_ == 0 {
                    v_unused_3581_ = crate::leanh::lean_ctor_get(v_head_3559_, 1);
                    crate::leanh::lean_dec(v_unused_3581_);
                    v___x_3566_ = v_head_3559_;
                    v_isShared_3567_ = v_isSharedCheck_3580_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_before_3564_);
                    crate::leanh::lean_dec(v_head_3559_);
                    v___x_3566_ = crate::leanh::lean_box(0);
                    v_isShared_3567_ = v_isSharedCheck_3580_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3568_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__0);
                if v_isShared_3567_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3566_, 7);
                    crate::leanh::lean_ctor_set(v___x_3566_, 1, v___x_3568_);
                    crate::leanh::lean_ctor_set(v___x_3566_, 0, v_x_3557_);
                    v___x_3570_ = v___x_3566_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3579_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3579_, 0, v_x_3557_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3579_, 1, v___x_3568_);
                    v___x_3570_ = v_reuseFailAlloc_3579_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3571_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__3);
                if v_isShared_3563_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3562_, 7);
                    crate::leanh::lean_ctor_set(v___x_3562_, 1, v___x_3571_);
                    crate::leanh::lean_ctor_set(v___x_3562_, 0, v___x_3570_);
                    v___x_3573_ = v___x_3562_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3578_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3578_, 0, v___x_3570_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3578_, 1, v___x_3571_);
                    v___x_3573_ = v_reuseFailAlloc_3578_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3574_ = l_Lean_MessageData_ofSyntax(v_before_3564_);
                v___x_3575_ = l_Lean_indentD(v___x_3574_);
                v___x_3576_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3576_, 0, v___x_3573_);
                crate::leanh::lean_ctor_set(v___x_3576_, 1, v___x_3575_);
                v_x_3557_ = v___x_3576_;
                v_x_3558_ = v_tail_3560_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3586_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___closed__1;
    v___x_3587_ = l_Lean_MessageData_ofFormat(v___x_3586_);
    return v___x_3587_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg(
    mut v_msgData_3588_: *mut crate::leanh::LeanObject,
    mut v_macroStack_3589_: *mut crate::leanh::LeanObject,
    mut v___y_3590_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: u8 = 0;
    let mut v___x_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_after_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3601_: u8 = 0;
    let mut v___x_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgData_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3613_: u8 = 0;
    let mut v_unused_3614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_3592_ = crate::leanh::lean_ctor_get(v___y_3590_, 2);
                v___x_3593_ = l_Lean_Elab_pp_macroStack;
                v___x_3594_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__4(v_options_3592_, v___x_3593_);
                if v___x_3594_ == 0 {
                    crate::leanh::lean_dec(v_macroStack_3589_);
                    v___x_3595_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3595_, 0, v_msgData_3588_);
                    return v___x_3595_;
                } else {
                    if crate::leanh::lean_obj_tag(v_macroStack_3589_) == 0 {
                        v___x_3596_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3596_, 0, v_msgData_3588_);
                        return v___x_3596_;
                    } else {
                        v_head_3597_ = crate::leanh::lean_ctor_get(v_macroStack_3589_, 0);
                        crate::leanh::lean_inc(v_head_3597_);
                        v_after_3598_ = crate::leanh::lean_ctor_get(v_head_3597_, 1);
                        v_isSharedCheck_3613_ =
                            (!crate::leanh::lean_is_exclusive(v_head_3597_)) as u8;
                        if v_isSharedCheck_3613_ == 0 {
                            v_unused_3614_ = crate::leanh::lean_ctor_get(v_head_3597_, 0);
                            crate::leanh::lean_dec(v_unused_3614_);
                            v___x_3600_ = v_head_3597_;
                            v_isShared_3601_ = v_isSharedCheck_3613_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_after_3598_);
                            crate::leanh::lean_dec(v_head_3597_);
                            v___x_3600_ = crate::leanh::lean_box(0);
                            v_isShared_3601_ = v_isSharedCheck_3613_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3602_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__0);
                if v_isShared_3601_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3600_, 7);
                    crate::leanh::lean_ctor_set(v___x_3600_, 1, v___x_3602_);
                    crate::leanh::lean_ctor_set(v___x_3600_, 0, v_msgData_3588_);
                    v___x_3604_ = v___x_3600_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3612_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3612_, 0, v_msgData_3588_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3612_, 1, v___x_3602_);
                    v___x_3604_ = v_reuseFailAlloc_3612_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3605_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___closed__2);
                v___x_3606_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3606_, 0, v___x_3604_);
                crate::leanh::lean_ctor_set(v___x_3606_, 1, v___x_3605_);
                v___x_3607_ = l_Lean_MessageData_ofSyntax(v_after_3598_);
                v___x_3608_ = l_Lean_indentD(v___x_3607_);
                v_msgData_3609_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_msgData_3609_, 0, v___x_3606_);
                crate::leanh::lean_ctor_set(v_msgData_3609_, 1, v___x_3608_);
                v___x_3610_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5(v_msgData_3609_, v_macroStack_3589_);
                v___x_3611_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3611_, 0, v___x_3610_);
                return v___x_3611_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_msgData_3615_: *mut crate::leanh::LeanObject,
    mut v_macroStack_3616_: *mut crate::leanh::LeanObject,
    mut v___y_3617_: *mut crate::leanh::LeanObject,
    mut v___y_3618_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3619_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg(v_msgData_3615_, v_macroStack_3616_, v___y_3617_);
    crate::leanh::lean_dec_ref(v___y_3617_);
    return v_res_3619_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0___redArg(
    mut v_msg_3620_: *mut crate::leanh::LeanObject,
    mut v___y_3621_: *mut crate::leanh::LeanObject,
    mut v___y_3622_: *mut crate::leanh::LeanObject,
    mut v___y_3623_: *mut crate::leanh::LeanObject,
    mut v___y_3624_: *mut crate::leanh::LeanObject,
    mut v___y_3625_: *mut crate::leanh::LeanObject,
    mut v___y_3626_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_3631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3637_: u8 = 0;
    let mut v___x_3638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3642_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3628_ = crate::leanh::lean_ctor_get(v___y_3625_, 5);
                v___x_3629_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0_spec__0(v_msg_3620_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_);
                v_a_3630_ = crate::leanh::lean_ctor_get(v___x_3629_, 0);
                crate::leanh::lean_inc(v_a_3630_);
                crate::leanh::lean_dec_ref(v___x_3629_);
                v_macroStack_3631_ = crate::leanh::lean_ctor_get(v___y_3621_, 1);
                v___x_3632_ = l_Lean_Elab_getBetterRef(v_ref_3628_, v_macroStack_3631_);
                crate::leanh::lean_inc(v_macroStack_3631_);
                v___x_3633_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg(v_a_3630_, v_macroStack_3631_, v___y_3625_);
                v_a_3634_ = crate::leanh::lean_ctor_get(v___x_3633_, 0);
                v_isSharedCheck_3642_ = (!crate::leanh::lean_is_exclusive(v___x_3633_)) as u8;
                if v_isSharedCheck_3642_ == 0 {
                    v___x_3636_ = v___x_3633_;
                    v_isShared_3637_ = v_isSharedCheck_3642_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3634_);
                    crate::leanh::lean_dec(v___x_3633_);
                    v___x_3636_ = crate::leanh::lean_box(0);
                    v_isShared_3637_ = v_isSharedCheck_3642_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3638_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3638_, 0, v___x_3632_);
                crate::leanh::lean_ctor_set(v___x_3638_, 1, v_a_3634_);
                if v_isShared_3637_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3636_, 1);
                    crate::leanh::lean_ctor_set(v___x_3636_, 0, v___x_3638_);
                    v___x_3640_ = v___x_3636_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3641_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3641_, 0, v___x_3638_);
                    v___x_3640_ = v_reuseFailAlloc_3641_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3640_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0___redArg___boxed(
    mut v_msg_3643_: *mut crate::leanh::LeanObject,
    mut v___y_3644_: *mut crate::leanh::LeanObject,
    mut v___y_3645_: *mut crate::leanh::LeanObject,
    mut v___y_3646_: *mut crate::leanh::LeanObject,
    mut v___y_3647_: *mut crate::leanh::LeanObject,
    mut v___y_3648_: *mut crate::leanh::LeanObject,
    mut v___y_3649_: *mut crate::leanh::LeanObject,
    mut v___y_3650_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3651_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0___redArg(v_msg_3643_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_);
    crate::leanh::lean_dec(v___y_3649_);
    crate::leanh::lean_dec_ref(v___y_3648_);
    crate::leanh::lean_dec(v___y_3647_);
    crate::leanh::lean_dec_ref(v___y_3646_);
    crate::leanh::lean_dec(v___y_3645_);
    crate::leanh::lean_dec_ref(v___y_3644_);
    return v_res_3651_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0___redArg(
    mut v_ref_3652_: *mut crate::leanh::LeanObject,
    mut v_msg_3653_: *mut crate::leanh::LeanObject,
    mut v___y_3654_: *mut crate::leanh::LeanObject,
    mut v___y_3655_: *mut crate::leanh::LeanObject,
    mut v___y_3656_: *mut crate::leanh::LeanObject,
    mut v___y_3657_: *mut crate::leanh::LeanObject,
    mut v___y_3658_: *mut crate::leanh::LeanObject,
    mut v___y_3659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_3661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3673_: u8 = 0;
    let mut v_cancelTk_x3f_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3675_: u8 = 0;
    let mut v_inheritedTraceOptions_3676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_3661_ = crate::leanh::lean_ctor_get(v___y_3658_, 0);
    v_fileMap_3662_ = crate::leanh::lean_ctor_get(v___y_3658_, 1);
    v_options_3663_ = crate::leanh::lean_ctor_get(v___y_3658_, 2);
    v_currRecDepth_3664_ = crate::leanh::lean_ctor_get(v___y_3658_, 3);
    v_maxRecDepth_3665_ = crate::leanh::lean_ctor_get(v___y_3658_, 4);
    v_ref_3666_ = crate::leanh::lean_ctor_get(v___y_3658_, 5);
    v_currNamespace_3667_ = crate::leanh::lean_ctor_get(v___y_3658_, 6);
    v_openDecls_3668_ = crate::leanh::lean_ctor_get(v___y_3658_, 7);
    v_initHeartbeats_3669_ = crate::leanh::lean_ctor_get(v___y_3658_, 8);
    v_maxHeartbeats_3670_ = crate::leanh::lean_ctor_get(v___y_3658_, 9);
    v_quotContext_3671_ = crate::leanh::lean_ctor_get(v___y_3658_, 10);
    v_currMacroScope_3672_ = crate::leanh::lean_ctor_get(v___y_3658_, 11);
    v_diag_3673_ = crate::leanh::lean_ctor_get_uint8(
        v___y_3658_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_3674_ = crate::leanh::lean_ctor_get(v___y_3658_, 12);
    v_suppressElabErrors_3675_ = crate::leanh::lean_ctor_get_uint8(
        v___y_3658_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_3676_ = crate::leanh::lean_ctor_get(v___y_3658_, 13);
    v_ref_3677_ = l_Lean_replaceRef(v_ref_3652_, v_ref_3666_);
    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_3676_);
    crate::leanh::lean_inc(v_cancelTk_x3f_3674_);
    crate::leanh::lean_inc(v_currMacroScope_3672_);
    crate::leanh::lean_inc(v_quotContext_3671_);
    crate::leanh::lean_inc(v_maxHeartbeats_3670_);
    crate::leanh::lean_inc(v_initHeartbeats_3669_);
    crate::leanh::lean_inc(v_openDecls_3668_);
    crate::leanh::lean_inc(v_currNamespace_3667_);
    crate::leanh::lean_inc(v_maxRecDepth_3665_);
    crate::leanh::lean_inc(v_currRecDepth_3664_);
    crate::leanh::lean_inc_ref(v_options_3663_);
    crate::leanh::lean_inc_ref(v_fileMap_3662_);
    crate::leanh::lean_inc_ref(v_fileName_3661_);
    v___x_3678_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_3678_, 0, v_fileName_3661_);
    crate::leanh::lean_ctor_set(v___x_3678_, 1, v_fileMap_3662_);
    crate::leanh::lean_ctor_set(v___x_3678_, 2, v_options_3663_);
    crate::leanh::lean_ctor_set(v___x_3678_, 3, v_currRecDepth_3664_);
    crate::leanh::lean_ctor_set(v___x_3678_, 4, v_maxRecDepth_3665_);
    crate::leanh::lean_ctor_set(v___x_3678_, 5, v_ref_3677_);
    crate::leanh::lean_ctor_set(v___x_3678_, 6, v_currNamespace_3667_);
    crate::leanh::lean_ctor_set(v___x_3678_, 7, v_openDecls_3668_);
    crate::leanh::lean_ctor_set(v___x_3678_, 8, v_initHeartbeats_3669_);
    crate::leanh::lean_ctor_set(v___x_3678_, 9, v_maxHeartbeats_3670_);
    crate::leanh::lean_ctor_set(v___x_3678_, 10, v_quotContext_3671_);
    crate::leanh::lean_ctor_set(v___x_3678_, 11, v_currMacroScope_3672_);
    crate::leanh::lean_ctor_set(v___x_3678_, 12, v_cancelTk_x3f_3674_);
    crate::leanh::lean_ctor_set(v___x_3678_, 13, v_inheritedTraceOptions_3676_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_3678_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v_diag_3673_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_3678_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_3675_,
    );
    v___x_3679_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0___redArg(v_msg_3653_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_, v___x_3678_, v___y_3659_);
    crate::leanh::lean_dec_ref_known(v___x_3678_, 14);
    return v___x_3679_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0___redArg___boxed(
    mut v_ref_3680_: *mut crate::leanh::LeanObject,
    mut v_msg_3681_: *mut crate::leanh::LeanObject,
    mut v___y_3682_: *mut crate::leanh::LeanObject,
    mut v___y_3683_: *mut crate::leanh::LeanObject,
    mut v___y_3684_: *mut crate::leanh::LeanObject,
    mut v___y_3685_: *mut crate::leanh::LeanObject,
    mut v___y_3686_: *mut crate::leanh::LeanObject,
    mut v___y_3687_: *mut crate::leanh::LeanObject,
    mut v___y_3688_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3689_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0___redArg(
        v_ref_3680_,
        v_msg_3681_,
        v___y_3682_,
        v___y_3683_,
        v___y_3684_,
        v___y_3685_,
        v___y_3686_,
        v___y_3687_,
    );
    crate::leanh::lean_dec(v___y_3687_);
    crate::leanh::lean_dec_ref(v___y_3686_);
    crate::leanh::lean_dec(v___y_3685_);
    crate::leanh::lean_dec_ref(v___y_3684_);
    crate::leanh::lean_dec(v___y_3683_);
    crate::leanh::lean_dec_ref(v___y_3682_);
    crate::leanh::lean_dec(v_ref_3680_);
    return v_res_3689_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3691_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__0;
    v___x_3692_ = l_Lean_stringToMessageData(v___x_3691_);
    return v___x_3692_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3694_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__2;
    v___x_3695_ = l_Lean_stringToMessageData(v___x_3694_);
    return v___x_3695_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3697_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__4;
    v___x_3698_ = l_Lean_stringToMessageData(v___x_3697_);
    return v___x_3698_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3700_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__6;
    v___x_3701_ = l_Lean_stringToMessageData(v___x_3700_);
    return v___x_3701_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1(
    mut v_as_3702_: *mut crate::leanh::LeanObject,
    mut v_sz_3703_: usize,
    mut v_i_3704_: usize,
    mut v_b_3705_: *mut crate::leanh::LeanObject,
    mut v___y_3706_: *mut crate::leanh::LeanObject,
    mut v___y_3707_: *mut crate::leanh::LeanObject,
    mut v___y_3708_: *mut crate::leanh::LeanObject,
    mut v___y_3709_: *mut crate::leanh::LeanObject,
    mut v___y_3710_: *mut crate::leanh::LeanObject,
    mut v___y_3711_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: usize = 0;
    let mut v___x_3716_: usize = 0;
    let mut v___y_3719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: u8 = 0;
    let mut v___x_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3730_: u8 = 0;
    let mut v_a_3731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_term_3741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_3742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3766_: u8 = 0;
    let mut v_cancelTk_x3f_3767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3768_: u8 = 0;
    let mut v_inheritedTraceOptions_3769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3777_: u8 = 0;
    let mut v___x_3779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3781_: u8 = 0;
    let mut v_a_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3785_: u8 = 0;
    let mut v___x_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3789_: u8 = 0;
    let mut v_a_3790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3797_: u8 = 0;
    let mut v___x_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3801_: u8 = 0;
    let mut v_a_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3812_: u8 = 0;
    let mut v_fst_3813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3817_: u8 = 0;
    let mut v_val_3818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3821_: u8 = 0;
    let mut v___x_3822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_term_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3849_: u8 = 0;
    let mut v___x_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3853_: u8 = 0;
    let mut v_reuseFailAlloc_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3859_: u8 = 0;
    let mut v___x_3861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3863_: u8 = 0;
    let mut v_a_3864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3867_: u8 = 0;
    let mut v___x_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3871_: u8 = 0;
    let mut v_a_3872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3875_: u8 = 0;
    let mut v___x_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3879_: u8 = 0;
    let mut v_isSharedCheck_3880_: u8 = 0;
    let mut v_snd_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3882_: u8 = 0;
    let mut v_unused_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_term_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3893_: u8 = 0;
    let mut v___x_3895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3897_: u8 = 0;
    let mut v_a_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3901_: u8 = 0;
    let mut v___x_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3905_: u8 = 0;
    let mut v_a_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3909_: u8 = 0;
    let mut v___x_3911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3913_: u8 = 0;
    let mut v_val_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_term_3917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3923_: u8 = 0;
    let mut v___x_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3927_: u8 = 0;
    let mut v_a_3928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3931_: u8 = 0;
    let mut v___x_3933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3935_: u8 = 0;
    let mut v_term_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3937_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3724_ = lean_usize_dec_lt(v_i_3704_, v_sz_3703_);
                if v___x_3724_ == 0 {
                    v___x_3725_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3725_, 0, v_b_3705_);
                    return v___x_3725_;
                } else {
                    v_fst_3726_ = crate::leanh::lean_ctor_get(v_b_3705_, 0);
                    v_snd_3727_ = crate::leanh::lean_ctor_get(v_b_3705_, 1);
                    v_isSharedCheck_3937_ = (!crate::leanh::lean_is_exclusive(v_b_3705_)) as u8;
                    if v_isSharedCheck_3937_ == 0 {
                        v___x_3729_ = v_b_3705_;
                        v_isShared_3730_ = v_isSharedCheck_3937_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3727_);
                        crate::leanh::lean_inc(v_fst_3726_);
                        crate::leanh::lean_dec(v_b_3705_);
                        v___x_3729_ = crate::leanh::lean_box(0);
                        v_isShared_3730_ = v_isSharedCheck_3937_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3715_ = 1usize;
                v___x_3716_ = lean_usize_add(v_i_3704_, v___x_3715_);
                v_i_3704_ = v___x_3716_;
                v_b_3705_ = v_a_3714_;
                state = 0;
                continue;
            }
            2 => {
                v___x_3721_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3721_, 0, v_a_3720_);
                v___x_3722_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3722_, 0, v___y_3719_);
                v___x_3723_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3723_, 0, v___x_3721_);
                crate::leanh::lean_ctor_set(v___x_3723_, 1, v___x_3722_);
                v_a_3714_ = v___x_3723_;
                state = 1;
                continue;
            }
            3 => {
                v_a_3731_ = lean_array_uget_borrowed(v_as_3702_, v_i_3704_);
                if crate::leanh::lean_obj_tag(v_snd_3727_) == 1 {
                    v_val_3914_ = crate::leanh::lean_ctor_get(v_snd_3727_, 0);
                    crate::leanh::lean_inc(v___y_3711_);
                    crate::leanh::lean_inc_ref(v___y_3710_);
                    crate::leanh::lean_inc(v___y_3709_);
                    crate::leanh::lean_inc_ref(v___y_3708_);
                    crate::leanh::lean_inc(v_val_3914_);
                    v___x_3915_ = lean_infer_type(
                        v_val_3914_,
                        v___y_3708_,
                        v___y_3709_,
                        v___y_3710_,
                        v___y_3711_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3915_) == 0 {
                        v_a_3916_ = crate::leanh::lean_ctor_get(v___x_3915_, 0);
                        crate::leanh::lean_inc(v_a_3916_);
                        crate::leanh::lean_dec_ref_known(v___x_3915_, 1);
                        v_term_3917_ = crate::leanh::lean_ctor_get(v_a_3731_, 1);
                        crate::leanh::lean_inc(v_term_3917_);
                        v___x_3918_ = l_Lean_Elab_Term_annotateFirstHoleWithType(
                            v_term_3917_,
                            v_a_3916_,
                            v___y_3706_,
                            v___y_3707_,
                            v___y_3708_,
                            v___y_3709_,
                            v___y_3710_,
                            v___y_3711_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3918_) == 0 {
                            v_a_3919_ = crate::leanh::lean_ctor_get(v___x_3918_, 0);
                            crate::leanh::lean_inc(v_a_3919_);
                            crate::leanh::lean_dec_ref_known(v___x_3918_, 1);
                            v_a_3803_ = v_a_3919_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref_known(v_snd_3727_, 1);
                            crate::leanh::lean_del_object(v___x_3729_);
                            crate::leanh::lean_dec(v_fst_3726_);
                            v_a_3920_ = crate::leanh::lean_ctor_get(v___x_3918_, 0);
                            v_isSharedCheck_3927_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3918_)) as u8;
                            if v_isSharedCheck_3927_ == 0 {
                                v___x_3922_ = v___x_3918_;
                                v_isShared_3923_ = v_isSharedCheck_3927_;
                                state = 31;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3920_);
                                crate::leanh::lean_dec(v___x_3918_);
                                v___x_3922_ = crate::leanh::lean_box(0);
                                v_isShared_3923_ = v_isSharedCheck_3927_;
                                state = 31;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_snd_3727_, 1);
                        crate::leanh::lean_del_object(v___x_3729_);
                        crate::leanh::lean_dec(v_fst_3726_);
                        v_a_3928_ = crate::leanh::lean_ctor_get(v___x_3915_, 0);
                        v_isSharedCheck_3935_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3915_)) as u8;
                        if v_isSharedCheck_3935_ == 0 {
                            v___x_3930_ = v___x_3915_;
                            v_isShared_3931_ = v_isSharedCheck_3935_;
                            state = 33;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3928_);
                            crate::leanh::lean_dec(v___x_3915_);
                            v___x_3930_ = crate::leanh::lean_box(0);
                            v_isShared_3931_ = v_isSharedCheck_3935_;
                            state = 33;
                            continue;
                        }
                    }
                } else {
                    v_term_3936_ = crate::leanh::lean_ctor_get(v_a_3731_, 1);
                    crate::leanh::lean_inc(v_term_3936_);
                    v_a_3803_ = v_term_3936_;
                    state = 12;
                    continue;
                }
            }
            4 => {
                v_term_3741_ = crate::leanh::lean_ctor_get(v_a_3731_, 1);
                v_proof_3742_ = crate::leanh::lean_ctor_get(v_a_3731_, 2);
                crate::leanh::lean_inc_ref(v___y_3734_);
                v___x_3743_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3743_, 0, v___y_3734_);
                v___x_3744_ = crate::leanh::lean_box(0);
                v___x_3745_ = crate::leanh::lean_box((v___x_3724_) as usize);
                v___x_3746_ = crate::leanh::lean_box((v___x_3724_) as usize);
                crate::leanh::lean_inc(v___y_3738_);
                crate::leanh::lean_inc_ref(v___y_3737_);
                crate::leanh::lean_inc(v___y_3736_);
                crate::leanh::lean_inc_ref(v___y_3735_);
                crate::leanh::lean_inc(v_proof_3742_);
                v___x_3747_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_Term_elabTermEnsuringType___boxed as *mut core::ffi::c_void,
                    12,
                    9,
                );
                crate::leanh::lean_closure_set(v___x_3747_, 0, v_proof_3742_);
                crate::leanh::lean_closure_set(v___x_3747_, 1, v___x_3743_);
                crate::leanh::lean_closure_set(v___x_3747_, 2, v___x_3745_);
                crate::leanh::lean_closure_set(v___x_3747_, 3, v___x_3746_);
                crate::leanh::lean_closure_set(v___x_3747_, 4, v___x_3744_);
                crate::leanh::lean_closure_set(v___x_3747_, 5, v___y_3735_);
                crate::leanh::lean_closure_set(v___x_3747_, 6, v___y_3736_);
                crate::leanh::lean_closure_set(v___x_3747_, 7, v___y_3737_);
                crate::leanh::lean_closure_set(v___x_3747_, 8, v___y_3738_);
                v___x_3748_ =
                    l_Lean_Core_withFreshMacroScope___redArg(v___x_3747_, v___y_3739_, v___y_3740_);
                if crate::leanh::lean_obj_tag(v___x_3748_) == 0 {
                    if crate::leanh::lean_obj_tag(v_fst_3726_) == 1 {
                        crate::leanh::lean_del_object(v___x_3729_);
                        v_val_3749_ = crate::leanh::lean_ctor_get(v_fst_3726_, 0);
                        crate::leanh::lean_inc(v_val_3749_);
                        crate::leanh::lean_dec_ref_known(v_fst_3726_, 1);
                        v_a_3750_ = crate::leanh::lean_ctor_get(v___x_3748_, 0);
                        crate::leanh::lean_inc(v_a_3750_);
                        crate::leanh::lean_dec_ref_known(v___x_3748_, 1);
                        v_fst_3751_ = crate::leanh::lean_ctor_get(v_val_3749_, 0);
                        crate::leanh::lean_inc(v_fst_3751_);
                        v_snd_3752_ = crate::leanh::lean_ctor_get(v_val_3749_, 1);
                        crate::leanh::lean_inc(v_snd_3752_);
                        crate::leanh::lean_dec(v_val_3749_);
                        v___x_3753_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsUsingDefault(
                            v___y_3735_,
                            v___y_3736_,
                            v___y_3737_,
                            v___y_3738_,
                            v___y_3739_,
                            v___y_3740_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3753_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_3753_, 1);
                            v_fileName_3754_ = crate::leanh::lean_ctor_get(v___y_3739_, 0);
                            v_fileMap_3755_ = crate::leanh::lean_ctor_get(v___y_3739_, 1);
                            v_options_3756_ = crate::leanh::lean_ctor_get(v___y_3739_, 2);
                            v_currRecDepth_3757_ = crate::leanh::lean_ctor_get(v___y_3739_, 3);
                            v_maxRecDepth_3758_ = crate::leanh::lean_ctor_get(v___y_3739_, 4);
                            v_ref_3759_ = crate::leanh::lean_ctor_get(v___y_3739_, 5);
                            v_currNamespace_3760_ = crate::leanh::lean_ctor_get(v___y_3739_, 6);
                            v_openDecls_3761_ = crate::leanh::lean_ctor_get(v___y_3739_, 7);
                            v_initHeartbeats_3762_ = crate::leanh::lean_ctor_get(v___y_3739_, 8);
                            v_maxHeartbeats_3763_ = crate::leanh::lean_ctor_get(v___y_3739_, 9);
                            v_quotContext_3764_ = crate::leanh::lean_ctor_get(v___y_3739_, 10);
                            v_currMacroScope_3765_ = crate::leanh::lean_ctor_get(v___y_3739_, 11);
                            v_diag_3766_ = crate::leanh::lean_ctor_get_uint8(
                                v___y_3739_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                            );
                            v_cancelTk_x3f_3767_ = crate::leanh::lean_ctor_get(v___y_3739_, 12);
                            v_suppressElabErrors_3768_ = crate::leanh::lean_ctor_get_uint8(
                                v___y_3739_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1)
                                    as u32,
                            );
                            v_inheritedTraceOptions_3769_ =
                                crate::leanh::lean_ctor_get(v___y_3739_, 13);
                            v_ref_3770_ = l_Lean_replaceRef(v_term_3741_, v_ref_3759_);
                            crate::leanh::lean_inc_ref(v_inheritedTraceOptions_3769_);
                            crate::leanh::lean_inc(v_cancelTk_x3f_3767_);
                            crate::leanh::lean_inc(v_currMacroScope_3765_);
                            crate::leanh::lean_inc(v_quotContext_3764_);
                            crate::leanh::lean_inc(v_maxHeartbeats_3763_);
                            crate::leanh::lean_inc(v_initHeartbeats_3762_);
                            crate::leanh::lean_inc(v_openDecls_3761_);
                            crate::leanh::lean_inc(v_currNamespace_3760_);
                            crate::leanh::lean_inc(v_maxRecDepth_3758_);
                            crate::leanh::lean_inc(v_currRecDepth_3757_);
                            crate::leanh::lean_inc_ref(v_options_3756_);
                            crate::leanh::lean_inc_ref(v_fileMap_3755_);
                            crate::leanh::lean_inc_ref(v_fileName_3754_);
                            v___x_3771_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                            crate::leanh::lean_ctor_set(v___x_3771_, 0, v_fileName_3754_);
                            crate::leanh::lean_ctor_set(v___x_3771_, 1, v_fileMap_3755_);
                            crate::leanh::lean_ctor_set(v___x_3771_, 2, v_options_3756_);
                            crate::leanh::lean_ctor_set(v___x_3771_, 3, v_currRecDepth_3757_);
                            crate::leanh::lean_ctor_set(v___x_3771_, 4, v_maxRecDepth_3758_);
                            crate::leanh::lean_ctor_set(v___x_3771_, 5, v_ref_3770_);
                            crate::leanh::lean_ctor_set(v___x_3771_, 6, v_currNamespace_3760_);
                            crate::leanh::lean_ctor_set(v___x_3771_, 7, v_openDecls_3761_);
                            crate::leanh::lean_ctor_set(v___x_3771_, 8, v_initHeartbeats_3762_);
                            crate::leanh::lean_ctor_set(v___x_3771_, 9, v_maxHeartbeats_3763_);
                            crate::leanh::lean_ctor_set(v___x_3771_, 10, v_quotContext_3764_);
                            crate::leanh::lean_ctor_set(v___x_3771_, 11, v_currMacroScope_3765_);
                            crate::leanh::lean_ctor_set(v___x_3771_, 12, v_cancelTk_x3f_3767_);
                            crate::leanh::lean_ctor_set(
                                v___x_3771_,
                                13,
                                v_inheritedTraceOptions_3769_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_3771_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                                v_diag_3766_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_3771_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1)
                                    as u32,
                                v_suppressElabErrors_3768_,
                            );
                            v___x_3772_ = l_Lean_Elab_Term_mkCalcTrans(
                                v_fst_3751_,
                                v_snd_3752_,
                                v_a_3750_,
                                v___y_3734_,
                                v___y_3737_,
                                v___y_3738_,
                                v___x_3771_,
                                v___y_3740_,
                            );
                            crate::leanh::lean_dec_ref_known(v___x_3771_, 14);
                            crate::leanh::lean_dec(v_snd_3752_);
                            if crate::leanh::lean_obj_tag(v___x_3772_) == 0 {
                                v_a_3773_ = crate::leanh::lean_ctor_get(v___x_3772_, 0);
                                crate::leanh::lean_inc(v_a_3773_);
                                crate::leanh::lean_dec_ref_known(v___x_3772_, 1);
                                v___y_3719_ = v___y_3733_;
                                v_a_3720_ = v_a_3773_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v___y_3733_);
                                v_a_3774_ = crate::leanh::lean_ctor_get(v___x_3772_, 0);
                                v_isSharedCheck_3781_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3772_)) as u8;
                                if v_isSharedCheck_3781_ == 0 {
                                    v___x_3776_ = v___x_3772_;
                                    v_isShared_3777_ = v_isSharedCheck_3781_;
                                    state = 5;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3774_);
                                    crate::leanh::lean_dec(v___x_3772_);
                                    v___x_3776_ = crate::leanh::lean_box(0);
                                    v_isShared_3777_ = v_isSharedCheck_3781_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_snd_3752_);
                            crate::leanh::lean_dec(v_fst_3751_);
                            crate::leanh::lean_dec(v_a_3750_);
                            crate::leanh::lean_dec_ref(v___y_3734_);
                            crate::leanh::lean_dec_ref(v___y_3733_);
                            v_a_3782_ = crate::leanh::lean_ctor_get(v___x_3753_, 0);
                            v_isSharedCheck_3789_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3753_)) as u8;
                            if v_isSharedCheck_3789_ == 0 {
                                v___x_3784_ = v___x_3753_;
                                v_isShared_3785_ = v_isSharedCheck_3789_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3782_);
                                crate::leanh::lean_dec(v___x_3753_);
                                v___x_3784_ = crate::leanh::lean_box(0);
                                v_isShared_3785_ = v_isSharedCheck_3789_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_fst_3726_);
                        v_a_3790_ = crate::leanh::lean_ctor_get(v___x_3748_, 0);
                        crate::leanh::lean_inc(v_a_3790_);
                        crate::leanh::lean_dec_ref_known(v___x_3748_, 1);
                        if v_isShared_3730_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3729_, 1, v___y_3734_);
                            crate::leanh::lean_ctor_set(v___x_3729_, 0, v_a_3790_);
                            v___x_3792_ = v___x_3729_;
                            state = 9;
                            continue;
                        } else {
                            v_reuseFailAlloc_3793_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3793_, 0, v_a_3790_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3793_, 1, v___y_3734_);
                            v___x_3792_ = v_reuseFailAlloc_3793_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_3734_);
                    crate::leanh::lean_dec_ref(v___y_3733_);
                    crate::leanh::lean_del_object(v___x_3729_);
                    crate::leanh::lean_dec(v_fst_3726_);
                    v_a_3794_ = crate::leanh::lean_ctor_get(v___x_3748_, 0);
                    v_isSharedCheck_3801_ = (!crate::leanh::lean_is_exclusive(v___x_3748_)) as u8;
                    if v_isSharedCheck_3801_ == 0 {
                        v___x_3796_ = v___x_3748_;
                        v_isShared_3797_ = v_isSharedCheck_3801_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3794_);
                        crate::leanh::lean_dec(v___x_3748_);
                        v___x_3796_ = crate::leanh::lean_box(0);
                        v_isShared_3797_ = v_isSharedCheck_3801_;
                        state = 10;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_3777_ == 0 {
                    v___x_3779_ = v___x_3776_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3780_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3780_, 0, v_a_3774_);
                    v___x_3779_ = v_reuseFailAlloc_3780_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3779_;
            }
            7 => {
                if v_isShared_3785_ == 0 {
                    v___x_3787_ = v___x_3784_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3788_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3788_, 0, v_a_3782_);
                    v___x_3787_ = v_reuseFailAlloc_3788_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3787_;
            }
            9 => {
                v___y_3719_ = v___y_3733_;
                v_a_3720_ = v___x_3792_;
                state = 2;
                continue;
            }
            10 => {
                if v_isShared_3797_ == 0 {
                    v___x_3799_ = v___x_3796_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3800_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3800_, 0, v_a_3794_);
                    v___x_3799_ = v_reuseFailAlloc_3800_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3799_;
            }
            12 => {
                v___x_3804_ = l_Lean_Elab_Term_elabType(
                    v_a_3803_,
                    v___y_3706_,
                    v___y_3707_,
                    v___y_3708_,
                    v___y_3709_,
                    v___y_3710_,
                    v___y_3711_,
                );
                if crate::leanh::lean_obj_tag(v___x_3804_) == 0 {
                    v_a_3805_ = crate::leanh::lean_ctor_get(v___x_3804_, 0);
                    crate::leanh::lean_inc(v_a_3805_);
                    crate::leanh::lean_dec_ref_known(v___x_3804_, 1);
                    v___x_3806_ = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(v_a_3805_);
                    if crate::leanh::lean_obj_tag(v___x_3806_) == 0 {
                        v_a_3807_ = crate::leanh::lean_ctor_get(v___x_3806_, 0);
                        crate::leanh::lean_inc(v_a_3807_);
                        crate::leanh::lean_dec_ref_known(v___x_3806_, 1);
                        if crate::leanh::lean_obj_tag(v_a_3807_) == 1 {
                            v_val_3808_ = crate::leanh::lean_ctor_get(v_a_3807_, 0);
                            crate::leanh::lean_inc(v_val_3808_);
                            crate::leanh::lean_dec_ref_known(v_a_3807_, 1);
                            v_snd_3809_ = crate::leanh::lean_ctor_get(v_val_3808_, 1);
                            v_isSharedCheck_3882_ =
                                (!crate::leanh::lean_is_exclusive(v_val_3808_)) as u8;
                            if v_isSharedCheck_3882_ == 0 {
                                v_unused_3883_ = crate::leanh::lean_ctor_get(v_val_3808_, 0);
                                crate::leanh::lean_dec(v_unused_3883_);
                                v___x_3811_ = v_val_3808_;
                                v_isShared_3812_ = v_isSharedCheck_3882_;
                                state = 13;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_snd_3809_);
                                crate::leanh::lean_dec(v_val_3808_);
                                v___x_3811_ = crate::leanh::lean_box(0);
                                v_isShared_3812_ = v_isSharedCheck_3882_;
                                state = 13;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3807_);
                            crate::leanh::lean_del_object(v___x_3729_);
                            v_term_3884_ = crate::leanh::lean_ctor_get(v_a_3731_, 1);
                            v___x_3885_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__7), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__7_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__7);
                            v___x_3886_ = l_Lean_indentExpr(v_a_3805_);
                            v___x_3887_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3887_, 0, v___x_3885_);
                            crate::leanh::lean_ctor_set(v___x_3887_, 1, v___x_3886_);
                            v___x_3888_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0___redArg(v_term_3884_, v___x_3887_, v___y_3706_, v___y_3707_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_);
                            if crate::leanh::lean_obj_tag(v___x_3888_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_3888_, 1);
                                v___x_3889_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3889_, 0, v_fst_3726_);
                                crate::leanh::lean_ctor_set(v___x_3889_, 1, v_snd_3727_);
                                v_a_3714_ = v___x_3889_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_snd_3727_);
                                crate::leanh::lean_dec(v_fst_3726_);
                                v_a_3890_ = crate::leanh::lean_ctor_get(v___x_3888_, 0);
                                v_isSharedCheck_3897_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3888_)) as u8;
                                if v_isSharedCheck_3897_ == 0 {
                                    v___x_3892_ = v___x_3888_;
                                    v_isShared_3893_ = v_isSharedCheck_3897_;
                                    state = 25;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3890_);
                                    crate::leanh::lean_dec(v___x_3888_);
                                    v___x_3892_ = crate::leanh::lean_box(0);
                                    v_isShared_3893_ = v_isSharedCheck_3897_;
                                    state = 25;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3805_);
                        crate::leanh::lean_del_object(v___x_3729_);
                        crate::leanh::lean_dec(v_snd_3727_);
                        crate::leanh::lean_dec(v_fst_3726_);
                        v_a_3898_ = crate::leanh::lean_ctor_get(v___x_3806_, 0);
                        v_isSharedCheck_3905_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3806_)) as u8;
                        if v_isSharedCheck_3905_ == 0 {
                            v___x_3900_ = v___x_3806_;
                            v_isShared_3901_ = v_isSharedCheck_3905_;
                            state = 27;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3898_);
                            crate::leanh::lean_dec(v___x_3806_);
                            v___x_3900_ = crate::leanh::lean_box(0);
                            v_isShared_3901_ = v_isSharedCheck_3905_;
                            state = 27;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3729_);
                    crate::leanh::lean_dec(v_snd_3727_);
                    crate::leanh::lean_dec(v_fst_3726_);
                    v_a_3906_ = crate::leanh::lean_ctor_get(v___x_3804_, 0);
                    v_isSharedCheck_3913_ = (!crate::leanh::lean_is_exclusive(v___x_3804_)) as u8;
                    if v_isSharedCheck_3913_ == 0 {
                        v___x_3908_ = v___x_3804_;
                        v_isShared_3909_ = v_isSharedCheck_3913_;
                        state = 29;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3906_);
                        crate::leanh::lean_dec(v___x_3804_);
                        v___x_3908_ = crate::leanh::lean_box(0);
                        v_isShared_3909_ = v_isSharedCheck_3913_;
                        state = 29;
                        continue;
                    }
                }
            }
            13 => {
                if crate::leanh::lean_obj_tag(v_snd_3727_) == 1 {
                    v_fst_3813_ = crate::leanh::lean_ctor_get(v_snd_3809_, 0);
                    v_snd_3814_ = crate::leanh::lean_ctor_get(v_snd_3809_, 1);
                    v_isSharedCheck_3880_ = (!crate::leanh::lean_is_exclusive(v_snd_3809_)) as u8;
                    if v_isSharedCheck_3880_ == 0 {
                        v___x_3816_ = v_snd_3809_;
                        v_isShared_3817_ = v_isSharedCheck_3880_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3814_);
                        crate::leanh::lean_inc(v_fst_3813_);
                        crate::leanh::lean_dec(v_snd_3809_);
                        v___x_3816_ = crate::leanh::lean_box(0);
                        v_isShared_3817_ = v_isSharedCheck_3880_;
                        state = 14;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3811_);
                    crate::leanh::lean_dec(v_snd_3727_);
                    v_snd_3881_ = crate::leanh::lean_ctor_get(v_snd_3809_, 1);
                    crate::leanh::lean_inc(v_snd_3881_);
                    crate::leanh::lean_dec(v_snd_3809_);
                    v___y_3733_ = v_snd_3881_;
                    v___y_3734_ = v_a_3805_;
                    v___y_3735_ = v___y_3706_;
                    v___y_3736_ = v___y_3707_;
                    v___y_3737_ = v___y_3708_;
                    v___y_3738_ = v___y_3709_;
                    v___y_3739_ = v___y_3710_;
                    v___y_3740_ = v___y_3711_;
                    state = 4;
                    continue;
                }
            }
            14 => {
                v_val_3818_ = crate::leanh::lean_ctor_get(v_snd_3727_, 0);
                crate::leanh::lean_inc_n(v_val_3818_, 2);
                crate::leanh::lean_dec_ref_known(v_snd_3727_, 1);
                crate::leanh::lean_inc(v_fst_3813_);
                v___x_3819_ = l_Lean_Meta_isExprDefEqGuarded(
                    v_fst_3813_,
                    v_val_3818_,
                    v___y_3708_,
                    v___y_3709_,
                    v___y_3710_,
                    v___y_3711_,
                );
                if crate::leanh::lean_obj_tag(v___x_3819_) == 0 {
                    v_a_3820_ = crate::leanh::lean_ctor_get(v___x_3819_, 0);
                    crate::leanh::lean_inc(v_a_3820_);
                    crate::leanh::lean_dec_ref_known(v___x_3819_, 1);
                    v___x_3821_ = (crate::leanh::lean_unbox(v_a_3820_) as u8);
                    crate::leanh::lean_dec(v_a_3820_);
                    if v___x_3821_ == 0 {
                        crate::leanh::lean_inc(v___y_3711_);
                        crate::leanh::lean_inc_ref(v___y_3710_);
                        crate::leanh::lean_inc(v___y_3709_);
                        crate::leanh::lean_inc_ref(v___y_3708_);
                        crate::leanh::lean_inc(v_fst_3813_);
                        v___x_3822_ = lean_infer_type(
                            v_fst_3813_,
                            v___y_3708_,
                            v___y_3709_,
                            v___y_3710_,
                            v___y_3711_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3822_) == 0 {
                            v_a_3823_ = crate::leanh::lean_ctor_get(v___x_3822_, 0);
                            crate::leanh::lean_inc(v_a_3823_);
                            crate::leanh::lean_dec_ref_known(v___x_3822_, 1);
                            crate::leanh::lean_inc(v___y_3711_);
                            crate::leanh::lean_inc_ref(v___y_3710_);
                            crate::leanh::lean_inc(v___y_3709_);
                            crate::leanh::lean_inc_ref(v___y_3708_);
                            crate::leanh::lean_inc(v_val_3818_);
                            v___x_3824_ = lean_infer_type(
                                v_val_3818_,
                                v___y_3708_,
                                v___y_3709_,
                                v___y_3710_,
                                v___y_3711_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_3824_) == 0 {
                                v_a_3825_ = crate::leanh::lean_ctor_get(v___x_3824_, 0);
                                crate::leanh::lean_inc(v_a_3825_);
                                crate::leanh::lean_dec_ref_known(v___x_3824_, 1);
                                v_term_3826_ = crate::leanh::lean_ctor_get(v_a_3731_, 1);
                                v___x_3827_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__1);
                                v___x_3828_ = l_Lean_MessageData_ofExpr(v_fst_3813_);
                                v___x_3829_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3);
                                if v_isShared_3817_ == 0 {
                                    crate::leanh::lean_ctor_set_tag(v___x_3816_, 7);
                                    crate::leanh::lean_ctor_set(v___x_3816_, 1, v___x_3829_);
                                    crate::leanh::lean_ctor_set(v___x_3816_, 0, v___x_3828_);
                                    v___x_3831_ = v___x_3816_;
                                    state = 15;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3855_ =
                                        crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3855_,
                                        0,
                                        v___x_3828_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3855_,
                                        1,
                                        v___x_3829_,
                                    );
                                    v___x_3831_ = v_reuseFailAlloc_3855_;
                                    state = 15;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_3823_);
                                crate::leanh::lean_dec(v_val_3818_);
                                crate::leanh::lean_del_object(v___x_3816_);
                                crate::leanh::lean_dec(v_snd_3814_);
                                crate::leanh::lean_dec(v_fst_3813_);
                                crate::leanh::lean_del_object(v___x_3811_);
                                crate::leanh::lean_dec(v_a_3805_);
                                crate::leanh::lean_del_object(v___x_3729_);
                                crate::leanh::lean_dec(v_fst_3726_);
                                v_a_3856_ = crate::leanh::lean_ctor_get(v___x_3824_, 0);
                                v_isSharedCheck_3863_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3824_)) as u8;
                                if v_isSharedCheck_3863_ == 0 {
                                    v___x_3858_ = v___x_3824_;
                                    v_isShared_3859_ = v_isSharedCheck_3863_;
                                    state = 19;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3856_);
                                    crate::leanh::lean_dec(v___x_3824_);
                                    v___x_3858_ = crate::leanh::lean_box(0);
                                    v_isShared_3859_ = v_isSharedCheck_3863_;
                                    state = 19;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_val_3818_);
                            crate::leanh::lean_del_object(v___x_3816_);
                            crate::leanh::lean_dec(v_snd_3814_);
                            crate::leanh::lean_dec(v_fst_3813_);
                            crate::leanh::lean_del_object(v___x_3811_);
                            crate::leanh::lean_dec(v_a_3805_);
                            crate::leanh::lean_del_object(v___x_3729_);
                            crate::leanh::lean_dec(v_fst_3726_);
                            v_a_3864_ = crate::leanh::lean_ctor_get(v___x_3822_, 0);
                            v_isSharedCheck_3871_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3822_)) as u8;
                            if v_isSharedCheck_3871_ == 0 {
                                v___x_3866_ = v___x_3822_;
                                v_isShared_3867_ = v_isSharedCheck_3871_;
                                state = 21;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3864_);
                                crate::leanh::lean_dec(v___x_3822_);
                                v___x_3866_ = crate::leanh::lean_box(0);
                                v_isShared_3867_ = v_isSharedCheck_3871_;
                                state = 21;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_3818_);
                        crate::leanh::lean_del_object(v___x_3816_);
                        crate::leanh::lean_dec(v_fst_3813_);
                        crate::leanh::lean_del_object(v___x_3811_);
                        v___y_3733_ = v_snd_3814_;
                        v___y_3734_ = v_a_3805_;
                        v___y_3735_ = v___y_3706_;
                        v___y_3736_ = v___y_3707_;
                        v___y_3737_ = v___y_3708_;
                        v___y_3738_ = v___y_3709_;
                        v___y_3739_ = v___y_3710_;
                        v___y_3740_ = v___y_3711_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_val_3818_);
                    crate::leanh::lean_del_object(v___x_3816_);
                    crate::leanh::lean_dec(v_snd_3814_);
                    crate::leanh::lean_dec(v_fst_3813_);
                    crate::leanh::lean_del_object(v___x_3811_);
                    crate::leanh::lean_dec(v_a_3805_);
                    crate::leanh::lean_del_object(v___x_3729_);
                    crate::leanh::lean_dec(v_fst_3726_);
                    v_a_3872_ = crate::leanh::lean_ctor_get(v___x_3819_, 0);
                    v_isSharedCheck_3879_ = (!crate::leanh::lean_is_exclusive(v___x_3819_)) as u8;
                    if v_isSharedCheck_3879_ == 0 {
                        v___x_3874_ = v___x_3819_;
                        v_isShared_3875_ = v_isSharedCheck_3879_;
                        state = 23;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3872_);
                        crate::leanh::lean_dec(v___x_3819_);
                        v___x_3874_ = crate::leanh::lean_box(0);
                        v_isShared_3875_ = v_isSharedCheck_3879_;
                        state = 23;
                        continue;
                    }
                }
            }
            15 => {
                v___x_3832_ = l_Lean_MessageData_ofExpr(v_a_3823_);
                if v_isShared_3812_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3811_, 7);
                    crate::leanh::lean_ctor_set(v___x_3811_, 1, v___x_3832_);
                    crate::leanh::lean_ctor_set(v___x_3811_, 0, v___x_3831_);
                    v___x_3834_ = v___x_3811_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3854_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3854_, 0, v___x_3831_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3854_, 1, v___x_3832_);
                    v___x_3834_ = v_reuseFailAlloc_3854_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___x_3835_ = l_Lean_indentD(v___x_3834_);
                v___x_3836_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3836_, 0, v___x_3827_);
                crate::leanh::lean_ctor_set(v___x_3836_, 1, v___x_3835_);
                v___x_3837_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__5), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__5_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__5);
                v___x_3838_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3838_, 0, v___x_3836_);
                crate::leanh::lean_ctor_set(v___x_3838_, 1, v___x_3837_);
                v___x_3839_ = l_Lean_MessageData_ofExpr(v_val_3818_);
                v___x_3840_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3840_, 0, v___x_3839_);
                crate::leanh::lean_ctor_set(v___x_3840_, 1, v___x_3829_);
                v___x_3841_ = l_Lean_MessageData_ofExpr(v_a_3825_);
                v___x_3842_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3842_, 0, v___x_3840_);
                crate::leanh::lean_ctor_set(v___x_3842_, 1, v___x_3841_);
                v___x_3843_ = l_Lean_indentD(v___x_3842_);
                v___x_3844_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3844_, 0, v___x_3838_);
                crate::leanh::lean_ctor_set(v___x_3844_, 1, v___x_3843_);
                v___x_3845_ =
                    l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0___redArg(
                        v_term_3826_,
                        v___x_3844_,
                        v___y_3706_,
                        v___y_3707_,
                        v___y_3708_,
                        v___y_3709_,
                        v___y_3710_,
                        v___y_3711_,
                    );
                if crate::leanh::lean_obj_tag(v___x_3845_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3845_, 1);
                    v___y_3733_ = v_snd_3814_;
                    v___y_3734_ = v_a_3805_;
                    v___y_3735_ = v___y_3706_;
                    v___y_3736_ = v___y_3707_;
                    v___y_3737_ = v___y_3708_;
                    v___y_3738_ = v___y_3709_;
                    v___y_3739_ = v___y_3710_;
                    v___y_3740_ = v___y_3711_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_snd_3814_);
                    crate::leanh::lean_dec(v_a_3805_);
                    crate::leanh::lean_del_object(v___x_3729_);
                    crate::leanh::lean_dec(v_fst_3726_);
                    v_a_3846_ = crate::leanh::lean_ctor_get(v___x_3845_, 0);
                    v_isSharedCheck_3853_ = (!crate::leanh::lean_is_exclusive(v___x_3845_)) as u8;
                    if v_isSharedCheck_3853_ == 0 {
                        v___x_3848_ = v___x_3845_;
                        v_isShared_3849_ = v_isSharedCheck_3853_;
                        state = 17;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3846_);
                        crate::leanh::lean_dec(v___x_3845_);
                        v___x_3848_ = crate::leanh::lean_box(0);
                        v_isShared_3849_ = v_isSharedCheck_3853_;
                        state = 17;
                        continue;
                    }
                }
            }
            17 => {
                if v_isShared_3849_ == 0 {
                    v___x_3851_ = v___x_3848_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3852_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3852_, 0, v_a_3846_);
                    v___x_3851_ = v_reuseFailAlloc_3852_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3851_;
            }
            19 => {
                if v_isShared_3859_ == 0 {
                    v___x_3861_ = v___x_3858_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3862_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3862_, 0, v_a_3856_);
                    v___x_3861_ = v_reuseFailAlloc_3862_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_3861_;
            }
            21 => {
                if v_isShared_3867_ == 0 {
                    v___x_3869_ = v___x_3866_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_3870_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3870_, 0, v_a_3864_);
                    v___x_3869_ = v_reuseFailAlloc_3870_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_3869_;
            }
            23 => {
                if v_isShared_3875_ == 0 {
                    v___x_3877_ = v___x_3874_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_3878_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3878_, 0, v_a_3872_);
                    v___x_3877_ = v_reuseFailAlloc_3878_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_3877_;
            }
            25 => {
                if v_isShared_3893_ == 0 {
                    v___x_3895_ = v___x_3892_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_3896_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3896_, 0, v_a_3890_);
                    v___x_3895_ = v_reuseFailAlloc_3896_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_3895_;
            }
            27 => {
                if v_isShared_3901_ == 0 {
                    v___x_3903_ = v___x_3900_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_3904_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3904_, 0, v_a_3898_);
                    v___x_3903_ = v_reuseFailAlloc_3904_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_3903_;
            }
            29 => {
                if v_isShared_3909_ == 0 {
                    v___x_3911_ = v___x_3908_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_3912_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3912_, 0, v_a_3906_);
                    v___x_3911_ = v_reuseFailAlloc_3912_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_3911_;
            }
            31 => {
                if v_isShared_3923_ == 0 {
                    v___x_3925_ = v___x_3922_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_3926_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3926_, 0, v_a_3920_);
                    v___x_3925_ = v_reuseFailAlloc_3926_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_3925_;
            }
            33 => {
                if v_isShared_3931_ == 0 {
                    v___x_3933_ = v___x_3930_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_3934_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3934_, 0, v_a_3928_);
                    v___x_3933_ = v_reuseFailAlloc_3934_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_3933_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___boxed(
    mut v_as_3938_: *mut crate::leanh::LeanObject,
    mut v_sz_3939_: *mut crate::leanh::LeanObject,
    mut v_i_3940_: *mut crate::leanh::LeanObject,
    mut v_b_3941_: *mut crate::leanh::LeanObject,
    mut v___y_3942_: *mut crate::leanh::LeanObject,
    mut v___y_3943_: *mut crate::leanh::LeanObject,
    mut v___y_3944_: *mut crate::leanh::LeanObject,
    mut v___y_3945_: *mut crate::leanh::LeanObject,
    mut v___y_3946_: *mut crate::leanh::LeanObject,
    mut v___y_3947_: *mut crate::leanh::LeanObject,
    mut v___y_3948_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3949_: usize = 0;
    let mut v_i_boxed_3950_: usize = 0;
    let mut v_res_3951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3949_ = crate::leanh::lean_unbox_usize(v_sz_3939_);
    crate::leanh::lean_dec(v_sz_3939_);
    v_i_boxed_3950_ = crate::leanh::lean_unbox_usize(v_i_3940_);
    crate::leanh::lean_dec(v_i_3940_);
    v_res_3951_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1(v_as_3938_, v_sz_boxed_3949_, v_i_boxed_3950_, v_b_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_, v___y_3947_);
    crate::leanh::lean_dec(v___y_3947_);
    crate::leanh::lean_dec_ref(v___y_3946_);
    crate::leanh::lean_dec(v___y_3945_);
    crate::leanh::lean_dec_ref(v___y_3944_);
    crate::leanh::lean_dec(v___y_3943_);
    crate::leanh::lean_dec_ref(v___y_3942_);
    crate::leanh::lean_dec_ref(v_as_3938_);
    return v_res_3951_;
}
pub unsafe fn _init_l_Lean_Elab_Term_elabCalcSteps___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3957_ = l_Lean_Elab_Term_elabCalcSteps___closed__3;
    v___x_3958_ = crate::leanh::lean_unsigned_to_nat(14);
    v___x_3959_ = crate::leanh::lean_unsigned_to_nat(22);
    v___x_3960_ = l_Lean_Elab_Term_elabCalcSteps___closed__2;
    v___x_3961_ = l_Lean_Elab_Term_elabCalcSteps___closed__1;
    v___x_3962_ = l_mkPanicMessageWithDecl(
        v___x_3961_,
        v___x_3960_,
        v___x_3959_,
        v___x_3958_,
        v___x_3957_,
    );
    return v___x_3962_;
}
pub unsafe fn l_Lean_Elab_Term_elabCalcSteps(
    mut v_steps_3963_: *mut crate::leanh::LeanObject,
    mut v_a_3964_: *mut crate::leanh::LeanObject,
    mut v_a_3965_: *mut crate::leanh::LeanObject,
    mut v_a_3966_: *mut crate::leanh::LeanObject,
    mut v_a_3967_: *mut crate::leanh::LeanObject,
    mut v_a_3968_: *mut crate::leanh::LeanObject,
    mut v_a_3969_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3972_: usize = 0;
    let mut v___x_3973_: usize = 0;
    let mut v___x_3974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3979_: u8 = 0;
    let mut v_fst_3980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3990_: u8 = 0;
    let mut v_unused_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3995_: u8 = 0;
    let mut v___x_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3999_: u8 = 0;
    let mut v_a_4000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4003_: u8 = 0;
    let mut v___x_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4007_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3971_ = l_Lean_Elab_Term_elabCalcSteps___closed__0;
                v_sz_3972_ = lean_array_size(v_steps_3963_);
                v___x_3973_ = 0usize;
                v___x_3974_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1(v_steps_3963_, v_sz_3972_, v___x_3973_, v___x_3971_, v_a_3964_, v_a_3965_, v_a_3966_, v_a_3967_, v_a_3968_, v_a_3969_);
                if crate::leanh::lean_obj_tag(v___x_3974_) == 0 {
                    v_a_3975_ = crate::leanh::lean_ctor_get(v___x_3974_, 0);
                    crate::leanh::lean_inc(v_a_3975_);
                    crate::leanh::lean_dec_ref_known(v___x_3974_, 1);
                    v___x_3976_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsUsingDefault(
                        v_a_3964_, v_a_3965_, v_a_3966_, v_a_3967_, v_a_3968_, v_a_3969_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3976_) == 0 {
                        v_isSharedCheck_3990_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3976_)) as u8;
                        if v_isSharedCheck_3990_ == 0 {
                            v_unused_3991_ = crate::leanh::lean_ctor_get(v___x_3976_, 0);
                            crate::leanh::lean_dec(v_unused_3991_);
                            v___x_3978_ = v___x_3976_;
                            v_isShared_3979_ = v_isSharedCheck_3990_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_3976_);
                            v___x_3978_ = crate::leanh::lean_box(0);
                            v_isShared_3979_ = v_isSharedCheck_3990_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3975_);
                        v_a_3992_ = crate::leanh::lean_ctor_get(v___x_3976_, 0);
                        v_isSharedCheck_3999_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3976_)) as u8;
                        if v_isSharedCheck_3999_ == 0 {
                            v___x_3994_ = v___x_3976_;
                            v_isShared_3995_ = v_isSharedCheck_3999_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3992_);
                            crate::leanh::lean_dec(v___x_3976_);
                            v___x_3994_ = crate::leanh::lean_box(0);
                            v_isShared_3995_ = v_isSharedCheck_3999_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_a_4000_ = crate::leanh::lean_ctor_get(v___x_3974_, 0);
                    v_isSharedCheck_4007_ = (!crate::leanh::lean_is_exclusive(v___x_3974_)) as u8;
                    if v_isSharedCheck_4007_ == 0 {
                        v___x_4002_ = v___x_3974_;
                        v_isShared_4003_ = v_isSharedCheck_4007_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4000_);
                        crate::leanh::lean_dec(v___x_3974_);
                        v___x_4002_ = crate::leanh::lean_box(0);
                        v_isShared_4003_ = v_isSharedCheck_4007_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3980_ = crate::leanh::lean_ctor_get(v_a_3975_, 0);
                crate::leanh::lean_inc(v_fst_3980_);
                crate::leanh::lean_dec(v_a_3975_);
                if crate::leanh::lean_obj_tag(v_fst_3980_) == 0 {
                    v___x_3981_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_Term_elabCalcSteps___closed__4),
                        core::ptr::addr_of_mut!(l_Lean_Elab_Term_elabCalcSteps___closed__4_once),
                        _init_l_Lean_Elab_Term_elabCalcSteps___closed__4,
                    );
                    v___x_3982_ =
                        l_panic___at___00Lean_Elab_Term_elabCalcSteps_spec__2(v___x_3981_);
                    if v_isShared_3979_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3978_, 0, v___x_3982_);
                        v___x_3984_ = v___x_3978_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3985_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3985_, 0, v___x_3982_);
                        v___x_3984_ = v_reuseFailAlloc_3985_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_val_3986_ = crate::leanh::lean_ctor_get(v_fst_3980_, 0);
                    crate::leanh::lean_inc(v_val_3986_);
                    crate::leanh::lean_dec_ref_known(v_fst_3980_, 1);
                    if v_isShared_3979_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3978_, 0, v_val_3986_);
                        v___x_3988_ = v___x_3978_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3989_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3989_, 0, v_val_3986_);
                        v___x_3988_ = v_reuseFailAlloc_3989_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3984_;
            }
            3 => {
                return v___x_3988_;
            }
            4 => {
                if v_isShared_3995_ == 0 {
                    v___x_3997_ = v___x_3994_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3998_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3998_, 0, v_a_3992_);
                    v___x_3997_ = v_reuseFailAlloc_3998_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3997_;
            }
            6 => {
                if v_isShared_4003_ == 0 {
                    v___x_4005_ = v___x_4002_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4006_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4006_, 0, v_a_4000_);
                    v___x_4005_ = v_reuseFailAlloc_4006_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4005_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_elabCalcSteps___boxed(
    mut v_steps_4008_: *mut crate::leanh::LeanObject,
    mut v_a_4009_: *mut crate::leanh::LeanObject,
    mut v_a_4010_: *mut crate::leanh::LeanObject,
    mut v_a_4011_: *mut crate::leanh::LeanObject,
    mut v_a_4012_: *mut crate::leanh::LeanObject,
    mut v_a_4013_: *mut crate::leanh::LeanObject,
    mut v_a_4014_: *mut crate::leanh::LeanObject,
    mut v_a_4015_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4016_ = l_Lean_Elab_Term_elabCalcSteps(
        v_steps_4008_,
        v_a_4009_,
        v_a_4010_,
        v_a_4011_,
        v_a_4012_,
        v_a_4013_,
        v_a_4014_,
    );
    crate::leanh::lean_dec(v_a_4014_);
    crate::leanh::lean_dec_ref(v_a_4013_);
    crate::leanh::lean_dec(v_a_4012_);
    crate::leanh::lean_dec_ref(v_a_4011_);
    crate::leanh::lean_dec(v_a_4010_);
    crate::leanh::lean_dec_ref(v_a_4009_);
    crate::leanh::lean_dec_ref(v_steps_4008_);
    return v_res_4016_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0(
    mut v_00_u03b1_4017_: *mut crate::leanh::LeanObject,
    mut v_ref_4018_: *mut crate::leanh::LeanObject,
    mut v_msg_4019_: *mut crate::leanh::LeanObject,
    mut v___y_4020_: *mut crate::leanh::LeanObject,
    mut v___y_4021_: *mut crate::leanh::LeanObject,
    mut v___y_4022_: *mut crate::leanh::LeanObject,
    mut v___y_4023_: *mut crate::leanh::LeanObject,
    mut v___y_4024_: *mut crate::leanh::LeanObject,
    mut v___y_4025_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4027_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0___redArg(
        v_ref_4018_,
        v_msg_4019_,
        v___y_4020_,
        v___y_4021_,
        v___y_4022_,
        v___y_4023_,
        v___y_4024_,
        v___y_4025_,
    );
    return v___x_4027_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0___boxed(
    mut v_00_u03b1_4028_: *mut crate::leanh::LeanObject,
    mut v_ref_4029_: *mut crate::leanh::LeanObject,
    mut v_msg_4030_: *mut crate::leanh::LeanObject,
    mut v___y_4031_: *mut crate::leanh::LeanObject,
    mut v___y_4032_: *mut crate::leanh::LeanObject,
    mut v___y_4033_: *mut crate::leanh::LeanObject,
    mut v___y_4034_: *mut crate::leanh::LeanObject,
    mut v___y_4035_: *mut crate::leanh::LeanObject,
    mut v___y_4036_: *mut crate::leanh::LeanObject,
    mut v___y_4037_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4038_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0(
        v_00_u03b1_4028_,
        v_ref_4029_,
        v_msg_4030_,
        v___y_4031_,
        v___y_4032_,
        v___y_4033_,
        v___y_4034_,
        v___y_4035_,
        v___y_4036_,
    );
    crate::leanh::lean_dec(v___y_4036_);
    crate::leanh::lean_dec_ref(v___y_4035_);
    crate::leanh::lean_dec(v___y_4034_);
    crate::leanh::lean_dec_ref(v___y_4033_);
    crate::leanh::lean_dec(v___y_4032_);
    crate::leanh::lean_dec_ref(v___y_4031_);
    crate::leanh::lean_dec(v_ref_4029_);
    return v_res_4038_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0(
    mut v_00_u03b1_4039_: *mut crate::leanh::LeanObject,
    mut v_msg_4040_: *mut crate::leanh::LeanObject,
    mut v___y_4041_: *mut crate::leanh::LeanObject,
    mut v___y_4042_: *mut crate::leanh::LeanObject,
    mut v___y_4043_: *mut crate::leanh::LeanObject,
    mut v___y_4044_: *mut crate::leanh::LeanObject,
    mut v___y_4045_: *mut crate::leanh::LeanObject,
    mut v___y_4046_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4048_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0___redArg(v_msg_4040_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_);
    return v___x_4048_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0___boxed(
    mut v_00_u03b1_4049_: *mut crate::leanh::LeanObject,
    mut v_msg_4050_: *mut crate::leanh::LeanObject,
    mut v___y_4051_: *mut crate::leanh::LeanObject,
    mut v___y_4052_: *mut crate::leanh::LeanObject,
    mut v___y_4053_: *mut crate::leanh::LeanObject,
    mut v___y_4054_: *mut crate::leanh::LeanObject,
    mut v___y_4055_: *mut crate::leanh::LeanObject,
    mut v___y_4056_: *mut crate::leanh::LeanObject,
    mut v___y_4057_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4058_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0(v_00_u03b1_4049_, v_msg_4050_, v___y_4051_, v___y_4052_, v___y_4053_, v___y_4054_, v___y_4055_, v___y_4056_);
    crate::leanh::lean_dec(v___y_4056_);
    crate::leanh::lean_dec_ref(v___y_4055_);
    crate::leanh::lean_dec(v___y_4054_);
    crate::leanh::lean_dec_ref(v___y_4053_);
    crate::leanh::lean_dec(v___y_4052_);
    crate::leanh::lean_dec_ref(v___y_4051_);
    return v_res_4058_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2(
    mut v_msgData_4059_: *mut crate::leanh::LeanObject,
    mut v_macroStack_4060_: *mut crate::leanh::LeanObject,
    mut v___y_4061_: *mut crate::leanh::LeanObject,
    mut v___y_4062_: *mut crate::leanh::LeanObject,
    mut v___y_4063_: *mut crate::leanh::LeanObject,
    mut v___y_4064_: *mut crate::leanh::LeanObject,
    mut v___y_4065_: *mut crate::leanh::LeanObject,
    mut v___y_4066_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4068_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg(v_msgData_4059_, v_macroStack_4060_, v___y_4065_);
    return v___x_4068_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___boxed(
    mut v_msgData_4069_: *mut crate::leanh::LeanObject,
    mut v_macroStack_4070_: *mut crate::leanh::LeanObject,
    mut v___y_4071_: *mut crate::leanh::LeanObject,
    mut v___y_4072_: *mut crate::leanh::LeanObject,
    mut v___y_4073_: *mut crate::leanh::LeanObject,
    mut v___y_4074_: *mut crate::leanh::LeanObject,
    mut v___y_4075_: *mut crate::leanh::LeanObject,
    mut v___y_4076_: *mut crate::leanh::LeanObject,
    mut v___y_4077_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4078_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2(v_msgData_4069_, v_macroStack_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_);
    crate::leanh::lean_dec(v___y_4076_);
    crate::leanh::lean_dec_ref(v___y_4075_);
    crate::leanh::lean_dec(v___y_4074_);
    crate::leanh::lean_dec_ref(v___y_4073_);
    crate::leanh::lean_dec(v___y_4072_);
    crate::leanh::lean_dec_ref(v___y_4071_);
    return v_res_4078_;
}
pub unsafe fn _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4079_ = crate::leanh::lean_box(0);
    v___x_4080_ = l_Lean_Elab_abortTermExceptionId;
    v___x_4081_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4081_, 0, v___x_4080_);
    crate::leanh::lean_ctor_set(v___x_4081_, 1, v___x_4079_);
    return v___x_4081_;
}
pub unsafe fn l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4083_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg___closed__0);
    v___x_4084_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4084_, 0, v___x_4083_);
    return v___x_4084_;
}
pub unsafe fn l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg___boxed(
    mut v___y_4085_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4086_ =
        l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg();
    return v_res_4086_;
}
pub unsafe fn l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0(
    mut v_00_u03b1_4087_: *mut crate::leanh::LeanObject,
    mut v___y_4088_: *mut crate::leanh::LeanObject,
    mut v___y_4089_: *mut crate::leanh::LeanObject,
    mut v___y_4090_: *mut crate::leanh::LeanObject,
    mut v___y_4091_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4093_ =
        l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg();
    return v___x_4093_;
}
pub unsafe fn l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___boxed(
    mut v_00_u03b1_4094_: *mut crate::leanh::LeanObject,
    mut v___y_4095_: *mut crate::leanh::LeanObject,
    mut v___y_4096_: *mut crate::leanh::LeanObject,
    mut v___y_4097_: *mut crate::leanh::LeanObject,
    mut v___y_4098_: *mut crate::leanh::LeanObject,
    mut v___y_4099_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4100_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0(
        v_00_u03b1_4094_,
        v___y_4095_,
        v___y_4096_,
        v___y_4097_,
        v___y_4098_,
    );
    crate::leanh::lean_dec(v___y_4098_);
    crate::leanh::lean_dec_ref(v___y_4097_);
    crate::leanh::lean_dec(v___y_4096_);
    crate::leanh::lean_dec_ref(v___y_4095_);
    return v_res_4100_;
}
pub unsafe fn l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2___redArg(
    mut v_msg_4101_: *mut crate::leanh::LeanObject,
    mut v___y_4102_: *mut crate::leanh::LeanObject,
    mut v___y_4103_: *mut crate::leanh::LeanObject,
    mut v___y_4104_: *mut crate::leanh::LeanObject,
    mut v___y_4105_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6547__overap_4108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4107_ = l_panic___at___00Lean_Elab_Term_mkCalcTrans_spec__1___closed__0;
    v___x_6547__overap_4108_ = lean_panic_fn_borrowed(v___f_4107_, v_msg_4101_);
    crate::leanh::lean_inc(v___y_4105_);
    crate::leanh::lean_inc_ref(v___y_4104_);
    crate::leanh::lean_inc(v___y_4103_);
    crate::leanh::lean_inc_ref(v___y_4102_);
    v___x_4109_ = crate::leanh::lean_apply_5(
        v___x_6547__overap_4108_,
        v___y_4102_,
        v___y_4103_,
        v___y_4104_,
        v___y_4105_,
        crate::leanh::lean_box(0),
    );
    return v___x_4109_;
}
pub unsafe fn l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2___redArg___boxed(
    mut v_msg_4110_: *mut crate::leanh::LeanObject,
    mut v___y_4111_: *mut crate::leanh::LeanObject,
    mut v___y_4112_: *mut crate::leanh::LeanObject,
    mut v___y_4113_: *mut crate::leanh::LeanObject,
    mut v___y_4114_: *mut crate::leanh::LeanObject,
    mut v___y_4115_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4116_ = l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2___redArg(
        v_msg_4110_,
        v___y_4111_,
        v___y_4112_,
        v___y_4113_,
        v___y_4114_,
    );
    crate::leanh::lean_dec(v___y_4114_);
    crate::leanh::lean_dec_ref(v___y_4113_);
    crate::leanh::lean_dec(v___y_4112_);
    crate::leanh::lean_dec_ref(v___y_4111_);
    return v_res_4116_;
}
pub unsafe fn l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2(
    mut v_00_u03b1_4117_: *mut crate::leanh::LeanObject,
    mut v_msg_4118_: *mut crate::leanh::LeanObject,
    mut v___y_4119_: *mut crate::leanh::LeanObject,
    mut v___y_4120_: *mut crate::leanh::LeanObject,
    mut v___y_4121_: *mut crate::leanh::LeanObject,
    mut v___y_4122_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4124_ = l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2___redArg(
        v_msg_4118_,
        v___y_4119_,
        v___y_4120_,
        v___y_4121_,
        v___y_4122_,
    );
    return v___x_4124_;
}
pub unsafe fn l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2___boxed(
    mut v_00_u03b1_4125_: *mut crate::leanh::LeanObject,
    mut v_msg_4126_: *mut crate::leanh::LeanObject,
    mut v___y_4127_: *mut crate::leanh::LeanObject,
    mut v___y_4128_: *mut crate::leanh::LeanObject,
    mut v___y_4129_: *mut crate::leanh::LeanObject,
    mut v___y_4130_: *mut crate::leanh::LeanObject,
    mut v___y_4131_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4132_ = l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2(
        v_00_u03b1_4125_,
        v_msg_4126_,
        v___y_4127_,
        v___y_4128_,
        v___y_4129_,
        v___y_4130_,
    );
    crate::leanh::lean_dec(v___y_4130_);
    crate::leanh::lean_dec_ref(v___y_4129_);
    crate::leanh::lean_dec(v___y_4128_);
    crate::leanh::lean_dec_ref(v___y_4127_);
    return v_res_4132_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0(
    mut v___y_4140_: u8,
    mut v_suppressElabErrors_4141_: u8,
    mut v_x_4142_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_4142_) == 1 {
        let mut v_pre_4143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_pre_4143_ = crate::leanh::lean_ctor_get(v_x_4142_, 0);
        match crate::leanh::lean_obj_tag(v_pre_4143_) {
            1 => {
                let mut v_pre_4144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_pre_4144_ = crate::leanh::lean_ctor_get(v_pre_4143_, 0);
                match crate::leanh::lean_obj_tag(v_pre_4144_) {
                    0 => {
                        let mut v_str_4145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v_str_4146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_4147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_4148_: u8 = 0;
                        v_str_4145_ = crate::leanh::lean_ctor_get(v_x_4142_, 1);
                        v_str_4146_ = crate::leanh::lean_ctor_get(v_pre_4143_, 1);
                        v___x_4147_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__13;
                        v___x_4148_ = lean_string_dec_eq(v_str_4146_, v___x_4147_);
                        if v___x_4148_ == 0 {
                            let mut v___x_4149_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4150_: u8 = 0;
                            v___x_4149_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__0;
                            v___x_4150_ = lean_string_dec_eq(v_str_4146_, v___x_4149_);
                            if v___x_4150_ == 0 {
                                return v___y_4140_;
                            } else {
                                let mut v___x_4151_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_4152_: u8 = 0;
                                v___x_4151_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__1;
                                v___x_4152_ = lean_string_dec_eq(v_str_4145_, v___x_4151_);
                                if v___x_4152_ == 0 {
                                    return v___y_4140_;
                                } else {
                                    return v_suppressElabErrors_4141_;
                                }
                            }
                        } else {
                            let mut v___x_4153_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4154_: u8 = 0;
                            v___x_4153_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__2;
                            v___x_4154_ = lean_string_dec_eq(v_str_4145_, v___x_4153_);
                            if v___x_4154_ == 0 {
                                return v___y_4140_;
                            } else {
                                return v_suppressElabErrors_4141_;
                            }
                        }
                    }
                    1 => {
                        let mut v_pre_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v_pre_4155_ = crate::leanh::lean_ctor_get(v_pre_4144_, 0);
                        if crate::leanh::lean_obj_tag(v_pre_4155_) == 0 {
                            let mut v_str_4156_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_4157_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_4158_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4159_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4160_: u8 = 0;
                            v_str_4156_ = crate::leanh::lean_ctor_get(v_x_4142_, 1);
                            v_str_4157_ = crate::leanh::lean_ctor_get(v_pre_4143_, 1);
                            v_str_4158_ = crate::leanh::lean_ctor_get(v_pre_4144_, 1);
                            v___x_4159_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__3;
                            v___x_4160_ = lean_string_dec_eq(v_str_4158_, v___x_4159_);
                            if v___x_4160_ == 0 {
                                return v___y_4140_;
                            } else {
                                let mut v___x_4161_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_4162_: u8 = 0;
                                v___x_4161_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__4;
                                v___x_4162_ = lean_string_dec_eq(v_str_4157_, v___x_4161_);
                                if v___x_4162_ == 0 {
                                    return v___y_4140_;
                                } else {
                                    let mut v___x_4163_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_4164_: u8 = 0;
                                    v___x_4163_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__5;
                                    v___x_4164_ = lean_string_dec_eq(v_str_4156_, v___x_4163_);
                                    if v___x_4164_ == 0 {
                                        return v___y_4140_;
                                    } else {
                                        return v_suppressElabErrors_4141_;
                                    }
                                }
                            }
                        } else {
                            return v___y_4140_;
                        }
                    }
                    _ => {
                        return v___y_4140_;
                    }
                }
            }
            0 => {
                let mut v_str_4165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4167_: u8 = 0;
                v_str_4165_ = crate::leanh::lean_ctor_get(v_x_4142_, 1);
                v___x_4166_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__6;
                v___x_4167_ = lean_string_dec_eq(v_str_4165_, v___x_4166_);
                if v___x_4167_ == 0 {
                    return v___y_4140_;
                } else {
                    return v_suppressElabErrors_4141_;
                }
            }
            _ => {
                return v___y_4140_;
            }
        }
    } else {
        return v___y_4140_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___boxed(
    mut v___y_4168_: *mut crate::leanh::LeanObject,
    mut v_suppressElabErrors_4169_: *mut crate::leanh::LeanObject,
    mut v_x_4170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_8930__boxed_4171_: u8 = 0;
    let mut v_suppressElabErrors_boxed_4172_: u8 = 0;
    let mut v_res_4173_: u8 = 0;
    let mut v_r_4174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_8930__boxed_4171_ = (crate::leanh::lean_unbox(v___y_4168_) as u8);
    v_suppressElabErrors_boxed_4172_ = (crate::leanh::lean_unbox(v_suppressElabErrors_4169_) as u8);
    v_res_4173_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0(v___y_8930__boxed_4171_, v_suppressElabErrors_boxed_4172_, v_x_4170_);
    crate::leanh::lean_dec(v_x_4170_);
    v_r_4174_ = crate::leanh::lean_box((v_res_4173_) as usize);
    return v_r_4174_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1(
    mut v_ref_4175_: *mut crate::leanh::LeanObject,
    mut v_msgData_4176_: *mut crate::leanh::LeanObject,
    mut v_severity_4177_: u8,
    mut v_isSilent_4178_: u8,
    mut v___y_4179_: *mut crate::leanh::LeanObject,
    mut v___y_4180_: *mut crate::leanh::LeanObject,
    mut v___y_4181_: *mut crate::leanh::LeanObject,
    mut v___y_4182_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4187_: u8 = 0;
    let mut v___y_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4189_: u8 = 0;
    let mut v___y_4190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4208_: u8 = 0;
    let mut v___x_4209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4219_: u8 = 0;
    let mut v___y_4221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4223_: u8 = 0;
    let mut v___y_4224_: u8 = 0;
    let mut v___y_4225_: u8 = 0;
    let mut v___y_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4234_: u8 = 0;
    let mut v___x_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: u8 = 0;
    let mut v___x_4240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4244_: u8 = 0;
    let mut v___y_4246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4248_: u8 = 0;
    let mut v___y_4249_: u8 = 0;
    let mut v___y_4250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4251_: u8 = 0;
    let mut v___y_4252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4259_: u8 = 0;
    let mut v___y_4260_: u8 = 0;
    let mut v___y_4261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4263_: u8 = 0;
    let mut v_ref_4264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: u8 = 0;
    let mut v___y_4270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4271_: u8 = 0;
    let mut v___y_4272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4275_: u8 = 0;
    let mut v___y_4276_: u8 = 0;
    let mut v___y_4278_: u8 = 0;
    let mut v_fileName_4279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4283_: u8 = 0;
    let mut v___x_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: u8 = 0;
    let mut v___x_4288_: u8 = 0;
    let mut v___x_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: u8 = 0;
    let mut v___x_4291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: u8 = 0;
    let mut v___x_4294_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4268_ = 2;
                v___x_4293_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4177_, v___x_4268_);
                if v___x_4293_ == 0 {
                    v___y_4278_ = v___x_4293_;
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_msgData_4176_);
                    v___x_4294_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_4176_);
                    v___y_4278_ = v___x_4294_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_4194_ = lean_st_ref_take(v___y_4193_);
                v_currNamespace_4195_ = crate::leanh::lean_ctor_get(v___y_4192_, 6);
                v_openDecls_4196_ = crate::leanh::lean_ctor_get(v___y_4192_, 7);
                v_env_4197_ = crate::leanh::lean_ctor_get(v___x_4194_, 0);
                v_nextMacroScope_4198_ = crate::leanh::lean_ctor_get(v___x_4194_, 1);
                v_ngen_4199_ = crate::leanh::lean_ctor_get(v___x_4194_, 2);
                v_auxDeclNGen_4200_ = crate::leanh::lean_ctor_get(v___x_4194_, 3);
                v_traceState_4201_ = crate::leanh::lean_ctor_get(v___x_4194_, 4);
                v_cache_4202_ = crate::leanh::lean_ctor_get(v___x_4194_, 5);
                v_messages_4203_ = crate::leanh::lean_ctor_get(v___x_4194_, 6);
                v_infoState_4204_ = crate::leanh::lean_ctor_get(v___x_4194_, 7);
                v_snapshotTasks_4205_ = crate::leanh::lean_ctor_get(v___x_4194_, 8);
                v_isSharedCheck_4219_ = (!crate::leanh::lean_is_exclusive(v___x_4194_)) as u8;
                if v_isSharedCheck_4219_ == 0 {
                    v___x_4207_ = v___x_4194_;
                    v_isShared_4208_ = v_isSharedCheck_4219_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_4205_);
                    crate::leanh::lean_inc(v_infoState_4204_);
                    crate::leanh::lean_inc(v_messages_4203_);
                    crate::leanh::lean_inc(v_cache_4202_);
                    crate::leanh::lean_inc(v_traceState_4201_);
                    crate::leanh::lean_inc(v_auxDeclNGen_4200_);
                    crate::leanh::lean_inc(v_ngen_4199_);
                    crate::leanh::lean_inc(v_nextMacroScope_4198_);
                    crate::leanh::lean_inc(v_env_4197_);
                    crate::leanh::lean_dec(v___x_4194_);
                    v___x_4207_ = crate::leanh::lean_box(0);
                    v_isShared_4208_ = v_isSharedCheck_4219_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_openDecls_4196_);
                crate::leanh::lean_inc(v_currNamespace_4195_);
                v___x_4209_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4209_, 0, v_currNamespace_4195_);
                crate::leanh::lean_ctor_set(v___x_4209_, 1, v_openDecls_4196_);
                v___x_4210_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4210_, 0, v___x_4209_);
                crate::leanh::lean_ctor_set(v___x_4210_, 1, v___y_4191_);
                crate::leanh::lean_inc_ref(v___y_4186_);
                crate::leanh::lean_inc_ref(v___y_4190_);
                v___x_4211_ = crate::leanh::lean_alloc_ctor(0, 5, (3) as u32);
                crate::leanh::lean_ctor_set(v___x_4211_, 0, v___y_4190_);
                crate::leanh::lean_ctor_set(v___x_4211_, 1, v___y_4185_);
                crate::leanh::lean_ctor_set(v___x_4211_, 2, v___y_4188_);
                crate::leanh::lean_ctor_set(v___x_4211_, 3, v___y_4186_);
                crate::leanh::lean_ctor_set(v___x_4211_, 4, v___x_4210_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4211_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v___y_4187_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4211_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_4189_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4211_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_4178_,
                );
                v___x_4212_ = l_Lean_MessageLog_add(v___x_4211_, v_messages_4203_);
                if v_isShared_4208_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4207_, 6, v___x_4212_);
                    v___x_4214_ = v___x_4207_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4218_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4218_, 0, v_env_4197_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4218_, 1, v_nextMacroScope_4198_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4218_, 2, v_ngen_4199_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4218_, 3, v_auxDeclNGen_4200_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4218_, 4, v_traceState_4201_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4218_, 5, v_cache_4202_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4218_, 6, v___x_4212_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4218_, 7, v_infoState_4204_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4218_, 8, v_snapshotTasks_4205_);
                    v___x_4214_ = v_reuseFailAlloc_4218_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4215_ = lean_st_ref_set(v___y_4193_, v___x_4214_);
                v___x_4216_ = crate::leanh::lean_box(0);
                v___x_4217_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4217_, 0, v___x_4216_);
                return v___x_4217_;
            }
            4 => {
                v___x_4229_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_4176_,
                    );
                v___x_4230_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0_spec__0(v___x_4229_, v___y_4179_, v___y_4180_, v___y_4181_, v___y_4182_);
                v_a_4231_ = crate::leanh::lean_ctor_get(v___x_4230_, 0);
                v_isSharedCheck_4244_ = (!crate::leanh::lean_is_exclusive(v___x_4230_)) as u8;
                if v_isSharedCheck_4244_ == 0 {
                    v___x_4233_ = v___x_4230_;
                    v_isShared_4234_ = v_isSharedCheck_4244_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_4231_);
                    crate::leanh::lean_dec(v___x_4230_);
                    v___x_4233_ = crate::leanh::lean_box(0);
                    v_isShared_4234_ = v_isSharedCheck_4244_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc_ref_n(v___y_4222_, 2);
                v___x_4235_ = l_Lean_FileMap_toPosition(v___y_4222_, v___y_4227_);
                crate::leanh::lean_dec(v___y_4227_);
                v___x_4236_ = l_Lean_FileMap_toPosition(v___y_4222_, v___y_4228_);
                crate::leanh::lean_dec(v___y_4228_);
                v___x_4237_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4237_, 0, v___x_4236_);
                v___x_4238_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__11;
                if v___y_4223_ == 0 {
                    crate::leanh::lean_del_object(v___x_4233_);
                    crate::leanh::lean_dec_ref(v___y_4221_);
                    v___y_4185_ = v___x_4235_;
                    v___y_4186_ = v___x_4238_;
                    v___y_4187_ = v___y_4224_;
                    v___y_4188_ = v___x_4237_;
                    v___y_4189_ = v___y_4225_;
                    v___y_4190_ = v___y_4226_;
                    v___y_4191_ = v_a_4231_;
                    v___y_4192_ = v___y_4181_;
                    v___y_4193_ = v___y_4182_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_4231_);
                    v___x_4239_ = l_Lean_MessageData_hasTag(v___y_4221_, v_a_4231_);
                    if v___x_4239_ == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_4237_, 1);
                        crate::leanh::lean_dec_ref(v___x_4235_);
                        crate::leanh::lean_dec(v_a_4231_);
                        v___x_4240_ = crate::leanh::lean_box(0);
                        if v_isShared_4234_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4233_, 0, v___x_4240_);
                            v___x_4242_ = v___x_4233_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_4243_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4243_, 0, v___x_4240_);
                            v___x_4242_ = v_reuseFailAlloc_4243_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_4233_);
                        v___y_4185_ = v___x_4235_;
                        v___y_4186_ = v___x_4238_;
                        v___y_4187_ = v___y_4224_;
                        v___y_4188_ = v___x_4237_;
                        v___y_4189_ = v___y_4225_;
                        v___y_4190_ = v___y_4226_;
                        v___y_4191_ = v_a_4231_;
                        v___y_4192_ = v___y_4181_;
                        v___y_4193_ = v___y_4182_;
                        state = 1;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_4242_;
            }
            7 => {
                v___x_4254_ = l_Lean_Syntax_getTailPos_x3f(v___y_4250_, v___y_4249_);
                crate::leanh::lean_dec(v___y_4250_);
                if crate::leanh::lean_obj_tag(v___x_4254_) == 0 {
                    crate::leanh::lean_inc(v___y_4253_);
                    v___y_4221_ = v___y_4246_;
                    v___y_4222_ = v___y_4247_;
                    v___y_4223_ = v___y_4248_;
                    v___y_4224_ = v___y_4249_;
                    v___y_4225_ = v___y_4251_;
                    v___y_4226_ = v___y_4252_;
                    v___y_4227_ = v___y_4253_;
                    v___y_4228_ = v___y_4253_;
                    state = 4;
                    continue;
                } else {
                    v_val_4255_ = crate::leanh::lean_ctor_get(v___x_4254_, 0);
                    crate::leanh::lean_inc(v_val_4255_);
                    crate::leanh::lean_dec_ref_known(v___x_4254_, 1);
                    v___y_4221_ = v___y_4246_;
                    v___y_4222_ = v___y_4247_;
                    v___y_4223_ = v___y_4248_;
                    v___y_4224_ = v___y_4249_;
                    v___y_4225_ = v___y_4251_;
                    v___y_4226_ = v___y_4252_;
                    v___y_4227_ = v___y_4253_;
                    v___y_4228_ = v_val_4255_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                v_ref_4264_ = l_Lean_replaceRef(v_ref_4175_, v___y_4262_);
                v___x_4265_ = l_Lean_Syntax_getPos_x3f(v_ref_4264_, v___y_4260_);
                if crate::leanh::lean_obj_tag(v___x_4265_) == 0 {
                    v___x_4266_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_4246_ = v___y_4257_;
                    v___y_4247_ = v___y_4258_;
                    v___y_4248_ = v___y_4259_;
                    v___y_4249_ = v___y_4260_;
                    v___y_4250_ = v_ref_4264_;
                    v___y_4251_ = v___y_4263_;
                    v___y_4252_ = v___y_4261_;
                    v___y_4253_ = v___x_4266_;
                    state = 7;
                    continue;
                } else {
                    v_val_4267_ = crate::leanh::lean_ctor_get(v___x_4265_, 0);
                    crate::leanh::lean_inc(v_val_4267_);
                    crate::leanh::lean_dec_ref_known(v___x_4265_, 1);
                    v___y_4246_ = v___y_4257_;
                    v___y_4247_ = v___y_4258_;
                    v___y_4248_ = v___y_4259_;
                    v___y_4249_ = v___y_4260_;
                    v___y_4250_ = v_ref_4264_;
                    v___y_4251_ = v___y_4263_;
                    v___y_4252_ = v___y_4261_;
                    v___y_4253_ = v_val_4267_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if v___y_4276_ == 0 {
                    v___y_4257_ = v___y_4272_;
                    v___y_4258_ = v___y_4270_;
                    v___y_4259_ = v___y_4271_;
                    v___y_4260_ = v___y_4275_;
                    v___y_4261_ = v___y_4274_;
                    v___y_4262_ = v___y_4273_;
                    v___y_4263_ = v_severity_4177_;
                    state = 8;
                    continue;
                } else {
                    v___y_4257_ = v___y_4272_;
                    v___y_4258_ = v___y_4270_;
                    v___y_4259_ = v___y_4271_;
                    v___y_4260_ = v___y_4275_;
                    v___y_4261_ = v___y_4274_;
                    v___y_4262_ = v___y_4273_;
                    v___y_4263_ = v___x_4268_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                if v___y_4278_ == 0 {
                    v_fileName_4279_ = crate::leanh::lean_ctor_get(v___y_4181_, 0);
                    v_fileMap_4280_ = crate::leanh::lean_ctor_get(v___y_4181_, 1);
                    v_options_4281_ = crate::leanh::lean_ctor_get(v___y_4181_, 2);
                    v_ref_4282_ = crate::leanh::lean_ctor_get(v___y_4181_, 5);
                    v_suppressElabErrors_4283_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_4181_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_4284_ = crate::leanh::lean_box((v___y_4278_) as usize);
                    v___x_4285_ = crate::leanh::lean_box((v_suppressElabErrors_4283_) as usize);
                    v___f_4286_ = crate::leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    crate::leanh::lean_closure_set(v___f_4286_, 0, v___x_4284_);
                    crate::leanh::lean_closure_set(v___f_4286_, 1, v___x_4285_);
                    v___x_4287_ = 1;
                    v___x_4288_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4177_, v___x_4287_);
                    if v___x_4288_ == 0 {
                        v___y_4270_ = v_fileMap_4280_;
                        v___y_4271_ = v_suppressElabErrors_4283_;
                        v___y_4272_ = v___f_4286_;
                        v___y_4273_ = v_ref_4282_;
                        v___y_4274_ = v_fileName_4279_;
                        v___y_4275_ = v___y_4278_;
                        v___y_4276_ = v___x_4288_;
                        state = 9;
                        continue;
                    } else {
                        v___x_4289_ = l_Lean_warningAsError;
                        v___x_4290_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__4(v_options_4281_, v___x_4289_);
                        v___y_4270_ = v_fileMap_4280_;
                        v___y_4271_ = v_suppressElabErrors_4283_;
                        v___y_4272_ = v___f_4286_;
                        v___y_4273_ = v_ref_4282_;
                        v___y_4274_ = v_fileName_4279_;
                        v___y_4275_ = v___y_4278_;
                        v___y_4276_ = v___x_4290_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msgData_4176_);
                    v___x_4291_ = crate::leanh::lean_box(0);
                    v___x_4292_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4292_, 0, v___x_4291_);
                    return v___x_4292_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___boxed(
    mut v_ref_4295_: *mut crate::leanh::LeanObject,
    mut v_msgData_4296_: *mut crate::leanh::LeanObject,
    mut v_severity_4297_: *mut crate::leanh::LeanObject,
    mut v_isSilent_4298_: *mut crate::leanh::LeanObject,
    mut v___y_4299_: *mut crate::leanh::LeanObject,
    mut v___y_4300_: *mut crate::leanh::LeanObject,
    mut v___y_4301_: *mut crate::leanh::LeanObject,
    mut v___y_4302_: *mut crate::leanh::LeanObject,
    mut v___y_4303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_4304_: u8 = 0;
    let mut v_isSilent_boxed_4305_: u8 = 0;
    let mut v_res_4306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_4304_ = (crate::leanh::lean_unbox(v_severity_4297_) as u8);
    v_isSilent_boxed_4305_ = (crate::leanh::lean_unbox(v_isSilent_4298_) as u8);
    v_res_4306_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1(v_ref_4295_, v_msgData_4296_, v_severity_boxed_4304_, v_isSilent_boxed_4305_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_);
    crate::leanh::lean_dec(v___y_4302_);
    crate::leanh::lean_dec_ref(v___y_4301_);
    crate::leanh::lean_dec(v___y_4300_);
    crate::leanh::lean_dec_ref(v___y_4299_);
    crate::leanh::lean_dec(v_ref_4295_);
    return v_res_4306_;
}
pub unsafe fn l_Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1(
    mut v_ref_4307_: *mut crate::leanh::LeanObject,
    mut v_msgData_4308_: *mut crate::leanh::LeanObject,
    mut v___y_4309_: *mut crate::leanh::LeanObject,
    mut v___y_4310_: *mut crate::leanh::LeanObject,
    mut v___y_4311_: *mut crate::leanh::LeanObject,
    mut v___y_4312_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4314_: u8 = 0;
    let mut v___x_4315_: u8 = 0;
    let mut v___x_4316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4314_ = 2;
    v___x_4315_ = 0;
    v___x_4316_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1(v_ref_4307_, v_msgData_4308_, v___x_4314_, v___x_4315_, v___y_4309_, v___y_4310_, v___y_4311_, v___y_4312_);
    return v___x_4316_;
}
pub unsafe fn l_Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1___boxed(
    mut v_ref_4317_: *mut crate::leanh::LeanObject,
    mut v_msgData_4318_: *mut crate::leanh::LeanObject,
    mut v___y_4319_: *mut crate::leanh::LeanObject,
    mut v___y_4320_: *mut crate::leanh::LeanObject,
    mut v___y_4321_: *mut crate::leanh::LeanObject,
    mut v___y_4322_: *mut crate::leanh::LeanObject,
    mut v___y_4323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4324_ = l_Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1(
        v_ref_4317_,
        v_msgData_4318_,
        v___y_4319_,
        v___y_4320_,
        v___y_4321_,
        v___y_4322_,
    );
    crate::leanh::lean_dec(v___y_4322_);
    crate::leanh::lean_dec_ref(v___y_4321_);
    crate::leanh::lean_dec(v___y_4320_);
    crate::leanh::lean_dec_ref(v___y_4319_);
    crate::leanh::lean_dec(v_ref_4317_);
    return v_res_4324_;
}
pub unsafe fn _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4328_ = l_Lean_Elab_Term_throwCalcFailure___redArg___closed__1;
    v___x_4329_ = l_Lean_MessageData_ofFormat(v___x_4328_);
    return v___x_4329_;
}
pub unsafe fn _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4330_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Term_throwCalcFailure___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_Term_throwCalcFailure___redArg___closed__2_once),
        _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__2,
    );
    v___x_4331_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4331_, 0, v___x_4330_);
    return v___x_4331_;
}
pub unsafe fn _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4333_ = l_Lean_Elab_Term_throwCalcFailure___redArg___closed__4;
    v___x_4334_ = l_Lean_stringToMessageData(v___x_4333_);
    return v___x_4334_;
}
pub unsafe fn _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4336_ = l_Lean_Elab_Term_throwCalcFailure___redArg___closed__6;
    v___x_4337_ = l_Lean_stringToMessageData(v___x_4336_);
    return v___x_4337_;
}
pub unsafe fn _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4339_ = l_Lean_Elab_Term_mkCalcTrans___closed__10;
    v___x_4340_ = crate::leanh::lean_unsigned_to_nat(57);
    v___x_4341_ = crate::leanh::lean_unsigned_to_nat(133);
    v___x_4342_ = l_Lean_Elab_Term_throwCalcFailure___redArg___closed__8;
    v___x_4343_ = l_Lean_Elab_Term_mkCalcTrans___closed__8;
    v___x_4344_ = l_mkPanicMessageWithDecl(
        v___x_4343_,
        v___x_4342_,
        v___x_4341_,
        v___x_4340_,
        v___x_4339_,
    );
    return v___x_4344_;
}
pub unsafe fn l_Lean_Elab_Term_throwCalcFailure___redArg(
    mut v_steps_4345_: *mut crate::leanh::LeanObject,
    mut v_expectedType_4346_: *mut crate::leanh::LeanObject,
    mut v_result_4347_: *mut crate::leanh::LeanObject,
    mut v_a_4348_: *mut crate::leanh::LeanObject,
    mut v_a_4349_: *mut crate::leanh::LeanObject,
    mut v_a_4350_: *mut crate::leanh::LeanObject,
    mut v_a_4351_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4375_: u8 = 0;
    let mut v___x_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4379_: u8 = 0;
    let mut v___x_4380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4387_: u8 = 0;
    let mut v_fst_4388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4392_: u8 = 0;
    let mut v___x_4393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4400_: u8 = 0;
    let mut v_fst_4401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4405_: u8 = 0;
    let mut v_failed_4407_: u8 = 0;
    let mut v___y_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: u8 = 0;
    let mut v___x_4415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4421_: u8 = 0;
    let mut v___x_4422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4432_: u8 = 0;
    let mut v___x_4433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_term_4438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4465_: u8 = 0;
    let mut v___x_4467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4469_: u8 = 0;
    let mut v_reuseFailAlloc_4470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4476_: u8 = 0;
    let mut v_a_4477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4480_: u8 = 0;
    let mut v___x_4482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4484_: u8 = 0;
    let mut v_a_4485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4488_: u8 = 0;
    let mut v___x_4490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4492_: u8 = 0;
    let mut v_a_4493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4496_: u8 = 0;
    let mut v___x_4498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4500_: u8 = 0;
    let mut v_isSharedCheck_4501_: u8 = 0;
    let mut v_a_4502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4505_: u8 = 0;
    let mut v___x_4507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4509_: u8 = 0;
    let mut v_a_4510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4513_: u8 = 0;
    let mut v___x_4515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4517_: u8 = 0;
    let mut v___x_4518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4520_: u8 = 0;
    let mut v___x_4521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4523_: u8 = 0;
    let mut v___x_4524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4530_: u8 = 0;
    let mut v___x_4531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4541_: u8 = 0;
    let mut v___x_4542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_term_4545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: u8 = 0;
    let mut v_a_4566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4569_: u8 = 0;
    let mut v___x_4571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4573_: u8 = 0;
    let mut v_reuseFailAlloc_4574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4576_: u8 = 0;
    let mut v_a_4577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4580_: u8 = 0;
    let mut v___x_4582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4584_: u8 = 0;
    let mut v_a_4585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4588_: u8 = 0;
    let mut v___x_4590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4592_: u8 = 0;
    let mut v_a_4593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4596_: u8 = 0;
    let mut v___x_4598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4600_: u8 = 0;
    let mut v_isSharedCheck_4601_: u8 = 0;
    let mut v_a_4602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4605_: u8 = 0;
    let mut v___x_4607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4609_: u8 = 0;
    let mut v___x_4610_: u8 = 0;
    let mut v_a_4611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4614_: u8 = 0;
    let mut v___x_4616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4618_: u8 = 0;
    let mut v_a_4619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4622_: u8 = 0;
    let mut v___x_4624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4626_: u8 = 0;
    let mut v_isSharedCheck_4627_: u8 = 0;
    let mut v_isSharedCheck_4628_: u8 = 0;
    let mut v_isSharedCheck_4629_: u8 = 0;
    let mut v_isSharedCheck_4630_: u8 = 0;
    let mut v___x_4631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4636_: u8 = 0;
    let mut v___x_4638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4640_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_4351_);
                crate::leanh::lean_inc_ref(v_a_4350_);
                crate::leanh::lean_inc(v_a_4349_);
                crate::leanh::lean_inc_ref(v_a_4348_);
                crate::leanh::lean_inc_ref(v_result_4347_);
                v___x_4353_ =
                    lean_infer_type(v_result_4347_, v_a_4348_, v_a_4349_, v_a_4350_, v_a_4351_);
                if crate::leanh::lean_obj_tag(v___x_4353_) == 0 {
                    v_a_4354_ = crate::leanh::lean_ctor_get(v___x_4353_, 0);
                    crate::leanh::lean_inc(v_a_4354_);
                    crate::leanh::lean_dec_ref_known(v___x_4353_, 1);
                    v___x_4355_ = l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0___redArg(v_a_4354_, v_a_4349_);
                    v_a_4356_ = crate::leanh::lean_ctor_get(v___x_4355_, 0);
                    crate::leanh::lean_inc(v_a_4356_);
                    crate::leanh::lean_dec_ref(v___x_4355_);
                    v___x_4357_ = l_Lean_Expr_headBeta(v_a_4356_);
                    v___x_4380_ = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(v___x_4357_);
                    v_a_4381_ = crate::leanh::lean_ctor_get(v___x_4380_, 0);
                    crate::leanh::lean_inc(v_a_4381_);
                    crate::leanh::lean_dec_ref(v___x_4380_);
                    if crate::leanh::lean_obj_tag(v_a_4381_) == 1 {
                        v_val_4382_ = crate::leanh::lean_ctor_get(v_a_4381_, 0);
                        crate::leanh::lean_inc(v_val_4382_);
                        crate::leanh::lean_dec_ref_known(v_a_4381_, 1);
                        v_snd_4383_ = crate::leanh::lean_ctor_get(v_val_4382_, 1);
                        v_fst_4384_ = crate::leanh::lean_ctor_get(v_val_4382_, 0);
                        v_isSharedCheck_4630_ =
                            (!crate::leanh::lean_is_exclusive(v_val_4382_)) as u8;
                        if v_isSharedCheck_4630_ == 0 {
                            v___x_4386_ = v_val_4382_;
                            v_isShared_4387_ = v_isSharedCheck_4630_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_4383_);
                            crate::leanh::lean_inc(v_fst_4384_);
                            crate::leanh::lean_dec(v_val_4382_);
                            v___x_4386_ = crate::leanh::lean_box(0);
                            v_isShared_4387_ = v_isSharedCheck_4630_;
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_4381_);
                        crate::leanh::lean_dec_ref(v___x_4357_);
                        crate::leanh::lean_dec_ref(v_result_4347_);
                        crate::leanh::lean_dec_ref(v_expectedType_4346_);
                        v___x_4631_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Term_throwCalcFailure___redArg___closed__9
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Term_throwCalcFailure___redArg___closed__9_once
                            ),
                            _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__9,
                        );
                        v___x_4632_ =
                            l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2___redArg(
                                v___x_4631_,
                                v_a_4348_,
                                v_a_4349_,
                                v_a_4350_,
                                v_a_4351_,
                            );
                        return v___x_4632_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_result_4347_);
                    crate::leanh::lean_dec_ref(v_expectedType_4346_);
                    v_a_4633_ = crate::leanh::lean_ctor_get(v___x_4353_, 0);
                    v_isSharedCheck_4640_ = (!crate::leanh::lean_is_exclusive(v___x_4353_)) as u8;
                    if v_isSharedCheck_4640_ == 0 {
                        v___x_4635_ = v___x_4353_;
                        v_isShared_4636_ = v_isSharedCheck_4640_;
                        state = 48;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4633_);
                        crate::leanh::lean_dec(v___x_4353_);
                        v___x_4635_ = crate::leanh::lean_box(0);
                        v_isShared_4636_ = v_isSharedCheck_4640_;
                        state = 48;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4363_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Term_throwCalcFailure___redArg___closed__3),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Term_throwCalcFailure___redArg___closed__3_once
                    ),
                    _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__3,
                );
                v___x_4364_ = crate::leanh::lean_box(0);
                v___x_4365_ = l_Lean_Elab_Term_throwTypeMismatchError___redArg(
                    v___x_4363_,
                    v_expectedType_4346_,
                    v___x_4357_,
                    v_result_4347_,
                    v___x_4364_,
                    v___y_4359_,
                    v___y_4360_,
                    v___y_4361_,
                    v___y_4362_,
                );
                return v___x_4365_;
            }
            2 => {
                v___x_4371_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg();
                v_a_4372_ = crate::leanh::lean_ctor_get(v___x_4371_, 0);
                v_isSharedCheck_4379_ = (!crate::leanh::lean_is_exclusive(v___x_4371_)) as u8;
                if v_isSharedCheck_4379_ == 0 {
                    v___x_4374_ = v___x_4371_;
                    v_isShared_4375_ = v_isSharedCheck_4379_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_4372_);
                    crate::leanh::lean_dec(v___x_4371_);
                    v___x_4374_ = crate::leanh::lean_box(0);
                    v_isShared_4375_ = v_isSharedCheck_4379_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4375_ == 0 {
                    v___x_4377_ = v___x_4374_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4378_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4378_, 0, v_a_4372_);
                    v___x_4377_ = v_reuseFailAlloc_4378_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4377_;
            }
            5 => {
                v_fst_4388_ = crate::leanh::lean_ctor_get(v_snd_4383_, 0);
                v_snd_4389_ = crate::leanh::lean_ctor_get(v_snd_4383_, 1);
                v_isSharedCheck_4629_ = (!crate::leanh::lean_is_exclusive(v_snd_4383_)) as u8;
                if v_isSharedCheck_4629_ == 0 {
                    v___x_4391_ = v_snd_4383_;
                    v_isShared_4392_ = v_isSharedCheck_4629_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4389_);
                    crate::leanh::lean_inc(v_fst_4388_);
                    crate::leanh::lean_dec(v_snd_4383_);
                    v___x_4391_ = crate::leanh::lean_box(0);
                    v_isShared_4392_ = v_isSharedCheck_4629_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_4393_ = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(v_expectedType_4346_);
                v_a_4394_ = crate::leanh::lean_ctor_get(v___x_4393_, 0);
                crate::leanh::lean_inc(v_a_4394_);
                crate::leanh::lean_dec_ref(v___x_4393_);
                if crate::leanh::lean_obj_tag(v_a_4394_) == 1 {
                    v_val_4395_ = crate::leanh::lean_ctor_get(v_a_4394_, 0);
                    crate::leanh::lean_inc(v_val_4395_);
                    crate::leanh::lean_dec_ref_known(v_a_4394_, 1);
                    v_snd_4396_ = crate::leanh::lean_ctor_get(v_val_4395_, 1);
                    v_fst_4397_ = crate::leanh::lean_ctor_get(v_val_4395_, 0);
                    v_isSharedCheck_4628_ = (!crate::leanh::lean_is_exclusive(v_val_4395_)) as u8;
                    if v_isSharedCheck_4628_ == 0 {
                        v___x_4399_ = v_val_4395_;
                        v_isShared_4400_ = v_isSharedCheck_4628_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4396_);
                        crate::leanh::lean_inc(v_fst_4397_);
                        crate::leanh::lean_dec(v_val_4395_);
                        v___x_4399_ = crate::leanh::lean_box(0);
                        v_isShared_4400_ = v_isSharedCheck_4628_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4394_);
                    crate::leanh::lean_del_object(v___x_4391_);
                    crate::leanh::lean_dec(v_snd_4389_);
                    crate::leanh::lean_dec(v_fst_4388_);
                    crate::leanh::lean_del_object(v___x_4386_);
                    crate::leanh::lean_dec(v_fst_4384_);
                    v___y_4359_ = v_a_4348_;
                    v___y_4360_ = v_a_4349_;
                    v___y_4361_ = v_a_4350_;
                    v___y_4362_ = v_a_4351_;
                    state = 1;
                    continue;
                }
            }
            7 => {
                v_fst_4401_ = crate::leanh::lean_ctor_get(v_snd_4396_, 0);
                v_snd_4402_ = crate::leanh::lean_ctor_get(v_snd_4396_, 1);
                v_isSharedCheck_4627_ = (!crate::leanh::lean_is_exclusive(v_snd_4396_)) as u8;
                if v_isSharedCheck_4627_ == 0 {
                    v___x_4404_ = v_snd_4396_;
                    v_isShared_4405_ = v_isSharedCheck_4627_;
                    state = 8;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4402_);
                    crate::leanh::lean_inc(v_fst_4401_);
                    crate::leanh::lean_dec(v_snd_4396_);
                    v___x_4404_ = crate::leanh::lean_box(0);
                    v_isShared_4405_ = v_isSharedCheck_4627_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_4518_ = l_Lean_Meta_isExprDefEqGuarded(
                    v_fst_4384_,
                    v_fst_4397_,
                    v_a_4348_,
                    v_a_4349_,
                    v_a_4350_,
                    v_a_4351_,
                );
                if crate::leanh::lean_obj_tag(v___x_4518_) == 0 {
                    v_a_4519_ = crate::leanh::lean_ctor_get(v___x_4518_, 0);
                    crate::leanh::lean_inc(v_a_4519_);
                    crate::leanh::lean_dec_ref_known(v___x_4518_, 1);
                    v___x_4520_ = (crate::leanh::lean_unbox(v_a_4519_) as u8);
                    if v___x_4520_ == 0 {
                        crate::leanh::lean_dec(v_a_4519_);
                        crate::leanh::lean_del_object(v___x_4404_);
                        crate::leanh::lean_dec(v_snd_4402_);
                        crate::leanh::lean_dec(v_fst_4401_);
                        crate::leanh::lean_del_object(v___x_4399_);
                        crate::leanh::lean_del_object(v___x_4391_);
                        crate::leanh::lean_dec(v_snd_4389_);
                        crate::leanh::lean_dec(v_fst_4388_);
                        crate::leanh::lean_del_object(v___x_4386_);
                        v___y_4359_ = v_a_4348_;
                        v___y_4360_ = v_a_4349_;
                        v___y_4361_ = v_a_4350_;
                        v___y_4362_ = v_a_4351_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fst_4401_);
                        crate::leanh::lean_inc(v_fst_4388_);
                        v___x_4521_ = l_Lean_Meta_isExprDefEqGuarded(
                            v_fst_4388_,
                            v_fst_4401_,
                            v_a_4348_,
                            v_a_4349_,
                            v_a_4350_,
                            v_a_4351_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4521_) == 0 {
                            v_a_4522_ = crate::leanh::lean_ctor_get(v___x_4521_, 0);
                            crate::leanh::lean_inc(v_a_4522_);
                            crate::leanh::lean_dec_ref_known(v___x_4521_, 1);
                            v___x_4523_ = (crate::leanh::lean_unbox(v_a_4522_) as u8);
                            crate::leanh::lean_dec(v_a_4522_);
                            if v___x_4523_ == 0 {
                                v___x_4524_ = l_Lean_Meta_addPPExplicitToExposeDiff(
                                    v_fst_4388_,
                                    v_fst_4401_,
                                    v_a_4348_,
                                    v_a_4349_,
                                    v_a_4350_,
                                    v_a_4351_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_4524_) == 0 {
                                    v_a_4525_ = crate::leanh::lean_ctor_get(v___x_4524_, 0);
                                    crate::leanh::lean_inc(v_a_4525_);
                                    crate::leanh::lean_dec_ref_known(v___x_4524_, 1);
                                    v_fst_4526_ = crate::leanh::lean_ctor_get(v_a_4525_, 0);
                                    v_snd_4527_ = crate::leanh::lean_ctor_get(v_a_4525_, 1);
                                    v_isSharedCheck_4601_ =
                                        (!crate::leanh::lean_is_exclusive(v_a_4525_)) as u8;
                                    if v_isSharedCheck_4601_ == 0 {
                                        v___x_4529_ = v_a_4525_;
                                        v_isShared_4530_ = v_isSharedCheck_4601_;
                                        state = 30;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_snd_4527_);
                                        crate::leanh::lean_inc(v_fst_4526_);
                                        crate::leanh::lean_dec(v_a_4525_);
                                        v___x_4529_ = crate::leanh::lean_box(0);
                                        v_isShared_4530_ = v_isSharedCheck_4601_;
                                        state = 30;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_4519_);
                                    crate::leanh::lean_del_object(v___x_4404_);
                                    crate::leanh::lean_dec(v_snd_4402_);
                                    crate::leanh::lean_del_object(v___x_4399_);
                                    crate::leanh::lean_del_object(v___x_4391_);
                                    crate::leanh::lean_dec(v_snd_4389_);
                                    crate::leanh::lean_del_object(v___x_4386_);
                                    crate::leanh::lean_dec_ref(v___x_4357_);
                                    crate::leanh::lean_dec_ref(v_result_4347_);
                                    crate::leanh::lean_dec_ref(v_expectedType_4346_);
                                    v_a_4602_ = crate::leanh::lean_ctor_get(v___x_4524_, 0);
                                    v_isSharedCheck_4609_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_4524_)) as u8;
                                    if v_isSharedCheck_4609_ == 0 {
                                        v___x_4604_ = v___x_4524_;
                                        v_isShared_4605_ = v_isSharedCheck_4609_;
                                        state = 42;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_4602_);
                                        crate::leanh::lean_dec(v___x_4524_);
                                        v___x_4604_ = crate::leanh::lean_box(0);
                                        v_isShared_4605_ = v_isSharedCheck_4609_;
                                        state = 42;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_4519_);
                                crate::leanh::lean_dec(v_fst_4401_);
                                crate::leanh::lean_dec(v_fst_4388_);
                                v___x_4610_ = 0;
                                v_failed_4407_ = v___x_4610_;
                                v___y_4408_ = v_a_4348_;
                                v___y_4409_ = v_a_4349_;
                                v___y_4410_ = v_a_4350_;
                                v___y_4411_ = v_a_4351_;
                                state = 9;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_4519_);
                            crate::leanh::lean_del_object(v___x_4404_);
                            crate::leanh::lean_dec(v_snd_4402_);
                            crate::leanh::lean_dec(v_fst_4401_);
                            crate::leanh::lean_del_object(v___x_4399_);
                            crate::leanh::lean_del_object(v___x_4391_);
                            crate::leanh::lean_dec(v_snd_4389_);
                            crate::leanh::lean_dec(v_fst_4388_);
                            crate::leanh::lean_del_object(v___x_4386_);
                            crate::leanh::lean_dec_ref(v___x_4357_);
                            crate::leanh::lean_dec_ref(v_result_4347_);
                            crate::leanh::lean_dec_ref(v_expectedType_4346_);
                            v_a_4611_ = crate::leanh::lean_ctor_get(v___x_4521_, 0);
                            v_isSharedCheck_4618_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4521_)) as u8;
                            if v_isSharedCheck_4618_ == 0 {
                                v___x_4613_ = v___x_4521_;
                                v_isShared_4614_ = v_isSharedCheck_4618_;
                                state = 44;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4611_);
                                crate::leanh::lean_dec(v___x_4521_);
                                v___x_4613_ = crate::leanh::lean_box(0);
                                v_isShared_4614_ = v_isSharedCheck_4618_;
                                state = 44;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4404_);
                    crate::leanh::lean_dec(v_snd_4402_);
                    crate::leanh::lean_dec(v_fst_4401_);
                    crate::leanh::lean_del_object(v___x_4399_);
                    crate::leanh::lean_del_object(v___x_4391_);
                    crate::leanh::lean_dec(v_snd_4389_);
                    crate::leanh::lean_dec(v_fst_4388_);
                    crate::leanh::lean_del_object(v___x_4386_);
                    crate::leanh::lean_dec_ref(v___x_4357_);
                    crate::leanh::lean_dec_ref(v_result_4347_);
                    crate::leanh::lean_dec_ref(v_expectedType_4346_);
                    v_a_4619_ = crate::leanh::lean_ctor_get(v___x_4518_, 0);
                    v_isSharedCheck_4626_ = (!crate::leanh::lean_is_exclusive(v___x_4518_)) as u8;
                    if v_isSharedCheck_4626_ == 0 {
                        v___x_4621_ = v___x_4518_;
                        v_isShared_4622_ = v_isSharedCheck_4626_;
                        state = 46;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4619_);
                        crate::leanh::lean_dec(v___x_4518_);
                        v___x_4621_ = crate::leanh::lean_box(0);
                        v_isShared_4622_ = v_isSharedCheck_4626_;
                        state = 46;
                        continue;
                    }
                }
            }
            9 => {
                crate::leanh::lean_inc(v_snd_4402_);
                crate::leanh::lean_inc(v_snd_4389_);
                v___x_4412_ = l_Lean_Meta_isExprDefEqGuarded(
                    v_snd_4389_,
                    v_snd_4402_,
                    v___y_4408_,
                    v___y_4409_,
                    v___y_4410_,
                    v___y_4411_,
                );
                if crate::leanh::lean_obj_tag(v___x_4412_) == 0 {
                    v_a_4413_ = crate::leanh::lean_ctor_get(v___x_4412_, 0);
                    crate::leanh::lean_inc(v_a_4413_);
                    crate::leanh::lean_dec_ref_known(v___x_4412_, 1);
                    v___x_4414_ = (crate::leanh::lean_unbox(v_a_4413_) as u8);
                    crate::leanh::lean_dec(v_a_4413_);
                    if v___x_4414_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_4357_);
                        crate::leanh::lean_dec_ref(v_result_4347_);
                        crate::leanh::lean_dec_ref(v_expectedType_4346_);
                        v___x_4415_ = l_Lean_Meta_addPPExplicitToExposeDiff(
                            v_snd_4389_,
                            v_snd_4402_,
                            v___y_4408_,
                            v___y_4409_,
                            v___y_4410_,
                            v___y_4411_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4415_) == 0 {
                            v_a_4416_ = crate::leanh::lean_ctor_get(v___x_4415_, 0);
                            crate::leanh::lean_inc(v_a_4416_);
                            crate::leanh::lean_dec_ref_known(v___x_4415_, 1);
                            v_fst_4417_ = crate::leanh::lean_ctor_get(v_a_4416_, 0);
                            v_snd_4418_ = crate::leanh::lean_ctor_get(v_a_4416_, 1);
                            v_isSharedCheck_4501_ =
                                (!crate::leanh::lean_is_exclusive(v_a_4416_)) as u8;
                            if v_isSharedCheck_4501_ == 0 {
                                v___x_4420_ = v_a_4416_;
                                v_isShared_4421_ = v_isSharedCheck_4501_;
                                state = 10;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_snd_4418_);
                                crate::leanh::lean_inc(v_fst_4417_);
                                crate::leanh::lean_dec(v_a_4416_);
                                v___x_4420_ = crate::leanh::lean_box(0);
                                v_isShared_4421_ = v_isSharedCheck_4501_;
                                state = 10;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_4404_);
                            crate::leanh::lean_del_object(v___x_4399_);
                            crate::leanh::lean_del_object(v___x_4391_);
                            crate::leanh::lean_del_object(v___x_4386_);
                            v_a_4502_ = crate::leanh::lean_ctor_get(v___x_4415_, 0);
                            v_isSharedCheck_4509_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4415_)) as u8;
                            if v_isSharedCheck_4509_ == 0 {
                                v___x_4504_ = v___x_4415_;
                                v_isShared_4505_ = v_isSharedCheck_4509_;
                                state = 26;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4502_);
                                crate::leanh::lean_dec(v___x_4415_);
                                v___x_4504_ = crate::leanh::lean_box(0);
                                v_isShared_4505_ = v_isSharedCheck_4509_;
                                state = 26;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_4404_);
                        crate::leanh::lean_dec(v_snd_4402_);
                        crate::leanh::lean_del_object(v___x_4399_);
                        crate::leanh::lean_del_object(v___x_4391_);
                        crate::leanh::lean_dec(v_snd_4389_);
                        crate::leanh::lean_del_object(v___x_4386_);
                        if v_failed_4407_ == 0 {
                            v___y_4359_ = v___y_4408_;
                            v___y_4360_ = v___y_4409_;
                            v___y_4361_ = v___y_4410_;
                            v___y_4362_ = v___y_4411_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v___x_4357_);
                            crate::leanh::lean_dec_ref(v_result_4347_);
                            crate::leanh::lean_dec_ref(v_expectedType_4346_);
                            v___y_4367_ = v___y_4408_;
                            v___y_4368_ = v___y_4409_;
                            v___y_4369_ = v___y_4410_;
                            v___y_4370_ = v___y_4411_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4404_);
                    crate::leanh::lean_dec(v_snd_4402_);
                    crate::leanh::lean_del_object(v___x_4399_);
                    crate::leanh::lean_del_object(v___x_4391_);
                    crate::leanh::lean_dec(v_snd_4389_);
                    crate::leanh::lean_del_object(v___x_4386_);
                    crate::leanh::lean_dec_ref(v___x_4357_);
                    crate::leanh::lean_dec_ref(v_result_4347_);
                    crate::leanh::lean_dec_ref(v_expectedType_4346_);
                    v_a_4510_ = crate::leanh::lean_ctor_get(v___x_4412_, 0);
                    v_isSharedCheck_4517_ = (!crate::leanh::lean_is_exclusive(v___x_4412_)) as u8;
                    if v_isSharedCheck_4517_ == 0 {
                        v___x_4512_ = v___x_4412_;
                        v_isShared_4513_ = v_isSharedCheck_4517_;
                        state = 28;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4510_);
                        crate::leanh::lean_dec(v___x_4412_);
                        v___x_4512_ = crate::leanh::lean_box(0);
                        v_isShared_4513_ = v_isSharedCheck_4517_;
                        state = 28;
                        continue;
                    }
                }
            }
            10 => {
                crate::leanh::lean_inc(v___y_4411_);
                crate::leanh::lean_inc_ref(v___y_4410_);
                crate::leanh::lean_inc(v___y_4409_);
                crate::leanh::lean_inc_ref(v___y_4408_);
                crate::leanh::lean_inc(v_fst_4417_);
                v___x_4422_ = lean_infer_type(
                    v_fst_4417_,
                    v___y_4408_,
                    v___y_4409_,
                    v___y_4410_,
                    v___y_4411_,
                );
                if crate::leanh::lean_obj_tag(v___x_4422_) == 0 {
                    v_a_4423_ = crate::leanh::lean_ctor_get(v___x_4422_, 0);
                    crate::leanh::lean_inc(v_a_4423_);
                    crate::leanh::lean_dec_ref_known(v___x_4422_, 1);
                    crate::leanh::lean_inc(v___y_4411_);
                    crate::leanh::lean_inc_ref(v___y_4410_);
                    crate::leanh::lean_inc(v___y_4409_);
                    crate::leanh::lean_inc_ref(v___y_4408_);
                    crate::leanh::lean_inc(v_snd_4418_);
                    v___x_4424_ = lean_infer_type(
                        v_snd_4418_,
                        v___y_4408_,
                        v___y_4409_,
                        v___y_4410_,
                        v___y_4411_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4424_) == 0 {
                        v_a_4425_ = crate::leanh::lean_ctor_get(v___x_4424_, 0);
                        crate::leanh::lean_inc(v_a_4425_);
                        crate::leanh::lean_dec_ref_known(v___x_4424_, 1);
                        v___x_4426_ = l_Lean_Meta_addPPExplicitToExposeDiff(
                            v_a_4423_,
                            v_a_4425_,
                            v___y_4408_,
                            v___y_4409_,
                            v___y_4410_,
                            v___y_4411_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4426_) == 0 {
                            v_a_4427_ = crate::leanh::lean_ctor_get(v___x_4426_, 0);
                            crate::leanh::lean_inc(v_a_4427_);
                            crate::leanh::lean_dec_ref_known(v___x_4426_, 1);
                            v_fst_4428_ = crate::leanh::lean_ctor_get(v_a_4427_, 0);
                            v_snd_4429_ = crate::leanh::lean_ctor_get(v_a_4427_, 1);
                            v_isSharedCheck_4476_ =
                                (!crate::leanh::lean_is_exclusive(v_a_4427_)) as u8;
                            if v_isSharedCheck_4476_ == 0 {
                                v___x_4431_ = v_a_4427_;
                                v_isShared_4432_ = v_isSharedCheck_4476_;
                                state = 11;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_snd_4429_);
                                crate::leanh::lean_inc(v_fst_4428_);
                                crate::leanh::lean_dec(v_a_4427_);
                                v___x_4431_ = crate::leanh::lean_box(0);
                                v_isShared_4432_ = v_isSharedCheck_4476_;
                                state = 11;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_4420_);
                            crate::leanh::lean_dec(v_snd_4418_);
                            crate::leanh::lean_dec(v_fst_4417_);
                            crate::leanh::lean_del_object(v___x_4404_);
                            crate::leanh::lean_del_object(v___x_4399_);
                            crate::leanh::lean_del_object(v___x_4391_);
                            crate::leanh::lean_del_object(v___x_4386_);
                            v_a_4477_ = crate::leanh::lean_ctor_get(v___x_4426_, 0);
                            v_isSharedCheck_4484_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4426_)) as u8;
                            if v_isSharedCheck_4484_ == 0 {
                                v___x_4479_ = v___x_4426_;
                                v_isShared_4480_ = v_isSharedCheck_4484_;
                                state = 20;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4477_);
                                crate::leanh::lean_dec(v___x_4426_);
                                v___x_4479_ = crate::leanh::lean_box(0);
                                v_isShared_4480_ = v_isSharedCheck_4484_;
                                state = 20;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_4423_);
                        crate::leanh::lean_del_object(v___x_4420_);
                        crate::leanh::lean_dec(v_snd_4418_);
                        crate::leanh::lean_dec(v_fst_4417_);
                        crate::leanh::lean_del_object(v___x_4404_);
                        crate::leanh::lean_del_object(v___x_4399_);
                        crate::leanh::lean_del_object(v___x_4391_);
                        crate::leanh::lean_del_object(v___x_4386_);
                        v_a_4485_ = crate::leanh::lean_ctor_get(v___x_4424_, 0);
                        v_isSharedCheck_4492_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4424_)) as u8;
                        if v_isSharedCheck_4492_ == 0 {
                            v___x_4487_ = v___x_4424_;
                            v_isShared_4488_ = v_isSharedCheck_4492_;
                            state = 22;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4485_);
                            crate::leanh::lean_dec(v___x_4424_);
                            v___x_4487_ = crate::leanh::lean_box(0);
                            v_isShared_4488_ = v_isSharedCheck_4492_;
                            state = 22;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4420_);
                    crate::leanh::lean_dec(v_snd_4418_);
                    crate::leanh::lean_dec(v_fst_4417_);
                    crate::leanh::lean_del_object(v___x_4404_);
                    crate::leanh::lean_del_object(v___x_4399_);
                    crate::leanh::lean_del_object(v___x_4391_);
                    crate::leanh::lean_del_object(v___x_4386_);
                    v_a_4493_ = crate::leanh::lean_ctor_get(v___x_4422_, 0);
                    v_isSharedCheck_4500_ = (!crate::leanh::lean_is_exclusive(v___x_4422_)) as u8;
                    if v_isSharedCheck_4500_ == 0 {
                        v___x_4495_ = v___x_4422_;
                        v_isShared_4496_ = v_isSharedCheck_4500_;
                        state = 24;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4493_);
                        crate::leanh::lean_dec(v___x_4422_);
                        v___x_4495_ = crate::leanh::lean_box(0);
                        v_isShared_4496_ = v_isSharedCheck_4500_;
                        state = 24;
                        continue;
                    }
                }
            }
            11 => {
                v___x_4433_ = l_Lean_Elab_Term_instInhabitedCalcStepView_default;
                v___x_4434_ = lean_array_get_size(v_steps_4345_);
                v___x_4435_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4436_ = lean_nat_sub(v___x_4434_, v___x_4435_);
                v___x_4437_ = lean_array_get_borrowed(v___x_4433_, v_steps_4345_, v___x_4436_);
                crate::leanh::lean_dec(v___x_4436_);
                v_term_4438_ = crate::leanh::lean_ctor_get(v___x_4437_, 1);
                v___x_4439_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Term_throwCalcFailure___redArg___closed__5),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Term_throwCalcFailure___redArg___closed__5_once
                    ),
                    _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__5,
                );
                v___x_4440_ = l_Lean_MessageData_ofExpr(v_fst_4417_);
                v___x_4441_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3);
                if v_isShared_4432_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4431_, 7);
                    crate::leanh::lean_ctor_set(v___x_4431_, 1, v___x_4441_);
                    crate::leanh::lean_ctor_set(v___x_4431_, 0, v___x_4440_);
                    v___x_4443_ = v___x_4431_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4475_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4475_, 0, v___x_4440_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4475_, 1, v___x_4441_);
                    v___x_4443_ = v_reuseFailAlloc_4475_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_4444_ = l_Lean_MessageData_ofExpr(v_fst_4428_);
                if v_isShared_4421_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4420_, 7);
                    crate::leanh::lean_ctor_set(v___x_4420_, 1, v___x_4444_);
                    crate::leanh::lean_ctor_set(v___x_4420_, 0, v___x_4443_);
                    v___x_4446_ = v___x_4420_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4474_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4474_, 0, v___x_4443_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4474_, 1, v___x_4444_);
                    v___x_4446_ = v_reuseFailAlloc_4474_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_4447_ = l_Lean_indentD(v___x_4446_);
                if v_isShared_4405_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4404_, 7);
                    crate::leanh::lean_ctor_set(v___x_4404_, 1, v___x_4447_);
                    crate::leanh::lean_ctor_set(v___x_4404_, 0, v___x_4439_);
                    v___x_4449_ = v___x_4404_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4473_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4473_, 0, v___x_4439_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4473_, 1, v___x_4447_);
                    v___x_4449_ = v_reuseFailAlloc_4473_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_4450_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Term_throwCalcFailure___redArg___closed__7),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Term_throwCalcFailure___redArg___closed__7_once
                    ),
                    _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__7,
                );
                if v_isShared_4400_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4399_, 7);
                    crate::leanh::lean_ctor_set(v___x_4399_, 1, v___x_4450_);
                    crate::leanh::lean_ctor_set(v___x_4399_, 0, v___x_4449_);
                    v___x_4452_ = v___x_4399_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4472_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4472_, 0, v___x_4449_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4472_, 1, v___x_4450_);
                    v___x_4452_ = v_reuseFailAlloc_4472_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___x_4453_ = l_Lean_MessageData_ofExpr(v_snd_4418_);
                if v_isShared_4392_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4391_, 7);
                    crate::leanh::lean_ctor_set(v___x_4391_, 1, v___x_4441_);
                    crate::leanh::lean_ctor_set(v___x_4391_, 0, v___x_4453_);
                    v___x_4455_ = v___x_4391_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4471_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4471_, 0, v___x_4453_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4471_, 1, v___x_4441_);
                    v___x_4455_ = v_reuseFailAlloc_4471_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___x_4456_ = l_Lean_MessageData_ofExpr(v_snd_4429_);
                if v_isShared_4387_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4386_, 7);
                    crate::leanh::lean_ctor_set(v___x_4386_, 1, v___x_4456_);
                    crate::leanh::lean_ctor_set(v___x_4386_, 0, v___x_4455_);
                    v___x_4458_ = v___x_4386_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_4470_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4470_, 0, v___x_4455_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4470_, 1, v___x_4456_);
                    v___x_4458_ = v_reuseFailAlloc_4470_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_4459_ = l_Lean_indentD(v___x_4458_);
                v___x_4460_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4460_, 0, v___x_4452_);
                crate::leanh::lean_ctor_set(v___x_4460_, 1, v___x_4459_);
                v___x_4461_ = l_Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1(
                    v_term_4438_,
                    v___x_4460_,
                    v___y_4408_,
                    v___y_4409_,
                    v___y_4410_,
                    v___y_4411_,
                );
                if crate::leanh::lean_obj_tag(v___x_4461_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_4461_, 1);
                    v___y_4367_ = v___y_4408_;
                    v___y_4368_ = v___y_4409_;
                    v___y_4369_ = v___y_4410_;
                    v___y_4370_ = v___y_4411_;
                    state = 2;
                    continue;
                } else {
                    v_a_4462_ = crate::leanh::lean_ctor_get(v___x_4461_, 0);
                    v_isSharedCheck_4469_ = (!crate::leanh::lean_is_exclusive(v___x_4461_)) as u8;
                    if v_isSharedCheck_4469_ == 0 {
                        v___x_4464_ = v___x_4461_;
                        v_isShared_4465_ = v_isSharedCheck_4469_;
                        state = 18;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4462_);
                        crate::leanh::lean_dec(v___x_4461_);
                        v___x_4464_ = crate::leanh::lean_box(0);
                        v_isShared_4465_ = v_isSharedCheck_4469_;
                        state = 18;
                        continue;
                    }
                }
            }
            18 => {
                if v_isShared_4465_ == 0 {
                    v___x_4467_ = v___x_4464_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_4468_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4468_, 0, v_a_4462_);
                    v___x_4467_ = v_reuseFailAlloc_4468_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_4467_;
            }
            20 => {
                if v_isShared_4480_ == 0 {
                    v___x_4482_ = v___x_4479_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_4483_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4483_, 0, v_a_4477_);
                    v___x_4482_ = v_reuseFailAlloc_4483_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_4482_;
            }
            22 => {
                if v_isShared_4488_ == 0 {
                    v___x_4490_ = v___x_4487_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_4491_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4491_, 0, v_a_4485_);
                    v___x_4490_ = v_reuseFailAlloc_4491_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_4490_;
            }
            24 => {
                if v_isShared_4496_ == 0 {
                    v___x_4498_ = v___x_4495_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_4499_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4499_, 0, v_a_4493_);
                    v___x_4498_ = v_reuseFailAlloc_4499_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_4498_;
            }
            26 => {
                if v_isShared_4505_ == 0 {
                    v___x_4507_ = v___x_4504_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_4508_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4508_, 0, v_a_4502_);
                    v___x_4507_ = v_reuseFailAlloc_4508_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_4507_;
            }
            28 => {
                if v_isShared_4513_ == 0 {
                    v___x_4515_ = v___x_4512_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_4516_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4516_, 0, v_a_4510_);
                    v___x_4515_ = v_reuseFailAlloc_4516_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_4515_;
            }
            30 => {
                crate::leanh::lean_inc(v_a_4351_);
                crate::leanh::lean_inc_ref(v_a_4350_);
                crate::leanh::lean_inc(v_a_4349_);
                crate::leanh::lean_inc_ref(v_a_4348_);
                crate::leanh::lean_inc(v_fst_4526_);
                v___x_4531_ =
                    lean_infer_type(v_fst_4526_, v_a_4348_, v_a_4349_, v_a_4350_, v_a_4351_);
                if crate::leanh::lean_obj_tag(v___x_4531_) == 0 {
                    v_a_4532_ = crate::leanh::lean_ctor_get(v___x_4531_, 0);
                    crate::leanh::lean_inc(v_a_4532_);
                    crate::leanh::lean_dec_ref_known(v___x_4531_, 1);
                    crate::leanh::lean_inc(v_a_4351_);
                    crate::leanh::lean_inc_ref(v_a_4350_);
                    crate::leanh::lean_inc(v_a_4349_);
                    crate::leanh::lean_inc_ref(v_a_4348_);
                    crate::leanh::lean_inc(v_snd_4527_);
                    v___x_4533_ =
                        lean_infer_type(v_snd_4527_, v_a_4348_, v_a_4349_, v_a_4350_, v_a_4351_);
                    if crate::leanh::lean_obj_tag(v___x_4533_) == 0 {
                        v_a_4534_ = crate::leanh::lean_ctor_get(v___x_4533_, 0);
                        crate::leanh::lean_inc(v_a_4534_);
                        crate::leanh::lean_dec_ref_known(v___x_4533_, 1);
                        v___x_4535_ = l_Lean_Meta_addPPExplicitToExposeDiff(
                            v_a_4532_, v_a_4534_, v_a_4348_, v_a_4349_, v_a_4350_, v_a_4351_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4535_) == 0 {
                            v_a_4536_ = crate::leanh::lean_ctor_get(v___x_4535_, 0);
                            crate::leanh::lean_inc(v_a_4536_);
                            crate::leanh::lean_dec_ref_known(v___x_4535_, 1);
                            v_fst_4537_ = crate::leanh::lean_ctor_get(v_a_4536_, 0);
                            v_snd_4538_ = crate::leanh::lean_ctor_get(v_a_4536_, 1);
                            v_isSharedCheck_4576_ =
                                (!crate::leanh::lean_is_exclusive(v_a_4536_)) as u8;
                            if v_isSharedCheck_4576_ == 0 {
                                v___x_4540_ = v_a_4536_;
                                v_isShared_4541_ = v_isSharedCheck_4576_;
                                state = 31;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_snd_4538_);
                                crate::leanh::lean_inc(v_fst_4537_);
                                crate::leanh::lean_dec(v_a_4536_);
                                v___x_4540_ = crate::leanh::lean_box(0);
                                v_isShared_4541_ = v_isSharedCheck_4576_;
                                state = 31;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_4529_);
                            crate::leanh::lean_dec(v_snd_4527_);
                            crate::leanh::lean_dec(v_fst_4526_);
                            crate::leanh::lean_dec(v_a_4519_);
                            crate::leanh::lean_del_object(v___x_4404_);
                            crate::leanh::lean_dec(v_snd_4402_);
                            crate::leanh::lean_del_object(v___x_4399_);
                            crate::leanh::lean_del_object(v___x_4391_);
                            crate::leanh::lean_dec(v_snd_4389_);
                            crate::leanh::lean_del_object(v___x_4386_);
                            crate::leanh::lean_dec_ref(v___x_4357_);
                            crate::leanh::lean_dec_ref(v_result_4347_);
                            crate::leanh::lean_dec_ref(v_expectedType_4346_);
                            v_a_4577_ = crate::leanh::lean_ctor_get(v___x_4535_, 0);
                            v_isSharedCheck_4584_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4535_)) as u8;
                            if v_isSharedCheck_4584_ == 0 {
                                v___x_4579_ = v___x_4535_;
                                v_isShared_4580_ = v_isSharedCheck_4584_;
                                state = 36;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4577_);
                                crate::leanh::lean_dec(v___x_4535_);
                                v___x_4579_ = crate::leanh::lean_box(0);
                                v_isShared_4580_ = v_isSharedCheck_4584_;
                                state = 36;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_4532_);
                        crate::leanh::lean_del_object(v___x_4529_);
                        crate::leanh::lean_dec(v_snd_4527_);
                        crate::leanh::lean_dec(v_fst_4526_);
                        crate::leanh::lean_dec(v_a_4519_);
                        crate::leanh::lean_del_object(v___x_4404_);
                        crate::leanh::lean_dec(v_snd_4402_);
                        crate::leanh::lean_del_object(v___x_4399_);
                        crate::leanh::lean_del_object(v___x_4391_);
                        crate::leanh::lean_dec(v_snd_4389_);
                        crate::leanh::lean_del_object(v___x_4386_);
                        crate::leanh::lean_dec_ref(v___x_4357_);
                        crate::leanh::lean_dec_ref(v_result_4347_);
                        crate::leanh::lean_dec_ref(v_expectedType_4346_);
                        v_a_4585_ = crate::leanh::lean_ctor_get(v___x_4533_, 0);
                        v_isSharedCheck_4592_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4533_)) as u8;
                        if v_isSharedCheck_4592_ == 0 {
                            v___x_4587_ = v___x_4533_;
                            v_isShared_4588_ = v_isSharedCheck_4592_;
                            state = 38;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4585_);
                            crate::leanh::lean_dec(v___x_4533_);
                            v___x_4587_ = crate::leanh::lean_box(0);
                            v_isShared_4588_ = v_isSharedCheck_4592_;
                            state = 38;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4529_);
                    crate::leanh::lean_dec(v_snd_4527_);
                    crate::leanh::lean_dec(v_fst_4526_);
                    crate::leanh::lean_dec(v_a_4519_);
                    crate::leanh::lean_del_object(v___x_4404_);
                    crate::leanh::lean_dec(v_snd_4402_);
                    crate::leanh::lean_del_object(v___x_4399_);
                    crate::leanh::lean_del_object(v___x_4391_);
                    crate::leanh::lean_dec(v_snd_4389_);
                    crate::leanh::lean_del_object(v___x_4386_);
                    crate::leanh::lean_dec_ref(v___x_4357_);
                    crate::leanh::lean_dec_ref(v_result_4347_);
                    crate::leanh::lean_dec_ref(v_expectedType_4346_);
                    v_a_4593_ = crate::leanh::lean_ctor_get(v___x_4531_, 0);
                    v_isSharedCheck_4600_ = (!crate::leanh::lean_is_exclusive(v___x_4531_)) as u8;
                    if v_isSharedCheck_4600_ == 0 {
                        v___x_4595_ = v___x_4531_;
                        v_isShared_4596_ = v_isSharedCheck_4600_;
                        state = 40;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4593_);
                        crate::leanh::lean_dec(v___x_4531_);
                        v___x_4595_ = crate::leanh::lean_box(0);
                        v_isShared_4596_ = v_isSharedCheck_4600_;
                        state = 40;
                        continue;
                    }
                }
            }
            31 => {
                v___x_4542_ = l_Lean_Elab_Term_instInhabitedCalcStepView_default;
                v___x_4543_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4544_ = lean_array_get_borrowed(v___x_4542_, v_steps_4345_, v___x_4543_);
                v_term_4545_ = crate::leanh::lean_ctor_get(v___x_4544_, 1);
                v___x_4546_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__1);
                v___x_4547_ = l_Lean_MessageData_ofExpr(v_fst_4526_);
                v___x_4548_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3);
                if v_isShared_4541_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4540_, 7);
                    crate::leanh::lean_ctor_set(v___x_4540_, 1, v___x_4548_);
                    crate::leanh::lean_ctor_set(v___x_4540_, 0, v___x_4547_);
                    v___x_4550_ = v___x_4540_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_4575_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4575_, 0, v___x_4547_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4575_, 1, v___x_4548_);
                    v___x_4550_ = v_reuseFailAlloc_4575_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                v___x_4551_ = l_Lean_MessageData_ofExpr(v_fst_4537_);
                if v_isShared_4530_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4529_, 7);
                    crate::leanh::lean_ctor_set(v___x_4529_, 1, v___x_4551_);
                    crate::leanh::lean_ctor_set(v___x_4529_, 0, v___x_4550_);
                    v___x_4553_ = v___x_4529_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_4574_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4574_, 0, v___x_4550_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4574_, 1, v___x_4551_);
                    v___x_4553_ = v_reuseFailAlloc_4574_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                v___x_4554_ = l_Lean_indentD(v___x_4553_);
                v___x_4555_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4555_, 0, v___x_4546_);
                crate::leanh::lean_ctor_set(v___x_4555_, 1, v___x_4554_);
                v___x_4556_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Term_throwCalcFailure___redArg___closed__7),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Term_throwCalcFailure___redArg___closed__7_once
                    ),
                    _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__7,
                );
                v___x_4557_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4557_, 0, v___x_4555_);
                crate::leanh::lean_ctor_set(v___x_4557_, 1, v___x_4556_);
                v___x_4558_ = l_Lean_MessageData_ofExpr(v_snd_4527_);
                v___x_4559_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4559_, 0, v___x_4558_);
                crate::leanh::lean_ctor_set(v___x_4559_, 1, v___x_4548_);
                v___x_4560_ = l_Lean_MessageData_ofExpr(v_snd_4538_);
                v___x_4561_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4561_, 0, v___x_4559_);
                crate::leanh::lean_ctor_set(v___x_4561_, 1, v___x_4560_);
                v___x_4562_ = l_Lean_indentD(v___x_4561_);
                v___x_4563_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4563_, 0, v___x_4557_);
                crate::leanh::lean_ctor_set(v___x_4563_, 1, v___x_4562_);
                v___x_4564_ = l_Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1(
                    v_term_4545_,
                    v___x_4563_,
                    v_a_4348_,
                    v_a_4349_,
                    v_a_4350_,
                    v_a_4351_,
                );
                if crate::leanh::lean_obj_tag(v___x_4564_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_4564_, 1);
                    v___x_4565_ = (crate::leanh::lean_unbox(v_a_4519_) as u8);
                    crate::leanh::lean_dec(v_a_4519_);
                    v_failed_4407_ = v___x_4565_;
                    v___y_4408_ = v_a_4348_;
                    v___y_4409_ = v_a_4349_;
                    v___y_4410_ = v_a_4350_;
                    v___y_4411_ = v_a_4351_;
                    state = 9;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_a_4519_);
                    crate::leanh::lean_del_object(v___x_4404_);
                    crate::leanh::lean_dec(v_snd_4402_);
                    crate::leanh::lean_del_object(v___x_4399_);
                    crate::leanh::lean_del_object(v___x_4391_);
                    crate::leanh::lean_dec(v_snd_4389_);
                    crate::leanh::lean_del_object(v___x_4386_);
                    crate::leanh::lean_dec_ref(v___x_4357_);
                    crate::leanh::lean_dec_ref(v_result_4347_);
                    crate::leanh::lean_dec_ref(v_expectedType_4346_);
                    v_a_4566_ = crate::leanh::lean_ctor_get(v___x_4564_, 0);
                    v_isSharedCheck_4573_ = (!crate::leanh::lean_is_exclusive(v___x_4564_)) as u8;
                    if v_isSharedCheck_4573_ == 0 {
                        v___x_4568_ = v___x_4564_;
                        v_isShared_4569_ = v_isSharedCheck_4573_;
                        state = 34;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4566_);
                        crate::leanh::lean_dec(v___x_4564_);
                        v___x_4568_ = crate::leanh::lean_box(0);
                        v_isShared_4569_ = v_isSharedCheck_4573_;
                        state = 34;
                        continue;
                    }
                }
            }
            34 => {
                if v_isShared_4569_ == 0 {
                    v___x_4571_ = v___x_4568_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_4572_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4572_, 0, v_a_4566_);
                    v___x_4571_ = v_reuseFailAlloc_4572_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_4571_;
            }
            36 => {
                if v_isShared_4580_ == 0 {
                    v___x_4582_ = v___x_4579_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_4583_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4583_, 0, v_a_4577_);
                    v___x_4582_ = v_reuseFailAlloc_4583_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_4582_;
            }
            38 => {
                if v_isShared_4588_ == 0 {
                    v___x_4590_ = v___x_4587_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_4591_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4591_, 0, v_a_4585_);
                    v___x_4590_ = v_reuseFailAlloc_4591_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_4590_;
            }
            40 => {
                if v_isShared_4596_ == 0 {
                    v___x_4598_ = v___x_4595_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_4599_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4599_, 0, v_a_4593_);
                    v___x_4598_ = v_reuseFailAlloc_4599_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_4598_;
            }
            42 => {
                if v_isShared_4605_ == 0 {
                    v___x_4607_ = v___x_4604_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_4608_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4608_, 0, v_a_4602_);
                    v___x_4607_ = v_reuseFailAlloc_4608_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                return v___x_4607_;
            }
            44 => {
                if v_isShared_4614_ == 0 {
                    v___x_4616_ = v___x_4613_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_4617_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4617_, 0, v_a_4611_);
                    v___x_4616_ = v_reuseFailAlloc_4617_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                return v___x_4616_;
            }
            46 => {
                if v_isShared_4622_ == 0 {
                    v___x_4624_ = v___x_4621_;
                    state = 47;
                    continue;
                } else {
                    v_reuseFailAlloc_4625_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4625_, 0, v_a_4619_);
                    v___x_4624_ = v_reuseFailAlloc_4625_;
                    state = 47;
                    continue;
                }
            }
            47 => {
                return v___x_4624_;
            }
            48 => {
                if v_isShared_4636_ == 0 {
                    v___x_4638_ = v___x_4635_;
                    state = 49;
                    continue;
                } else {
                    v_reuseFailAlloc_4639_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4639_, 0, v_a_4633_);
                    v___x_4638_ = v_reuseFailAlloc_4639_;
                    state = 49;
                    continue;
                }
            }
            49 => {
                return v___x_4638_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_throwCalcFailure___redArg___boxed(
    mut v_steps_4641_: *mut crate::leanh::LeanObject,
    mut v_expectedType_4642_: *mut crate::leanh::LeanObject,
    mut v_result_4643_: *mut crate::leanh::LeanObject,
    mut v_a_4644_: *mut crate::leanh::LeanObject,
    mut v_a_4645_: *mut crate::leanh::LeanObject,
    mut v_a_4646_: *mut crate::leanh::LeanObject,
    mut v_a_4647_: *mut crate::leanh::LeanObject,
    mut v_a_4648_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4649_ = l_Lean_Elab_Term_throwCalcFailure___redArg(
        v_steps_4641_,
        v_expectedType_4642_,
        v_result_4643_,
        v_a_4644_,
        v_a_4645_,
        v_a_4646_,
        v_a_4647_,
    );
    crate::leanh::lean_dec(v_a_4647_);
    crate::leanh::lean_dec_ref(v_a_4646_);
    crate::leanh::lean_dec(v_a_4645_);
    crate::leanh::lean_dec_ref(v_a_4644_);
    crate::leanh::lean_dec_ref(v_steps_4641_);
    return v_res_4649_;
}
pub unsafe fn l_Lean_Elab_Term_throwCalcFailure(
    mut v_00_u03b1_4650_: *mut crate::leanh::LeanObject,
    mut v_steps_4651_: *mut crate::leanh::LeanObject,
    mut v_expectedType_4652_: *mut crate::leanh::LeanObject,
    mut v_result_4653_: *mut crate::leanh::LeanObject,
    mut v_a_4654_: *mut crate::leanh::LeanObject,
    mut v_a_4655_: *mut crate::leanh::LeanObject,
    mut v_a_4656_: *mut crate::leanh::LeanObject,
    mut v_a_4657_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4659_ = l_Lean_Elab_Term_throwCalcFailure___redArg(
        v_steps_4651_,
        v_expectedType_4652_,
        v_result_4653_,
        v_a_4654_,
        v_a_4655_,
        v_a_4656_,
        v_a_4657_,
    );
    return v___x_4659_;
}
pub unsafe fn l_Lean_Elab_Term_throwCalcFailure___boxed(
    mut v_00_u03b1_4660_: *mut crate::leanh::LeanObject,
    mut v_steps_4661_: *mut crate::leanh::LeanObject,
    mut v_expectedType_4662_: *mut crate::leanh::LeanObject,
    mut v_result_4663_: *mut crate::leanh::LeanObject,
    mut v_a_4664_: *mut crate::leanh::LeanObject,
    mut v_a_4665_: *mut crate::leanh::LeanObject,
    mut v_a_4666_: *mut crate::leanh::LeanObject,
    mut v_a_4667_: *mut crate::leanh::LeanObject,
    mut v_a_4668_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4669_ = l_Lean_Elab_Term_throwCalcFailure(
        v_00_u03b1_4660_,
        v_steps_4661_,
        v_expectedType_4662_,
        v_result_4663_,
        v_a_4664_,
        v_a_4665_,
        v_a_4666_,
        v_a_4667_,
    );
    crate::leanh::lean_dec(v_a_4667_);
    crate::leanh::lean_dec_ref(v_a_4666_);
    crate::leanh::lean_dec(v_a_4665_);
    crate::leanh::lean_dec_ref(v_a_4664_);
    crate::leanh::lean_dec_ref(v_steps_4661_);
    return v_res_4669_;
}
pub unsafe fn l_Lean_Elab_Term_elabCalc___lam__0(
    mut v_a_4670_: *mut crate::leanh::LeanObject,
    mut v_x_4671_: *mut crate::leanh::LeanObject,
    mut v___y_4672_: *mut crate::leanh::LeanObject,
    mut v___y_4673_: *mut crate::leanh::LeanObject,
    mut v___y_4674_: *mut crate::leanh::LeanObject,
    mut v___y_4675_: *mut crate::leanh::LeanObject,
    mut v___y_4676_: *mut crate::leanh::LeanObject,
    mut v___y_4677_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4679_ = l_Lean_Elab_Term_throwCalcFailure___redArg(
        v_a_4670_,
        v___y_4672_,
        v___y_4673_,
        v___y_4674_,
        v___y_4675_,
        v___y_4676_,
        v___y_4677_,
    );
    return v___x_4679_;
}
pub unsafe fn l_Lean_Elab_Term_elabCalc___lam__0___boxed(
    mut v_a_4680_: *mut crate::leanh::LeanObject,
    mut v_x_4681_: *mut crate::leanh::LeanObject,
    mut v___y_4682_: *mut crate::leanh::LeanObject,
    mut v___y_4683_: *mut crate::leanh::LeanObject,
    mut v___y_4684_: *mut crate::leanh::LeanObject,
    mut v___y_4685_: *mut crate::leanh::LeanObject,
    mut v___y_4686_: *mut crate::leanh::LeanObject,
    mut v___y_4687_: *mut crate::leanh::LeanObject,
    mut v___y_4688_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4689_ = l_Lean_Elab_Term_elabCalc___lam__0(
        v_a_4680_,
        v_x_4681_,
        v___y_4682_,
        v___y_4683_,
        v___y_4684_,
        v___y_4685_,
        v___y_4686_,
        v___y_4687_,
    );
    crate::leanh::lean_dec(v___y_4687_);
    crate::leanh::lean_dec_ref(v___y_4686_);
    crate::leanh::lean_dec(v___y_4685_);
    crate::leanh::lean_dec_ref(v___y_4684_);
    crate::leanh::lean_dec(v_x_4681_);
    crate::leanh::lean_dec_ref(v_a_4680_);
    return v_res_4689_;
}
pub unsafe fn l_Lean_Elab_Term_elabCalc___lam__1(
    mut v_a_4690_: *mut crate::leanh::LeanObject,
    mut v_x_4691_: *mut crate::leanh::LeanObject,
    mut v___y_4692_: *mut crate::leanh::LeanObject,
    mut v___y_4693_: *mut crate::leanh::LeanObject,
    mut v___y_4694_: *mut crate::leanh::LeanObject,
    mut v___y_4695_: *mut crate::leanh::LeanObject,
    mut v___y_4696_: *mut crate::leanh::LeanObject,
    mut v___y_4697_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4699_ = l_Lean_Elab_Term_throwCalcFailure___redArg(
        v_a_4690_,
        v___y_4692_,
        v___y_4693_,
        v___y_4694_,
        v___y_4695_,
        v___y_4696_,
        v___y_4697_,
    );
    return v___x_4699_;
}
pub unsafe fn l_Lean_Elab_Term_elabCalc___lam__1___boxed(
    mut v_a_4700_: *mut crate::leanh::LeanObject,
    mut v_x_4701_: *mut crate::leanh::LeanObject,
    mut v___y_4702_: *mut crate::leanh::LeanObject,
    mut v___y_4703_: *mut crate::leanh::LeanObject,
    mut v___y_4704_: *mut crate::leanh::LeanObject,
    mut v___y_4705_: *mut crate::leanh::LeanObject,
    mut v___y_4706_: *mut crate::leanh::LeanObject,
    mut v___y_4707_: *mut crate::leanh::LeanObject,
    mut v___y_4708_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4709_ = l_Lean_Elab_Term_elabCalc___lam__1(
        v_a_4700_,
        v_x_4701_,
        v___y_4702_,
        v___y_4703_,
        v___y_4704_,
        v___y_4705_,
        v___y_4706_,
        v___y_4707_,
    );
    crate::leanh::lean_dec(v___y_4707_);
    crate::leanh::lean_dec_ref(v___y_4706_);
    crate::leanh::lean_dec(v___y_4705_);
    crate::leanh::lean_dec_ref(v___y_4704_);
    crate::leanh::lean_dec(v_x_4701_);
    crate::leanh::lean_dec_ref(v_a_4700_);
    return v_res_4709_;
}
pub unsafe fn l_Lean_Elab_Term_elabCalc(
    mut v_x_4714_: *mut crate::leanh::LeanObject,
    mut v_x_4715_: *mut crate::leanh::LeanObject,
    mut v_a_4716_: *mut crate::leanh::LeanObject,
    mut v_a_4717_: *mut crate::leanh::LeanObject,
    mut v_a_4718_: *mut crate::leanh::LeanObject,
    mut v_a_4719_: *mut crate::leanh::LeanObject,
    mut v_a_4720_: *mut crate::leanh::LeanObject,
    mut v_a_4721_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4724_: u8 = 0;
    let mut v___x_4725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_4727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4729_: u8 = 0;
    let mut v___x_4730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_4731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4743_: u8 = 0;
    let mut v_cancelTk_x3f_4744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4745_: u8 = 0;
    let mut v_inheritedTraceOptions_4746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk_4748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4762_: u8 = 0;
    let mut v___x_4764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4766_: u8 = 0;
    let mut v_a_4767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4770_: u8 = 0;
    let mut v___x_4772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4774_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4723_ = l_Lean_Elab_Term_elabCalc___closed__1;
                crate::leanh::lean_inc(v_x_4714_);
                v___x_4724_ = l_Lean_Syntax_isOfKind(v_x_4714_, v___x_4723_);
                if v___x_4724_ == 0 {
                    crate::leanh::lean_dec(v_x_4715_);
                    crate::leanh::lean_dec(v_x_4714_);
                    v___x_4725_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
                    return v___x_4725_;
                } else {
                    v___x_4726_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_steps_4727_ = l_Lean_Syntax_getArg(v_x_4714_, v___x_4726_);
                    v___x_4728_ = l_Lean_Elab_Term_mkCalcStepViews___closed__1;
                    crate::leanh::lean_inc(v_steps_4727_);
                    v___x_4729_ = l_Lean_Syntax_isOfKind(v_steps_4727_, v___x_4728_);
                    if v___x_4729_ == 0 {
                        crate::leanh::lean_dec(v_steps_4727_);
                        crate::leanh::lean_dec(v_x_4715_);
                        crate::leanh::lean_dec(v_x_4714_);
                        v___x_4730_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
                        return v___x_4730_;
                    } else {
                        v_fileName_4731_ = crate::leanh::lean_ctor_get(v_a_4720_, 0);
                        v_fileMap_4732_ = crate::leanh::lean_ctor_get(v_a_4720_, 1);
                        v_options_4733_ = crate::leanh::lean_ctor_get(v_a_4720_, 2);
                        v_currRecDepth_4734_ = crate::leanh::lean_ctor_get(v_a_4720_, 3);
                        v_maxRecDepth_4735_ = crate::leanh::lean_ctor_get(v_a_4720_, 4);
                        v_ref_4736_ = crate::leanh::lean_ctor_get(v_a_4720_, 5);
                        v_currNamespace_4737_ = crate::leanh::lean_ctor_get(v_a_4720_, 6);
                        v_openDecls_4738_ = crate::leanh::lean_ctor_get(v_a_4720_, 7);
                        v_initHeartbeats_4739_ = crate::leanh::lean_ctor_get(v_a_4720_, 8);
                        v_maxHeartbeats_4740_ = crate::leanh::lean_ctor_get(v_a_4720_, 9);
                        v_quotContext_4741_ = crate::leanh::lean_ctor_get(v_a_4720_, 10);
                        v_currMacroScope_4742_ = crate::leanh::lean_ctor_get(v_a_4720_, 11);
                        v_diag_4743_ = crate::leanh::lean_ctor_get_uint8(
                            v_a_4720_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                        );
                        v_cancelTk_x3f_4744_ = crate::leanh::lean_ctor_get(v_a_4720_, 12);
                        v_suppressElabErrors_4745_ = crate::leanh::lean_ctor_get_uint8(
                            v_a_4720_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                        );
                        v_inheritedTraceOptions_4746_ = crate::leanh::lean_ctor_get(v_a_4720_, 13);
                        v___x_4747_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_tk_4748_ = l_Lean_Syntax_getArg(v_x_4714_, v___x_4747_);
                        crate::leanh::lean_dec(v_x_4714_);
                        v_ref_4749_ = l_Lean_replaceRef(v_tk_4748_, v_ref_4736_);
                        crate::leanh::lean_dec(v_tk_4748_);
                        crate::leanh::lean_inc_ref(v_inheritedTraceOptions_4746_);
                        crate::leanh::lean_inc(v_cancelTk_x3f_4744_);
                        crate::leanh::lean_inc(v_currMacroScope_4742_);
                        crate::leanh::lean_inc(v_quotContext_4741_);
                        crate::leanh::lean_inc(v_maxHeartbeats_4740_);
                        crate::leanh::lean_inc(v_initHeartbeats_4739_);
                        crate::leanh::lean_inc(v_openDecls_4738_);
                        crate::leanh::lean_inc(v_currNamespace_4737_);
                        crate::leanh::lean_inc(v_maxRecDepth_4735_);
                        crate::leanh::lean_inc(v_currRecDepth_4734_);
                        crate::leanh::lean_inc_ref(v_options_4733_);
                        crate::leanh::lean_inc_ref(v_fileMap_4732_);
                        crate::leanh::lean_inc_ref(v_fileName_4731_);
                        v___x_4750_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                        crate::leanh::lean_ctor_set(v___x_4750_, 0, v_fileName_4731_);
                        crate::leanh::lean_ctor_set(v___x_4750_, 1, v_fileMap_4732_);
                        crate::leanh::lean_ctor_set(v___x_4750_, 2, v_options_4733_);
                        crate::leanh::lean_ctor_set(v___x_4750_, 3, v_currRecDepth_4734_);
                        crate::leanh::lean_ctor_set(v___x_4750_, 4, v_maxRecDepth_4735_);
                        crate::leanh::lean_ctor_set(v___x_4750_, 5, v_ref_4749_);
                        crate::leanh::lean_ctor_set(v___x_4750_, 6, v_currNamespace_4737_);
                        crate::leanh::lean_ctor_set(v___x_4750_, 7, v_openDecls_4738_);
                        crate::leanh::lean_ctor_set(v___x_4750_, 8, v_initHeartbeats_4739_);
                        crate::leanh::lean_ctor_set(v___x_4750_, 9, v_maxHeartbeats_4740_);
                        crate::leanh::lean_ctor_set(v___x_4750_, 10, v_quotContext_4741_);
                        crate::leanh::lean_ctor_set(v___x_4750_, 11, v_currMacroScope_4742_);
                        crate::leanh::lean_ctor_set(v___x_4750_, 12, v_cancelTk_x3f_4744_);
                        crate::leanh::lean_ctor_set(v___x_4750_, 13, v_inheritedTraceOptions_4746_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_4750_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                            v_diag_4743_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_4750_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                            v_suppressElabErrors_4745_,
                        );
                        v___x_4751_ = l_Lean_Elab_Term_mkCalcStepViews(
                            v_steps_4727_,
                            v_a_4716_,
                            v_a_4717_,
                            v_a_4718_,
                            v_a_4719_,
                            v___x_4750_,
                            v_a_4721_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4751_) == 0 {
                            v_a_4752_ = crate::leanh::lean_ctor_get(v___x_4751_, 0);
                            crate::leanh::lean_inc(v_a_4752_);
                            crate::leanh::lean_dec_ref_known(v___x_4751_, 1);
                            v___x_4753_ = l_Lean_Elab_Term_elabCalcSteps(
                                v_a_4752_,
                                v_a_4716_,
                                v_a_4717_,
                                v_a_4718_,
                                v_a_4719_,
                                v___x_4750_,
                                v_a_4721_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_4753_) == 0 {
                                v_a_4754_ = crate::leanh::lean_ctor_get(v___x_4753_, 0);
                                crate::leanh::lean_inc(v_a_4754_);
                                crate::leanh::lean_dec_ref_known(v___x_4753_, 1);
                                v_fst_4755_ = crate::leanh::lean_ctor_get(v_a_4754_, 0);
                                crate::leanh::lean_inc(v_fst_4755_);
                                crate::leanh::lean_dec(v_a_4754_);
                                crate::leanh::lean_inc(v_a_4752_);
                                v___f_4756_ = crate::leanh::lean_alloc_closure(
                                    l_Lean_Elab_Term_elabCalc___lam__0___boxed
                                        as *mut core::ffi::c_void,
                                    9,
                                    1,
                                );
                                crate::leanh::lean_closure_set(v___f_4756_, 0, v_a_4752_);
                                v___f_4757_ = crate::leanh::lean_alloc_closure(
                                    l_Lean_Elab_Term_elabCalc___lam__1___boxed
                                        as *mut core::ffi::c_void,
                                    9,
                                    1,
                                );
                                crate::leanh::lean_closure_set(v___f_4757_, 0, v_a_4752_);
                                v___x_4758_ = l_Lean_Elab_Term_ensureHasTypeWithErrorMsgs(
                                    v_x_4715_,
                                    v_fst_4755_,
                                    v___f_4756_,
                                    v___f_4757_,
                                    v_a_4716_,
                                    v_a_4717_,
                                    v_a_4718_,
                                    v_a_4719_,
                                    v___x_4750_,
                                    v_a_4721_,
                                );
                                crate::leanh::lean_dec_ref_known(v___x_4750_, 14);
                                return v___x_4758_;
                            } else {
                                crate::leanh::lean_dec(v_a_4752_);
                                crate::leanh::lean_dec_ref_known(v___x_4750_, 14);
                                crate::leanh::lean_dec(v_x_4715_);
                                v_a_4759_ = crate::leanh::lean_ctor_get(v___x_4753_, 0);
                                v_isSharedCheck_4766_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4753_)) as u8;
                                if v_isSharedCheck_4766_ == 0 {
                                    v___x_4761_ = v___x_4753_;
                                    v_isShared_4762_ = v_isSharedCheck_4766_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4759_);
                                    crate::leanh::lean_dec(v___x_4753_);
                                    v___x_4761_ = crate::leanh::lean_box(0);
                                    v_isShared_4762_ = v_isSharedCheck_4766_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_4750_, 14);
                            crate::leanh::lean_dec(v_x_4715_);
                            v_a_4767_ = crate::leanh::lean_ctor_get(v___x_4751_, 0);
                            v_isSharedCheck_4774_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4751_)) as u8;
                            if v_isSharedCheck_4774_ == 0 {
                                v___x_4769_ = v___x_4751_;
                                v_isShared_4770_ = v_isSharedCheck_4774_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4767_);
                                crate::leanh::lean_dec(v___x_4751_);
                                v___x_4769_ = crate::leanh::lean_box(0);
                                v_isShared_4770_ = v_isSharedCheck_4774_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4762_ == 0 {
                    v___x_4764_ = v___x_4761_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4765_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4765_, 0, v_a_4759_);
                    v___x_4764_ = v_reuseFailAlloc_4765_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4764_;
            }
            3 => {
                if v_isShared_4770_ == 0 {
                    v___x_4772_ = v___x_4769_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4773_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4773_, 0, v_a_4767_);
                    v___x_4772_ = v_reuseFailAlloc_4773_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4772_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_elabCalc___boxed(
    mut v_x_4775_: *mut crate::leanh::LeanObject,
    mut v_x_4776_: *mut crate::leanh::LeanObject,
    mut v_a_4777_: *mut crate::leanh::LeanObject,
    mut v_a_4778_: *mut crate::leanh::LeanObject,
    mut v_a_4779_: *mut crate::leanh::LeanObject,
    mut v_a_4780_: *mut crate::leanh::LeanObject,
    mut v_a_4781_: *mut crate::leanh::LeanObject,
    mut v_a_4782_: *mut crate::leanh::LeanObject,
    mut v_a_4783_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4784_ = l_Lean_Elab_Term_elabCalc(
        v_x_4775_, v_x_4776_, v_a_4777_, v_a_4778_, v_a_4779_, v_a_4780_, v_a_4781_, v_a_4782_,
    );
    crate::leanh::lean_dec(v_a_4782_);
    crate::leanh::lean_dec_ref(v_a_4781_);
    crate::leanh::lean_dec(v_a_4780_);
    crate::leanh::lean_dec_ref(v_a_4779_);
    crate::leanh::lean_dec(v_a_4778_);
    crate::leanh::lean_dec_ref(v_a_4777_);
    return v_res_4784_;
}
pub unsafe fn l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4792_ = l_Lean_Elab_Term_termElabAttribute;
    v___x_4793_ = l_Lean_Elab_Term_elabCalc___closed__1;
    v___x_4794_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1;
    v___x_4795_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Term_elabCalc___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_4796_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_4792_,
        v___x_4793_,
        v___x_4794_,
        v___x_4795_,
    );
    return v___x_4796_;
}
pub unsafe fn l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___boxed(
    mut v_a_4797_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4798_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1();
    return v_res_4798_;
}
pub unsafe fn l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_docString__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4801_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1;
    v___x_4802_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_docString__3___closed__0;
    v___x_4803_ = l_Lean_addBuiltinDocString(v___x_4801_, v___x_4802_);
    return v___x_4803_;
}
pub unsafe fn l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_docString__3___boxed(
    mut v_a_4804_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4805_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_docString__3();
    return v_res_4805_;
}
pub unsafe fn l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4832_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1;
    v___x_4833_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__6;
    v___x_4834_ = l_Lean_addBuiltinDeclarationRanges(v___x_4832_, v___x_4833_);
    return v___x_4834_;
}
pub unsafe fn l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___boxed(
    mut v_a_4835_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4836_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5();
    return v_res_4836_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Calc(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_App(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_docString__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Calc(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Calc(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_App(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Calc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Calc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Calc(builtin);
}
