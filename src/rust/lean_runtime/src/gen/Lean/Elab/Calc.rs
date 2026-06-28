// Lean compiler output
// Module: Lean.Elab.Calc
// Imports: Lean.Elab.App
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3, l_Lean_Name_mkStr4,
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
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_dec_lt};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_borrowed, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed,
    lean_string_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Meta::Basic::{lean_infer_type, lean_whnf};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_5,
    lean_apply_7, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set,
    lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox,
    lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0___closed__0_value:
    LeanStringObject<25> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0___closed__0_value
) as *mut LeanObject;
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_Elab_Term_mkCalcTrans_spec__1___closed__0_value:
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
    m_fun: l_Lean_Meta_instInhabitedMetaM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_Elab_Term_mkCalcTrans_spec__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_panic___at___00Lean_Elab_Term_mkCalcTrans_spec__1___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Term_mkCalcTrans___closed__0_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Term_mkCalcTrans___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcTrans___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Term_mkCalcTrans___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcTrans___closed__0_value) as *mut LeanObject,
        9315039795129837137 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Term_mkCalcTrans___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcTrans___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_Term_mkCalcTrans___closed__2_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Term_mkCalcTrans___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcTrans___closed__2_value) as *mut LeanObject;
static l_Lean_Elab_Term_mkCalcTrans___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcTrans___closed__0_value) as *mut LeanObject,
        9315039795129837137 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_Term_mkCalcTrans___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcTrans___closed__3_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcTrans___closed__2_value) as *mut LeanObject,
        1217078205006953987 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Term_mkCalcTrans___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcTrans___closed__3_value) as *mut LeanObject;
pub static l_Lean_Elab_Term_mkCalcTrans___closed__4_value: LeanStringObject<51> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Term_mkCalcTrans___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcTrans___closed__4_value) as *mut LeanObject;
static mut l_Lean_Elab_Term_mkCalcTrans___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Term_mkCalcTrans___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Term_mkCalcTrans___closed__6_value: LeanStringObject<59> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Term_mkCalcTrans___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcTrans___closed__6_value) as *mut LeanObject;
static mut l_Lean_Elab_Term_mkCalcTrans___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Term_mkCalcTrans___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Term_mkCalcTrans___closed__8_value: LeanStringObject<15> =
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
            76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 67, 97, 108, 99, 0,
        ],
    };
static mut l_Lean_Elab_Term_mkCalcTrans___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcTrans___closed__8_value) as *mut LeanObject;
pub static l_Lean_Elab_Term_mkCalcTrans___closed__9_value: LeanStringObject<27> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Term_mkCalcTrans___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcTrans___closed__9_value) as *mut LeanObject;
pub static l_Lean_Elab_Term_mkCalcTrans___closed__10_value: LeanStringObject<34> =
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
static mut l_Lean_Elab_Term_mkCalcTrans___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcTrans___closed__10_value) as *mut LeanObject;
static mut l_Lean_Elab_Term_mkCalcTrans___closed__11_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Term_mkCalcTrans___closed__11: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Term_mkCalcTrans___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Term_mkCalcTrans___closed__12: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__1_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__2_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__2_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__3_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 111, 108, 101, 0]};
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__3_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__4_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [116, 121, 112, 101, 65, 115, 99, 114, 105, 112, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__4_value
) as *mut LeanObject;
static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__5_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__5_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__5_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__5_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__4_value) as *mut LeanObject,5346268661279150583 as *mut LeanObject] };
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__5_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__6_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0]};
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__6_value
) as *mut LeanObject;
static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__7_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__7_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__7_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__7_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__7_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__6_value) as *mut LeanObject,7306243862518720553 as *mut LeanObject] };
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__7_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__8_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__8_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__9_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0]};
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__9:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__9_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__10_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__9_value) as *mut LeanObject,9871775667037945883 as *mut LeanObject] };
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__10_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__11_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__11_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__12_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__12: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__16_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__16: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__16_value) as *mut LeanObject;
static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__17_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__17_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__17_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__16_value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__17: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__17_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__18_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__17_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__18: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__18_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__19_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__18_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__19: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__19_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__13_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__13_value) as *mut LeanObject;
static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__14_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__14_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__14_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__13_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__14_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__14_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__2_value) as *mut LeanObject,7892421401833366012 as *mut LeanObject] };
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__14: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__14_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__15_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__14_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__15: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__15_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__20_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__15_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__19_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__20: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__20_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__21_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [58, 0]};
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__21: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__21_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__22_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__22: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__22_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__23_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__22_value) as *mut LeanObject,9855511589286918680 as *mut LeanObject] };
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__23: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__23_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__24_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__24: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__24_value) as *mut LeanObject;
pub static l_Lean_Elab_Term_instInhabitedCalcStepView_default___closed__0_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_instInhabitedCalcStepView_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_instInhabitedCalcStepView_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Elab_Term_instInhabitedCalcStepView_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_instInhabitedCalcStepView_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Elab_Term_instInhabitedCalcStepView: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_instInhabitedCalcStepView_default___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Term_mkCalcFirstStepView___closed__0_value: LeanStringObject<14> =
    LeanStringObject {
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
            99, 97, 108, 99, 70, 105, 114, 115, 116, 83, 116, 101, 112, 0,
        ],
    };
static mut l_Lean_Elab_Term_mkCalcFirstStepView___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcFirstStepView___closed__0_value) as *mut LeanObject;
static l_Lean_Elab_Term_mkCalcFirstStepView___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l_Lean_Elab_Term_mkCalcFirstStepView___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcFirstStepView___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcFirstStepView___closed__0_value)
                as *mut LeanObject,
            7592674497018613504 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_mkCalcFirstStepView___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcFirstStepView___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_Term_mkCalcFirstStepView___closed__2_value: LeanStringObject<8> =
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
        m_data: [116, 101, 114, 109, 95, 61, 95, 0],
    };
static mut l_Lean_Elab_Term_mkCalcFirstStepView___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcFirstStepView___closed__2_value) as *mut LeanObject;
pub static l_Lean_Elab_Term_mkCalcFirstStepView___closed__3_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcFirstStepView___closed__2_value)
                as *mut LeanObject,
            5677895497334651815 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_mkCalcFirstStepView___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcFirstStepView___closed__3_value) as *mut LeanObject;
pub static l_Lean_Elab_Term_mkCalcFirstStepView___closed__4_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Term_mkCalcFirstStepView___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcFirstStepView___closed__4_value) as *mut LeanObject;
static l_Lean_Elab_Term_mkCalcFirstStepView___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_Term_mkCalcFirstStepView___closed__5_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcFirstStepView___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Elab_Term_mkCalcFirstStepView___closed__5_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcFirstStepView___closed__5_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lean_Elab_Term_mkCalcFirstStepView___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcFirstStepView___closed__5_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__3_value) as *mut LeanObject,3984140175429830279 as *mut LeanObject] };
static mut l_Lean_Elab_Term_mkCalcFirstStepView___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcFirstStepView___closed__5_value) as *mut LeanObject;
pub static l_Lean_Elab_Term_mkCalcFirstStepView___closed__6_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Term_mkCalcFirstStepView___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcFirstStepView___closed__6_value) as *mut LeanObject;
pub static l_Lean_Elab_Term_mkCalcFirstStepView___closed__7_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Term_mkCalcFirstStepView___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcFirstStepView___closed__7_value) as *mut LeanObject;
static mut l_Lean_Elab_Term_mkCalcFirstStepView___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Term_mkCalcFirstStepView___closed__8: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Term_mkCalcFirstStepView___closed__9_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcFirstStepView___closed__7_value)
                as *mut LeanObject,
            17342663138809293389 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_mkCalcFirstStepView___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcFirstStepView___closed__9_value) as *mut LeanObject;
pub static l_Lean_Elab_Term_mkCalcFirstStepView___closed__10_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcFirstStepView___closed__9_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_mkCalcFirstStepView___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcFirstStepView___closed__10_value) as *mut LeanObject;
pub static l_Lean_Elab_Term_mkCalcFirstStepView___closed__11_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcFirstStepView___closed__10_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_mkCalcFirstStepView___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcFirstStepView___closed__11_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg___closed__0_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [99, 97, 108, 99, 83, 116, 101, 112, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg___closed__0_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg___closed__0_value) as *mut LeanObject,12991710356565001059 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_Term_mkCalcStepViews___closed__0_value: LeanStringObject<10> =
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
        m_data: [99, 97, 108, 99, 83, 116, 101, 112, 115, 0],
    };
static mut l_Lean_Elab_Term_mkCalcStepViews___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcStepViews___closed__0_value) as *mut LeanObject;
static l_Lean_Elab_Term_mkCalcStepViews___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l_Lean_Elab_Term_mkCalcStepViews___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcStepViews___closed__1_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcStepViews___closed__0_value) as *mut LeanObject,
        11669652153185471091 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Term_mkCalcStepViews___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_mkCalcStepViews___closed__1_value) as *mut LeanObject;
static mut l_panic___at___00Lean_Elab_Term_elabCalcSteps_spec__2___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_panic___at___00Lean_Elab_Term_elabCalcSteps_spec__2___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__1_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__1_value) as *mut LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__2_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__1_value) as *mut LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__2: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__2_value) as *mut LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___closed__0_value: LeanStringObject<25> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___closed__0_value) as *mut LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___closed__1_value) as *mut LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__0_value: LeanStringObject<39> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 39, m_capacity: 39, m_length: 38, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 39, 99, 97, 108, 99, 39, 32, 115, 116, 101, 112, 44, 32, 108, 101, 102, 116, 45, 104, 97, 110, 100, 32, 115, 105, 100, 101, 32, 105, 115, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__0_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__2_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [32, 58, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__2_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__4_value: LeanStringObject<33> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [10, 98, 117, 116, 32, 112, 114, 101, 118, 105, 111, 117, 115, 32, 114, 105, 103, 104, 116, 45, 104, 97, 110, 100, 32, 115, 105, 100, 101, 32, 105, 115, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__4_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__6_value: LeanStringObject<39> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 39, m_capacity: 39, m_length: 38, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 39, 99, 97, 108, 99, 39, 32, 115, 116, 101, 112, 44, 32, 114, 101, 108, 97, 116, 105, 111, 110, 32, 101, 120, 112, 101, 99, 116, 101, 100, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__6_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Term_elabCalcSteps___closed__0_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Term_elabCalcSteps___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_elabCalcSteps___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Term_elabCalcSteps___closed__1_value: LeanStringObject<26> =
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
            73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 79, 112, 116, 105, 111, 110, 46, 66, 97,
            115, 105, 99, 65, 117, 120, 0,
        ],
    };
static mut l_Lean_Elab_Term_elabCalcSteps___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_elabCalcSteps___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_Term_elabCalcSteps___closed__2_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Term_elabCalcSteps___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_elabCalcSteps___closed__2_value) as *mut LeanObject;
pub static l_Lean_Elab_Term_elabCalcSteps___closed__3_value: LeanStringObject<14> =
    LeanStringObject {
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
            118, 97, 108, 117, 101, 32, 105, 115, 32, 110, 111, 110, 101, 0,
        ],
    };
static mut l_Lean_Elab_Term_elabCalcSteps___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_elabCalcSteps___closed__3_value) as *mut LeanObject;
static mut l_Lean_Elab_Term_elabCalcSteps___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Term_elabCalcSteps___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__0_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__1_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__1_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__2_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__2_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__3_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__3_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__4_value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__4_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__5_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__5_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__6_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__6_value) as *mut LeanObject;
pub static l_Lean_Elab_Term_throwCalcFailure___redArg___closed__0_value: LeanStringObject<18> =
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
            39, 99, 97, 108, 99, 39, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 0,
        ],
    };
static mut l_Lean_Elab_Term_throwCalcFailure___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_throwCalcFailure___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Term_throwCalcFailure___redArg___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Term_throwCalcFailure___redArg___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_throwCalcFailure___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_throwCalcFailure___redArg___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Term_throwCalcFailure___redArg___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Term_throwCalcFailure___redArg___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Term_throwCalcFailure___redArg___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Term_throwCalcFailure___redArg___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Term_throwCalcFailure___redArg___closed__4_value: LeanStringObject<40> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 40,
        m_capacity: 40,
        m_length: 39,
        m_data: [
            105, 110, 118, 97, 108, 105, 100, 32, 39, 99, 97, 108, 99, 39, 32, 115, 116, 101, 112,
            44, 32, 114, 105, 103, 104, 116, 45, 104, 97, 110, 100, 32, 115, 105, 100, 101, 32,
            105, 115, 0,
        ],
    };
static mut l_Lean_Elab_Term_throwCalcFailure___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_throwCalcFailure___redArg___closed__4_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Term_throwCalcFailure___redArg___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Term_throwCalcFailure___redArg___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Term_throwCalcFailure___redArg___closed__6_value: LeanStringObject<23> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 23,
        m_capacity: 23,
        m_length: 22,
        m_data: [
            10, 98, 117, 116, 32, 105, 115, 32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 116,
            111, 32, 98, 101, 0,
        ],
    };
static mut l_Lean_Elab_Term_throwCalcFailure___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_throwCalcFailure___redArg___closed__6_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Term_throwCalcFailure___redArg___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Term_throwCalcFailure___redArg___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Term_throwCalcFailure___redArg___closed__8_value: LeanStringObject<32> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 32,
        m_capacity: 32,
        m_length: 31,
        m_data: [
            76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 84, 101, 114, 109, 46, 116, 104, 114, 111,
            119, 67, 97, 108, 99, 70, 97, 105, 108, 117, 114, 101, 0,
        ],
    };
static mut l_Lean_Elab_Term_throwCalcFailure___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_throwCalcFailure___redArg___closed__8_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Term_throwCalcFailure___redArg___closed__9_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Term_throwCalcFailure___redArg___closed__9: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Term_elabCalc___closed__0_value: LeanStringObject<5> = LeanStringObject {
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
static mut l_Lean_Elab_Term_elabCalc___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_elabCalc___closed__0_value) as *mut LeanObject;
static l_Lean_Elab_Term_elabCalc___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l_Lean_Elab_Term_elabCalc___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Term_elabCalc___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_elabCalc___closed__0_value) as *mut LeanObject,
        2427138008637189675 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Term_elabCalc___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_elabCalc___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__0_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [101, 108, 97, 98, 67, 97, 108, 99, 0]};
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__13_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__2_value) as *mut LeanObject,7892421401833366012 as *mut LeanObject] };
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__0_value) as *mut LeanObject,5870693989401443778 as *mut LeanObject] };
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_docString__3___closed__0_value: LeanStringObject<46> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 46, m_capacity: 46, m_length: 45, m_data: [69, 108, 97, 98, 111, 114, 97, 116, 111, 114, 32, 102, 111, 114, 32, 116, 104, 101, 32, 96, 99, 97, 108, 99, 96, 32, 116, 101, 114, 109, 32, 109, 111, 100, 101, 32, 118, 97, 114, 105, 97, 110, 116, 46, 32, 0]};
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_docString__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_docString__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 116 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 121 as usize) << 1) | 1) as *mut LeanObject,((( 15 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__0_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__1_value) as *mut LeanObject,((( 15 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 116 as usize) << 1) | 1) as *mut LeanObject,((( 4 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 116 as usize) << 1) | 1) as *mut LeanObject,((( 12 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__3_value) as *mut LeanObject,((( 4 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__4_value) as *mut LeanObject,((( 12 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__6_value) as *mut LeanObject;
pub unsafe fn l_Lean_Elab_Term_getCalcRelation_x3f___redArg(
    mut v_e_2419_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: u8 = 0;
    v___x_2421_ = l_Lean_Expr_getAppNumArgs(v_e_2419_);
    v___x_2422_ = lean_unsigned_to_nat(2);
    v___x_2423_ = lean_nat_dec_lt(v___x_2421_, v___x_2422_);
    lean_dec(v___x_2421_);
    if v___x_2423_ == 0 {
        let mut v___x_2424_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2425_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2426_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2427_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2428_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2429_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2430_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2431_: *mut LeanObject = core::ptr::null_mut();
        v___x_2424_ = l_Lean_Expr_appFn_x21(v_e_2419_);
        v___x_2425_ = l_Lean_Expr_appFn_x21(v___x_2424_);
        v___x_2426_ = l_Lean_Expr_appArg_x21(v___x_2424_);
        lean_dec_ref(v___x_2424_);
        v___x_2427_ = l_Lean_Expr_appArg_x21(v_e_2419_);
        v___x_2428_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2428_, 0, v___x_2426_);
        lean_ctor_set(v___x_2428_, 1, v___x_2427_);
        v___x_2429_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2429_, 0, v___x_2425_);
        lean_ctor_set(v___x_2429_, 1, v___x_2428_);
        v___x_2430_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_2430_, 0, v___x_2429_);
        v___x_2431_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_2431_, 0, v___x_2430_);
        return v___x_2431_;
    } else {
        let mut v___x_2432_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2433_: *mut LeanObject = core::ptr::null_mut();
        v___x_2432_ = lean_box(0);
        v___x_2433_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_2433_, 0, v___x_2432_);
        return v___x_2433_;
    }
}
pub unsafe fn l_Lean_Elab_Term_getCalcRelation_x3f___redArg___boxed(
    mut v_e_2434_: *mut LeanObject,
    mut v_a_2435_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2436_: *mut LeanObject = core::ptr::null_mut();
    v_res_2436_ = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(v_e_2434_);
    lean_dec_ref(v_e_2434_);
    return v_res_2436_;
}
pub unsafe fn l_Lean_Elab_Term_getCalcRelation_x3f(
    mut v_e_2437_: *mut LeanObject,
    mut v_a_2438_: *mut LeanObject,
    mut v_a_2439_: *mut LeanObject,
    mut v_a_2440_: *mut LeanObject,
    mut v_a_2441_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2443_: *mut LeanObject = core::ptr::null_mut();
    v___x_2443_ = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(v_e_2437_);
    return v___x_2443_;
}
pub unsafe fn l_Lean_Elab_Term_getCalcRelation_x3f___boxed(
    mut v_e_2444_: *mut LeanObject,
    mut v_a_2445_: *mut LeanObject,
    mut v_a_2446_: *mut LeanObject,
    mut v_a_2447_: *mut LeanObject,
    mut v_a_2448_: *mut LeanObject,
    mut v_a_2449_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2450_: *mut LeanObject = core::ptr::null_mut();
    v_res_2450_ =
        l_Lean_Elab_Term_getCalcRelation_x3f(v_e_2444_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_);
    lean_dec(v_a_2448_);
    lean_dec_ref(v_a_2447_);
    lean_dec(v_a_2446_);
    lean_dec_ref(v_a_2445_);
    lean_dec_ref(v_e_2444_);
    return v_res_2450_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1___redArg___lam__0(
    mut v_k_2451_: *mut LeanObject,
    mut v_b_2452_: *mut LeanObject,
    mut v_c_2453_: *mut LeanObject,
    mut v___y_2454_: *mut LeanObject,
    mut v___y_2455_: *mut LeanObject,
    mut v___y_2456_: *mut LeanObject,
    mut v___y_2457_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2459_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_2457_);
    lean_inc_ref(v___y_2456_);
    lean_inc(v___y_2455_);
    lean_inc_ref(v___y_2454_);
    v___x_2459_ = lean_apply_7(
        v_k_2451_,
        v_b_2452_,
        v_c_2453_,
        v___y_2454_,
        v___y_2455_,
        v___y_2456_,
        v___y_2457_,
        lean_box(0),
    );
    return v___x_2459_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1___redArg___lam__0___boxed(
    mut v_k_2460_: *mut LeanObject,
    mut v_b_2461_: *mut LeanObject,
    mut v_c_2462_: *mut LeanObject,
    mut v___y_2463_: *mut LeanObject,
    mut v___y_2464_: *mut LeanObject,
    mut v___y_2465_: *mut LeanObject,
    mut v___y_2466_: *mut LeanObject,
    mut v___y_2467_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2468_: *mut LeanObject = core::ptr::null_mut();
    v_res_2468_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1___redArg___lam__0(v_k_2460_, v_b_2461_, v_c_2462_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_);
    lean_dec(v___y_2466_);
    lean_dec_ref(v___y_2465_);
    lean_dec(v___y_2464_);
    lean_dec_ref(v___y_2463_);
    return v_res_2468_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1___redArg(
    mut v_type_2469_: *mut LeanObject,
    mut v_k_2470_: *mut LeanObject,
    mut v_cleanupAnnotations_2471_: u8,
    mut v_whnfType_2472_: u8,
    mut v___y_2473_: *mut LeanObject,
    mut v___y_2474_: *mut LeanObject,
    mut v___y_2475_: *mut LeanObject,
    mut v___y_2476_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2483_: u8 = 0;
    let mut v___x_2485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2487_: u8 = 0;
    let mut v_a_2488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2491_: u8 = 0;
    let mut v___x_2493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2495_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_2478_ = lean_alloc_closure(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                lean_closure_set(v___f_2478_, 0, v_k_2470_);
                v___x_2479_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(
                    lean_box(0),
                    v_type_2469_,
                    v___f_2478_,
                    v_cleanupAnnotations_2471_,
                    v_whnfType_2472_,
                    v___y_2473_,
                    v___y_2474_,
                    v___y_2475_,
                    v___y_2476_,
                );
                if lean_obj_tag(v___x_2479_) == 0 {
                    v_a_2480_ = lean_ctor_get(v___x_2479_, 0);
                    v_isSharedCheck_2487_ = (!lean_is_exclusive(v___x_2479_)) as u8;
                    if v_isSharedCheck_2487_ == 0 {
                        v___x_2482_ = v___x_2479_;
                        v_isShared_2483_ = v_isSharedCheck_2487_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2480_);
                        lean_dec(v___x_2479_);
                        v___x_2482_ = lean_box(0);
                        v_isShared_2483_ = v_isSharedCheck_2487_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2488_ = lean_ctor_get(v___x_2479_, 0);
                    v_isSharedCheck_2495_ = (!lean_is_exclusive(v___x_2479_)) as u8;
                    if v_isSharedCheck_2495_ == 0 {
                        v___x_2490_ = v___x_2479_;
                        v_isShared_2491_ = v_isSharedCheck_2495_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2488_);
                        lean_dec(v___x_2479_);
                        v___x_2490_ = lean_box(0);
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
                    v_reuseFailAlloc_2486_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2486_, 0, v_a_2480_);
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
                    v_reuseFailAlloc_2494_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2494_, 0, v_a_2488_);
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
    mut v_type_2496_: *mut LeanObject,
    mut v_k_2497_: *mut LeanObject,
    mut v_cleanupAnnotations_2498_: *mut LeanObject,
    mut v_whnfType_2499_: *mut LeanObject,
    mut v___y_2500_: *mut LeanObject,
    mut v___y_2501_: *mut LeanObject,
    mut v___y_2502_: *mut LeanObject,
    mut v___y_2503_: *mut LeanObject,
    mut v___y_2504_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_2505_: u8 = 0;
    let mut v_whnfType_boxed_2506_: u8 = 0;
    let mut v_res_2507_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_2505_ = (lean_unbox(v_cleanupAnnotations_2498_) as u8);
    v_whnfType_boxed_2506_ = (lean_unbox(v_whnfType_2499_) as u8);
    v_res_2507_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1___redArg(v_type_2496_, v_k_2497_, v_cleanupAnnotations_boxed_2505_, v_whnfType_boxed_2506_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_);
    lean_dec(v___y_2503_);
    lean_dec_ref(v___y_2502_);
    lean_dec(v___y_2501_);
    lean_dec_ref(v___y_2500_);
    return v_res_2507_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1(
    mut v_00_u03b1_2508_: *mut LeanObject,
    mut v_type_2509_: *mut LeanObject,
    mut v_k_2510_: *mut LeanObject,
    mut v_cleanupAnnotations_2511_: u8,
    mut v_whnfType_2512_: u8,
    mut v___y_2513_: *mut LeanObject,
    mut v___y_2514_: *mut LeanObject,
    mut v___y_2515_: *mut LeanObject,
    mut v___y_2516_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2518_: *mut LeanObject = core::ptr::null_mut();
    v___x_2518_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1___redArg(v_type_2509_, v_k_2510_, v_cleanupAnnotations_2511_, v_whnfType_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
    return v___x_2518_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1___boxed(
    mut v_00_u03b1_2519_: *mut LeanObject,
    mut v_type_2520_: *mut LeanObject,
    mut v_k_2521_: *mut LeanObject,
    mut v_cleanupAnnotations_2522_: *mut LeanObject,
    mut v_whnfType_2523_: *mut LeanObject,
    mut v___y_2524_: *mut LeanObject,
    mut v___y_2525_: *mut LeanObject,
    mut v___y_2526_: *mut LeanObject,
    mut v___y_2527_: *mut LeanObject,
    mut v___y_2528_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_2529_: u8 = 0;
    let mut v_whnfType_boxed_2530_: u8 = 0;
    let mut v_res_2531_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_2529_ = (lean_unbox(v_cleanupAnnotations_2522_) as u8);
    v_whnfType_boxed_2530_ = (lean_unbox(v_whnfType_2523_) as u8);
    v_res_2531_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1(v_00_u03b1_2519_, v_type_2520_, v_k_2521_, v_cleanupAnnotations_boxed_2529_, v_whnfType_boxed_2530_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_);
    lean_dec(v___y_2527_);
    lean_dec_ref(v___y_2526_);
    lean_dec(v___y_2525_);
    lean_dec_ref(v___y_2524_);
    return v_res_2531_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0_spec__0(
    mut v_msgData_2532_: *mut LeanObject,
    mut v___y_2533_: *mut LeanObject,
    mut v___y_2534_: *mut LeanObject,
    mut v___y_2535_: *mut LeanObject,
    mut v___y_2536_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_2541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_2542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut LeanObject = core::ptr::null_mut();
    v___x_2538_ = lean_st_ref_get(v___y_2536_);
    v_env_2539_ = lean_ctor_get(v___x_2538_, 0);
    lean_inc_ref(v_env_2539_);
    lean_dec(v___x_2538_);
    v___x_2540_ = lean_st_ref_get(v___y_2534_);
    v_mctx_2541_ = lean_ctor_get(v___x_2540_, 0);
    lean_inc_ref(v_mctx_2541_);
    lean_dec(v___x_2540_);
    v_lctx_2542_ = lean_ctor_get(v___y_2533_, 2);
    v_options_2543_ = lean_ctor_get(v___y_2535_, 2);
    lean_inc_ref(v_options_2543_);
    lean_inc_ref(v_lctx_2542_);
    v___x_2544_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_2544_, 0, v_env_2539_);
    lean_ctor_set(v___x_2544_, 1, v_mctx_2541_);
    lean_ctor_set(v___x_2544_, 2, v_lctx_2542_);
    lean_ctor_set(v___x_2544_, 3, v_options_2543_);
    v___x_2545_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_2545_, 0, v___x_2544_);
    lean_ctor_set(v___x_2545_, 1, v_msgData_2532_);
    v___x_2546_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2546_, 0, v___x_2545_);
    return v___x_2546_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0_spec__0___boxed(
    mut v_msgData_2547_: *mut LeanObject,
    mut v___y_2548_: *mut LeanObject,
    mut v___y_2549_: *mut LeanObject,
    mut v___y_2550_: *mut LeanObject,
    mut v___y_2551_: *mut LeanObject,
    mut v___y_2552_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2553_: *mut LeanObject = core::ptr::null_mut();
    v_res_2553_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0_spec__0(v_msgData_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_);
    lean_dec(v___y_2551_);
    lean_dec_ref(v___y_2550_);
    lean_dec(v___y_2549_);
    lean_dec_ref(v___y_2548_);
    return v_res_2553_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0___redArg(
    mut v_msg_2554_: *mut LeanObject,
    mut v___y_2555_: *mut LeanObject,
    mut v___y_2556_: *mut LeanObject,
    mut v___y_2557_: *mut LeanObject,
    mut v___y_2558_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_2560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2565_: u8 = 0;
    let mut v___x_2566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2570_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2560_ = lean_ctor_get(v___y_2557_, 5);
                v___x_2561_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0_spec__0(v_msg_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_);
                v_a_2562_ = lean_ctor_get(v___x_2561_, 0);
                v_isSharedCheck_2570_ = (!lean_is_exclusive(v___x_2561_)) as u8;
                if v_isSharedCheck_2570_ == 0 {
                    v___x_2564_ = v___x_2561_;
                    v_isShared_2565_ = v_isSharedCheck_2570_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_2562_);
                    lean_dec(v___x_2561_);
                    v___x_2564_ = lean_box(0);
                    v_isShared_2565_ = v_isSharedCheck_2570_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_2560_);
                v___x_2566_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2566_, 0, v_ref_2560_);
                lean_ctor_set(v___x_2566_, 1, v_a_2562_);
                if v_isShared_2565_ == 0 {
                    lean_ctor_set_tag(v___x_2564_, 1);
                    lean_ctor_set(v___x_2564_, 0, v___x_2566_);
                    v___x_2568_ = v___x_2564_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2569_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2569_, 0, v___x_2566_);
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
    mut v_msg_2571_: *mut LeanObject,
    mut v___y_2572_: *mut LeanObject,
    mut v___y_2573_: *mut LeanObject,
    mut v___y_2574_: *mut LeanObject,
    mut v___y_2575_: *mut LeanObject,
    mut v___y_2576_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2577_: *mut LeanObject = core::ptr::null_mut();
    v_res_2577_ = l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0___redArg(v_msg_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
    lean_dec(v___y_2575_);
    lean_dec_ref(v___y_2574_);
    lean_dec(v___y_2573_);
    lean_dec_ref(v___y_2572_);
    return v_res_2577_;
}
pub unsafe fn _init_l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_2579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut LeanObject = core::ptr::null_mut();
    v___x_2579_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0___closed__0;
    v___x_2580_ = l_Lean_stringToMessageData(v___x_2579_);
    return v___x_2580_;
}
pub unsafe fn l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0(
    mut v_a_2581_: *mut LeanObject,
    mut v_x_2582_: *mut LeanObject,
    mut v_sort_2583_: *mut LeanObject,
    mut v___y_2584_: *mut LeanObject,
    mut v___y_2585_: *mut LeanObject,
    mut v___y_2586_: *mut LeanObject,
    mut v___y_2587_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2593_: u8 = 0;
    let mut v_u_2594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2602_: u8 = 0;
    let mut v_a_2603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2606_: u8 = 0;
    let mut v___x_2608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2610_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_2587_);
                lean_inc_ref(v___y_2586_);
                lean_inc(v___y_2585_);
                lean_inc_ref(v___y_2584_);
                v___x_2589_ = lean_whnf(
                    v_sort_2583_,
                    v___y_2584_,
                    v___y_2585_,
                    v___y_2586_,
                    v___y_2587_,
                );
                if lean_obj_tag(v___x_2589_) == 0 {
                    v_a_2590_ = lean_ctor_get(v___x_2589_, 0);
                    v_isSharedCheck_2602_ = (!lean_is_exclusive(v___x_2589_)) as u8;
                    if v_isSharedCheck_2602_ == 0 {
                        v___x_2592_ = v___x_2589_;
                        v_isShared_2593_ = v_isSharedCheck_2602_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2590_);
                        lean_dec(v___x_2589_);
                        v___x_2592_ = lean_box(0);
                        v_isShared_2593_ = v_isSharedCheck_2602_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_a_2581_);
                    v_a_2603_ = lean_ctor_get(v___x_2589_, 0);
                    v_isSharedCheck_2610_ = (!lean_is_exclusive(v___x_2589_)) as u8;
                    if v_isSharedCheck_2610_ == 0 {
                        v___x_2605_ = v___x_2589_;
                        v_isShared_2606_ = v_isSharedCheck_2610_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2603_);
                        lean_dec(v___x_2589_);
                        v___x_2605_ = lean_box(0);
                        v_isShared_2606_ = v_isSharedCheck_2610_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_2590_) == 3 {
                    lean_dec_ref(v_a_2581_);
                    v_u_2594_ = lean_ctor_get(v_a_2590_, 0);
                    lean_inc(v_u_2594_);
                    lean_dec_ref_known(v_a_2590_, 1);
                    if v_isShared_2593_ == 0 {
                        lean_ctor_set(v___x_2592_, 0, v_u_2594_);
                        v___x_2596_ = v___x_2592_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2597_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2597_, 0, v_u_2594_);
                        v___x_2596_ = v_reuseFailAlloc_2597_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2592_);
                    lean_dec(v_a_2590_);
                    v___x_2598_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0___closed__1_once), _init_l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0___closed__1);
                    v___x_2599_ = l_Lean_indentExpr(v_a_2581_);
                    v___x_2600_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2600_, 0, v___x_2598_);
                    lean_ctor_set(v___x_2600_, 1, v___x_2599_);
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
                    v_reuseFailAlloc_2609_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2609_, 0, v_a_2603_);
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
    mut v_a_2611_: *mut LeanObject,
    mut v_x_2612_: *mut LeanObject,
    mut v_sort_2613_: *mut LeanObject,
    mut v___y_2614_: *mut LeanObject,
    mut v___y_2615_: *mut LeanObject,
    mut v___y_2616_: *mut LeanObject,
    mut v___y_2617_: *mut LeanObject,
    mut v___y_2618_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2619_: *mut LeanObject = core::ptr::null_mut();
    v_res_2619_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0(
        v_a_2611_,
        v_x_2612_,
        v_sort_2613_,
        v___y_2614_,
        v___y_2615_,
        v___y_2616_,
        v___y_2617_,
    );
    lean_dec(v___y_2617_);
    lean_dec_ref(v___y_2616_);
    lean_dec(v___y_2615_);
    lean_dec_ref(v___y_2614_);
    lean_dec_ref(v_x_2612_);
    return v_res_2619_;
}
pub unsafe fn l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(
    mut v_r_2620_: *mut LeanObject,
    mut v_a_2621_: *mut LeanObject,
    mut v_a_2622_: *mut LeanObject,
    mut v_a_2623_: *mut LeanObject,
    mut v_a_2624_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: u8 = 0;
    let mut v___x_2630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2634_: u8 = 0;
    let mut v___x_2636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2638_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_a_2624_);
                lean_inc_ref(v_a_2623_);
                lean_inc(v_a_2622_);
                lean_inc_ref(v_a_2621_);
                v___x_2626_ =
                    lean_infer_type(v_r_2620_, v_a_2621_, v_a_2622_, v_a_2623_, v_a_2624_);
                if lean_obj_tag(v___x_2626_) == 0 {
                    v_a_2627_ = lean_ctor_get(v___x_2626_, 0);
                    lean_inc_n(v_a_2627_, 2);
                    lean_dec_ref_known(v___x_2626_, 1);
                    v___f_2628_ = lean_alloc_closure(
                        l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0___boxed
                            as *mut core::ffi::c_void,
                        8,
                        1,
                    );
                    lean_closure_set(v___f_2628_, 0, v_a_2627_);
                    v___x_2629_ = 0;
                    v___x_2630_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__1___redArg(v_a_2627_, v___f_2628_, v___x_2629_, v___x_2629_, v_a_2621_, v_a_2622_, v_a_2623_, v_a_2624_);
                    return v___x_2630_;
                } else {
                    v_a_2631_ = lean_ctor_get(v___x_2626_, 0);
                    v_isSharedCheck_2638_ = (!lean_is_exclusive(v___x_2626_)) as u8;
                    if v_isSharedCheck_2638_ == 0 {
                        v___x_2633_ = v___x_2626_;
                        v_isShared_2634_ = v_isSharedCheck_2638_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2631_);
                        lean_dec(v___x_2626_);
                        v___x_2633_ = lean_box(0);
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
                    v_reuseFailAlloc_2637_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2637_, 0, v_a_2631_);
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
    mut v_r_2639_: *mut LeanObject,
    mut v_a_2640_: *mut LeanObject,
    mut v_a_2641_: *mut LeanObject,
    mut v_a_2642_: *mut LeanObject,
    mut v_a_2643_: *mut LeanObject,
    mut v_a_2644_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2645_: *mut LeanObject = core::ptr::null_mut();
    v_res_2645_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(
        v_r_2639_, v_a_2640_, v_a_2641_, v_a_2642_, v_a_2643_,
    );
    lean_dec(v_a_2643_);
    lean_dec_ref(v_a_2642_);
    lean_dec(v_a_2641_);
    lean_dec_ref(v_a_2640_);
    return v_res_2645_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0(
    mut v_00_u03b1_2646_: *mut LeanObject,
    mut v_msg_2647_: *mut LeanObject,
    mut v___y_2648_: *mut LeanObject,
    mut v___y_2649_: *mut LeanObject,
    mut v___y_2650_: *mut LeanObject,
    mut v___y_2651_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2653_: *mut LeanObject = core::ptr::null_mut();
    v___x_2653_ = l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0___redArg(v_msg_2647_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_);
    return v___x_2653_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0___boxed(
    mut v_00_u03b1_2654_: *mut LeanObject,
    mut v_msg_2655_: *mut LeanObject,
    mut v___y_2656_: *mut LeanObject,
    mut v___y_2657_: *mut LeanObject,
    mut v___y_2658_: *mut LeanObject,
    mut v___y_2659_: *mut LeanObject,
    mut v___y_2660_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2661_: *mut LeanObject = core::ptr::null_mut();
    v_res_2661_ =
        l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0(
            v_00_u03b1_2654_,
            v_msg_2655_,
            v___y_2656_,
            v___y_2657_,
            v___y_2658_,
            v___y_2659_,
        );
    lean_dec(v___y_2659_);
    lean_dec_ref(v___y_2658_);
    lean_dec(v___y_2657_);
    lean_dec_ref(v___y_2656_);
    return v_res_2661_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0___redArg(
    mut v_e_2662_: *mut LeanObject,
    mut v___y_2663_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2665_: u8 = 0;
    let mut v___x_2666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_2668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_2673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_2675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_2676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2679_: u8 = 0;
    let mut v___x_2681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2685_: u8 = 0;
    let mut v_unused_2686_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2665_ = l_Lean_Expr_hasMVar(v_e_2662_);
                if v___x_2665_ == 0 {
                    v___x_2666_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2666_, 0, v_e_2662_);
                    return v___x_2666_;
                } else {
                    v___x_2667_ = lean_st_ref_get(v___y_2663_);
                    v_mctx_2668_ = lean_ctor_get(v___x_2667_, 0);
                    lean_inc_ref(v_mctx_2668_);
                    lean_dec(v___x_2667_);
                    v___x_2669_ = l_Lean_instantiateMVarsCore(v_mctx_2668_, v_e_2662_);
                    v_fst_2670_ = lean_ctor_get(v___x_2669_, 0);
                    lean_inc(v_fst_2670_);
                    v_snd_2671_ = lean_ctor_get(v___x_2669_, 1);
                    lean_inc(v_snd_2671_);
                    lean_dec_ref(v___x_2669_);
                    v___x_2672_ = lean_st_ref_take(v___y_2663_);
                    v_cache_2673_ = lean_ctor_get(v___x_2672_, 1);
                    v_zetaDeltaFVarIds_2674_ = lean_ctor_get(v___x_2672_, 2);
                    v_postponed_2675_ = lean_ctor_get(v___x_2672_, 3);
                    v_diag_2676_ = lean_ctor_get(v___x_2672_, 4);
                    v_isSharedCheck_2685_ = (!lean_is_exclusive(v___x_2672_)) as u8;
                    if v_isSharedCheck_2685_ == 0 {
                        v_unused_2686_ = lean_ctor_get(v___x_2672_, 0);
                        lean_dec(v_unused_2686_);
                        v___x_2678_ = v___x_2672_;
                        v_isShared_2679_ = v_isSharedCheck_2685_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_2676_);
                        lean_inc(v_postponed_2675_);
                        lean_inc(v_zetaDeltaFVarIds_2674_);
                        lean_inc(v_cache_2673_);
                        lean_dec(v___x_2672_);
                        v___x_2678_ = lean_box(0);
                        v_isShared_2679_ = v_isSharedCheck_2685_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2679_ == 0 {
                    lean_ctor_set(v___x_2678_, 0, v_snd_2671_);
                    v___x_2681_ = v___x_2678_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2684_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2684_, 0, v_snd_2671_);
                    lean_ctor_set(v_reuseFailAlloc_2684_, 1, v_cache_2673_);
                    lean_ctor_set(v_reuseFailAlloc_2684_, 2, v_zetaDeltaFVarIds_2674_);
                    lean_ctor_set(v_reuseFailAlloc_2684_, 3, v_postponed_2675_);
                    lean_ctor_set(v_reuseFailAlloc_2684_, 4, v_diag_2676_);
                    v___x_2681_ = v_reuseFailAlloc_2684_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2682_ = lean_st_ref_set(v___y_2663_, v___x_2681_);
                v___x_2683_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2683_, 0, v_fst_2670_);
                return v___x_2683_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0___redArg___boxed(
    mut v_e_2687_: *mut LeanObject,
    mut v___y_2688_: *mut LeanObject,
    mut v___y_2689_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2690_: *mut LeanObject = core::ptr::null_mut();
    v_res_2690_ = l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0___redArg(
        v_e_2687_,
        v___y_2688_,
    );
    lean_dec(v___y_2688_);
    return v_res_2690_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0(
    mut v_e_2691_: *mut LeanObject,
    mut v___y_2692_: *mut LeanObject,
    mut v___y_2693_: *mut LeanObject,
    mut v___y_2694_: *mut LeanObject,
    mut v___y_2695_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2697_: *mut LeanObject = core::ptr::null_mut();
    v___x_2697_ = l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0___redArg(
        v_e_2691_,
        v___y_2693_,
    );
    return v___x_2697_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0___boxed(
    mut v_e_2698_: *mut LeanObject,
    mut v___y_2699_: *mut LeanObject,
    mut v___y_2700_: *mut LeanObject,
    mut v___y_2701_: *mut LeanObject,
    mut v___y_2702_: *mut LeanObject,
    mut v___y_2703_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2704_: *mut LeanObject = core::ptr::null_mut();
    v_res_2704_ = l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0(
        v_e_2698_,
        v___y_2699_,
        v___y_2700_,
        v___y_2701_,
        v___y_2702_,
    );
    lean_dec(v___y_2702_);
    lean_dec_ref(v___y_2701_);
    lean_dec(v___y_2700_);
    lean_dec_ref(v___y_2699_);
    return v_res_2704_;
}
pub unsafe fn l_panic___at___00Lean_Elab_Term_mkCalcTrans_spec__1(
    mut v_msg_2706_: *mut LeanObject,
    mut v___y_2707_: *mut LeanObject,
    mut v___y_2708_: *mut LeanObject,
    mut v___y_2709_: *mut LeanObject,
    mut v___y_2710_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7424__overap_2713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut LeanObject = core::ptr::null_mut();
    v___f_2712_ = l_panic___at___00Lean_Elab_Term_mkCalcTrans_spec__1___closed__0;
    v___x_7424__overap_2713_ = lean_panic_fn_borrowed(v___f_2712_, v_msg_2706_);
    lean_inc(v___y_2710_);
    lean_inc_ref(v___y_2709_);
    lean_inc(v___y_2708_);
    lean_inc_ref(v___y_2707_);
    v___x_2714_ = lean_apply_5(
        v___x_7424__overap_2713_,
        v___y_2707_,
        v___y_2708_,
        v___y_2709_,
        v___y_2710_,
        lean_box(0),
    );
    return v___x_2714_;
}
pub unsafe fn l_panic___at___00Lean_Elab_Term_mkCalcTrans_spec__1___boxed(
    mut v_msg_2715_: *mut LeanObject,
    mut v___y_2716_: *mut LeanObject,
    mut v___y_2717_: *mut LeanObject,
    mut v___y_2718_: *mut LeanObject,
    mut v___y_2719_: *mut LeanObject,
    mut v___y_2720_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2721_: *mut LeanObject = core::ptr::null_mut();
    v_res_2721_ = l_panic___at___00Lean_Elab_Term_mkCalcTrans_spec__1(
        v_msg_2715_,
        v___y_2716_,
        v___y_2717_,
        v___y_2718_,
        v___y_2719_,
    );
    lean_dec(v___y_2719_);
    lean_dec_ref(v___y_2718_);
    lean_dec(v___y_2717_);
    lean_dec_ref(v___y_2716_);
    return v_res_2721_;
}
pub unsafe fn _init_l_Lean_Elab_Term_mkCalcTrans___closed__5() -> *mut LeanObject {
    let mut v___x_2730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut LeanObject = core::ptr::null_mut();
    v___x_2730_ = l_Lean_Elab_Term_mkCalcTrans___closed__4;
    v___x_2731_ = l_Lean_stringToMessageData(v___x_2730_);
    return v___x_2731_;
}
pub unsafe fn _init_l_Lean_Elab_Term_mkCalcTrans___closed__7() -> *mut LeanObject {
    let mut v___x_2733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut LeanObject = core::ptr::null_mut();
    v___x_2733_ = l_Lean_Elab_Term_mkCalcTrans___closed__6;
    v___x_2734_ = l_Lean_stringToMessageData(v___x_2733_);
    return v___x_2734_;
}
pub unsafe fn _init_l_Lean_Elab_Term_mkCalcTrans___closed__11() -> *mut LeanObject {
    let mut v___x_2738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut LeanObject = core::ptr::null_mut();
    v___x_2738_ = l_Lean_Elab_Term_mkCalcTrans___closed__10;
    v___x_2739_ = lean_unsigned_to_nat(72);
    v___x_2740_ = lean_unsigned_to_nat(35);
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
pub unsafe fn _init_l_Lean_Elab_Term_mkCalcTrans___closed__12() -> *mut LeanObject {
    let mut v___x_2744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut LeanObject = core::ptr::null_mut();
    v___x_2744_ = l_Lean_Elab_Term_mkCalcTrans___closed__10;
    v___x_2745_ = lean_unsigned_to_nat(53);
    v___x_2746_ = lean_unsigned_to_nat(34);
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
    mut v_result_2750_: *mut LeanObject,
    mut v_resultType_2751_: *mut LeanObject,
    mut v_step_2752_: *mut LeanObject,
    mut v_stepType_2753_: *mut LeanObject,
    mut v_a_2754_: *mut LeanObject,
    mut v_a_2755_: *mut LeanObject,
    mut v_a_2756_: *mut LeanObject,
    mut v_a_2757_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2766_: u8 = 0;
    let mut v_fst_2767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2771_: u8 = 0;
    let mut v___x_2772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2779_: u8 = 0;
    let mut v_snd_2780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2784_: u8 = 0;
    let mut v_snd_2785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2788_: u8 = 0;
    let mut v___x_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: u8 = 0;
    let mut v___x_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2866_: u8 = 0;
    let mut v___x_2867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2884_: u8 = 0;
    let mut v___x_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2888_: u8 = 0;
    let mut v_isSharedCheck_2889_: u8 = 0;
    let mut v_a_2890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2893_: u8 = 0;
    let mut v___x_2895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2897_: u8 = 0;
    let mut v___x_2898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2907_: u8 = 0;
    let mut v___x_2909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2911_: u8 = 0;
    let mut v_reuseFailAlloc_2912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2918_: u8 = 0;
    let mut v___x_2920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2922_: u8 = 0;
    let mut v_reuseFailAlloc_2923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2927_: u8 = 0;
    let mut v___x_2929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2931_: u8 = 0;
    let mut v_a_2932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2935_: u8 = 0;
    let mut v___x_2937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2939_: u8 = 0;
    let mut v_a_2940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2943_: u8 = 0;
    let mut v___x_2945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2947_: u8 = 0;
    let mut v_a_2948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2951_: u8 = 0;
    let mut v___x_2953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2955_: u8 = 0;
    let mut v_a_2956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2959_: u8 = 0;
    let mut v___x_2961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2963_: u8 = 0;
    let mut v_a_2964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2967_: u8 = 0;
    let mut v___x_2969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2971_: u8 = 0;
    let mut v_a_2972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2975_: u8 = 0;
    let mut v___x_2977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2979_: u8 = 0;
    let mut v_a_2980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2983_: u8 = 0;
    let mut v___x_2985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2987_: u8 = 0;
    let mut v_a_2988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2991_: u8 = 0;
    let mut v___x_2993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2995_: u8 = 0;
    let mut v_a_2996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2999_: u8 = 0;
    let mut v___x_3001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3003_: u8 = 0;
    let mut v_a_3004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3007_: u8 = 0;
    let mut v___x_3009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3011_: u8 = 0;
    let mut v_isSharedCheck_3012_: u8 = 0;
    let mut v_unused_3013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3014_: u8 = 0;
    let mut v_isSharedCheck_3015_: u8 = 0;
    let mut v___x_3016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3018_: u8 = 0;
    let mut v_isSharedCheck_3019_: u8 = 0;
    let mut v___x_3020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2759_ = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(v_resultType_2751_);
                v_a_2760_ = lean_ctor_get(v___x_2759_, 0);
                lean_inc(v_a_2760_);
                lean_dec_ref(v___x_2759_);
                if lean_obj_tag(v_a_2760_) == 1 {
                    v_val_2761_ = lean_ctor_get(v_a_2760_, 0);
                    lean_inc(v_val_2761_);
                    lean_dec_ref_known(v_a_2760_, 1);
                    v_snd_2762_ = lean_ctor_get(v_val_2761_, 1);
                    v_fst_2763_ = lean_ctor_get(v_val_2761_, 0);
                    v_isSharedCheck_3019_ = (!lean_is_exclusive(v_val_2761_)) as u8;
                    if v_isSharedCheck_3019_ == 0 {
                        v___x_2765_ = v_val_2761_;
                        v_isShared_2766_ = v_isSharedCheck_3019_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_2762_);
                        lean_inc(v_fst_2763_);
                        lean_dec(v_val_2761_);
                        v___x_2765_ = lean_box(0);
                        v_isShared_2766_ = v_isSharedCheck_3019_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_a_2760_);
                    lean_dec_ref(v_stepType_2753_);
                    lean_dec_ref(v_step_2752_);
                    lean_dec_ref(v_result_2750_);
                    v___x_3020_ = lean_obj_once(
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
                v_fst_2767_ = lean_ctor_get(v_snd_2762_, 0);
                v_snd_2768_ = lean_ctor_get(v_snd_2762_, 1);
                v_isSharedCheck_3018_ = (!lean_is_exclusive(v_snd_2762_)) as u8;
                if v_isSharedCheck_3018_ == 0 {
                    v___x_2770_ = v_snd_2762_;
                    v_isShared_2771_ = v_isSharedCheck_3018_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_2768_);
                    lean_inc(v_fst_2767_);
                    lean_dec(v_snd_2762_);
                    v___x_2770_ = lean_box(0);
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
                v_a_2773_ = lean_ctor_get(v___x_2772_, 0);
                lean_inc(v_a_2773_);
                lean_dec_ref(v___x_2772_);
                v___x_2774_ = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(v_a_2773_);
                lean_dec(v_a_2773_);
                v_a_2775_ = lean_ctor_get(v___x_2774_, 0);
                lean_inc(v_a_2775_);
                lean_dec_ref(v___x_2774_);
                if lean_obj_tag(v_a_2775_) == 1 {
                    v_val_2776_ = lean_ctor_get(v_a_2775_, 0);
                    v_isSharedCheck_3015_ = (!lean_is_exclusive(v_a_2775_)) as u8;
                    if v_isSharedCheck_3015_ == 0 {
                        v___x_2778_ = v_a_2775_;
                        v_isShared_2779_ = v_isSharedCheck_3015_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_val_2776_);
                        lean_dec(v_a_2775_);
                        v___x_2778_ = lean_box(0);
                        v_isShared_2779_ = v_isSharedCheck_3015_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_2775_);
                    lean_del_object(v___x_2770_);
                    lean_dec(v_snd_2768_);
                    lean_dec(v_fst_2767_);
                    lean_del_object(v___x_2765_);
                    lean_dec(v_fst_2763_);
                    lean_dec_ref(v_step_2752_);
                    lean_dec_ref(v_result_2750_);
                    v___x_3016_ = lean_obj_once(
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
                v_snd_2780_ = lean_ctor_get(v_val_2776_, 1);
                v_fst_2781_ = lean_ctor_get(v_val_2776_, 0);
                v_isSharedCheck_3014_ = (!lean_is_exclusive(v_val_2776_)) as u8;
                if v_isSharedCheck_3014_ == 0 {
                    v___x_2783_ = v_val_2776_;
                    v_isShared_2784_ = v_isSharedCheck_3014_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_snd_2780_);
                    lean_inc(v_fst_2781_);
                    lean_dec(v_val_2776_);
                    v___x_2783_ = lean_box(0);
                    v_isShared_2784_ = v_isSharedCheck_3014_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_snd_2785_ = lean_ctor_get(v_snd_2780_, 1);
                v_isSharedCheck_3012_ = (!lean_is_exclusive(v_snd_2780_)) as u8;
                if v_isSharedCheck_3012_ == 0 {
                    v_unused_3013_ = lean_ctor_get(v_snd_2780_, 0);
                    lean_dec(v_unused_3013_);
                    v___x_2787_ = v_snd_2780_;
                    v_isShared_2788_ = v_isSharedCheck_3012_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_snd_2785_);
                    lean_dec(v_snd_2780_);
                    v___x_2787_ = lean_box(0);
                    v_isShared_2788_ = v_isSharedCheck_3012_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                lean_inc(v_fst_2763_);
                v___x_2789_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(
                    v_fst_2763_,
                    v_a_2754_,
                    v_a_2755_,
                    v_a_2756_,
                    v_a_2757_,
                );
                if lean_obj_tag(v___x_2789_) == 0 {
                    v_a_2790_ = lean_ctor_get(v___x_2789_, 0);
                    lean_inc(v_a_2790_);
                    lean_dec_ref_known(v___x_2789_, 1);
                    lean_inc(v_fst_2781_);
                    v___x_2791_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(
                        v_fst_2781_,
                        v_a_2754_,
                        v_a_2755_,
                        v_a_2756_,
                        v_a_2757_,
                    );
                    if lean_obj_tag(v___x_2791_) == 0 {
                        v_a_2792_ = lean_ctor_get(v___x_2791_, 0);
                        lean_inc(v_a_2792_);
                        lean_dec_ref_known(v___x_2791_, 1);
                        lean_inc(v_a_2757_);
                        lean_inc_ref(v_a_2756_);
                        lean_inc(v_a_2755_);
                        lean_inc_ref(v_a_2754_);
                        lean_inc(v_fst_2767_);
                        v___x_2793_ = lean_infer_type(
                            v_fst_2767_,
                            v_a_2754_,
                            v_a_2755_,
                            v_a_2756_,
                            v_a_2757_,
                        );
                        if lean_obj_tag(v___x_2793_) == 0 {
                            v_a_2794_ = lean_ctor_get(v___x_2793_, 0);
                            lean_inc(v_a_2794_);
                            lean_dec_ref_known(v___x_2793_, 1);
                            lean_inc(v_a_2757_);
                            lean_inc_ref(v_a_2756_);
                            lean_inc(v_a_2755_);
                            lean_inc_ref(v_a_2754_);
                            lean_inc(v_snd_2768_);
                            v___x_2795_ = lean_infer_type(
                                v_snd_2768_,
                                v_a_2754_,
                                v_a_2755_,
                                v_a_2756_,
                                v_a_2757_,
                            );
                            if lean_obj_tag(v___x_2795_) == 0 {
                                v_a_2796_ = lean_ctor_get(v___x_2795_, 0);
                                lean_inc(v_a_2796_);
                                lean_dec_ref_known(v___x_2795_, 1);
                                lean_inc(v_a_2757_);
                                lean_inc_ref(v_a_2756_);
                                lean_inc(v_a_2755_);
                                lean_inc_ref(v_a_2754_);
                                lean_inc(v_snd_2785_);
                                v___x_2797_ = lean_infer_type(
                                    v_snd_2785_,
                                    v_a_2754_,
                                    v_a_2755_,
                                    v_a_2756_,
                                    v_a_2757_,
                                );
                                if lean_obj_tag(v___x_2797_) == 0 {
                                    v_a_2798_ = lean_ctor_get(v___x_2797_, 0);
                                    lean_inc(v_a_2798_);
                                    lean_dec_ref_known(v___x_2797_, 1);
                                    lean_inc(v_a_2794_);
                                    v___x_2799_ = l_Lean_Meta_getLevel(
                                        v_a_2794_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_,
                                    );
                                    if lean_obj_tag(v___x_2799_) == 0 {
                                        v_a_2800_ = lean_ctor_get(v___x_2799_, 0);
                                        lean_inc(v_a_2800_);
                                        lean_dec_ref_known(v___x_2799_, 1);
                                        lean_inc(v_a_2796_);
                                        v___x_2801_ = l_Lean_Meta_getLevel(
                                            v_a_2796_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_,
                                        );
                                        if lean_obj_tag(v___x_2801_) == 0 {
                                            v_a_2802_ = lean_ctor_get(v___x_2801_, 0);
                                            lean_inc(v_a_2802_);
                                            lean_dec_ref_known(v___x_2801_, 1);
                                            lean_inc(v_a_2798_);
                                            v___x_2803_ = l_Lean_Meta_getLevel(
                                                v_a_2798_, v_a_2754_, v_a_2755_, v_a_2756_,
                                                v_a_2757_,
                                            );
                                            if lean_obj_tag(v___x_2803_) == 0 {
                                                v_a_2804_ = lean_ctor_get(v___x_2803_, 0);
                                                lean_inc(v_a_2804_);
                                                lean_dec_ref_known(v___x_2803_, 1);
                                                v___x_2805_ = l_Lean_Meta_mkFreshLevelMVar(
                                                    v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_,
                                                );
                                                if lean_obj_tag(v___x_2805_) == 0 {
                                                    v_a_2806_ = lean_ctor_get(v___x_2805_, 0);
                                                    lean_inc_n(v_a_2806_, 2);
                                                    lean_dec_ref_known(v___x_2805_, 1);
                                                    v___x_2807_ = l_Lean_mkSort(v_a_2806_);
                                                    lean_inc(v_a_2798_);
                                                    v___x_2808_ = l_Lean_mkArrow(
                                                        v_a_2798_,
                                                        v___x_2807_,
                                                        v_a_2756_,
                                                        v_a_2757_,
                                                    );
                                                    if lean_obj_tag(v___x_2808_) == 0 {
                                                        v_a_2809_ = lean_ctor_get(v___x_2808_, 0);
                                                        lean_inc(v_a_2809_);
                                                        lean_dec_ref_known(v___x_2808_, 1);
                                                        lean_inc(v_a_2794_);
                                                        v___x_2810_ = l_Lean_mkArrow(
                                                            v_a_2794_, v_a_2809_, v_a_2756_,
                                                            v_a_2757_,
                                                        );
                                                        if lean_obj_tag(v___x_2810_) == 0 {
                                                            v_a_2811_ =
                                                                lean_ctor_get(v___x_2810_, 0);
                                                            lean_inc(v_a_2811_);
                                                            lean_dec_ref_known(v___x_2810_, 1);
                                                            if v_isShared_2779_ == 0 {
                                                                lean_ctor_set(
                                                                    v___x_2778_,
                                                                    0,
                                                                    v_a_2811_,
                                                                );
                                                                v___x_2813_ = v___x_2778_;
                                                                state = 6;
                                                                continue;
                                                            } else {
                                                                v_reuseFailAlloc_2923_ =
                                                                    lean_alloc_ctor(
                                                                        1,
                                                                        1,
                                                                        (0) as u32,
                                                                    );
                                                                lean_ctor_set(
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
                                                            lean_dec(v_a_2806_);
                                                            lean_dec(v_a_2804_);
                                                            lean_dec(v_a_2802_);
                                                            lean_dec(v_a_2800_);
                                                            lean_dec(v_a_2798_);
                                                            lean_dec(v_a_2796_);
                                                            lean_dec(v_a_2794_);
                                                            lean_dec(v_a_2792_);
                                                            lean_dec(v_a_2790_);
                                                            lean_del_object(v___x_2787_);
                                                            lean_dec(v_snd_2785_);
                                                            lean_del_object(v___x_2783_);
                                                            lean_dec(v_fst_2781_);
                                                            lean_del_object(v___x_2778_);
                                                            lean_del_object(v___x_2770_);
                                                            lean_dec(v_snd_2768_);
                                                            lean_dec(v_fst_2767_);
                                                            lean_del_object(v___x_2765_);
                                                            lean_dec(v_fst_2763_);
                                                            lean_dec_ref(v_step_2752_);
                                                            lean_dec_ref(v_result_2750_);
                                                            v_a_2924_ =
                                                                lean_ctor_get(v___x_2810_, 0);
                                                            v_isSharedCheck_2931_ =
                                                                (!lean_is_exclusive(v___x_2810_))
                                                                    as u8;
                                                            if v_isSharedCheck_2931_ == 0 {
                                                                v___x_2926_ = v___x_2810_;
                                                                v_isShared_2927_ =
                                                                    v_isSharedCheck_2931_;
                                                                state = 22;
                                                                continue;
                                                            } else {
                                                                lean_inc(v_a_2924_);
                                                                lean_dec(v___x_2810_);
                                                                v___x_2926_ = lean_box(0);
                                                                v_isShared_2927_ =
                                                                    v_isSharedCheck_2931_;
                                                                state = 22;
                                                                continue;
                                                            }
                                                        }
                                                    } else {
                                                        lean_dec(v_a_2806_);
                                                        lean_dec(v_a_2804_);
                                                        lean_dec(v_a_2802_);
                                                        lean_dec(v_a_2800_);
                                                        lean_dec(v_a_2798_);
                                                        lean_dec(v_a_2796_);
                                                        lean_dec(v_a_2794_);
                                                        lean_dec(v_a_2792_);
                                                        lean_dec(v_a_2790_);
                                                        lean_del_object(v___x_2787_);
                                                        lean_dec(v_snd_2785_);
                                                        lean_del_object(v___x_2783_);
                                                        lean_dec(v_fst_2781_);
                                                        lean_del_object(v___x_2778_);
                                                        lean_del_object(v___x_2770_);
                                                        lean_dec(v_snd_2768_);
                                                        lean_dec(v_fst_2767_);
                                                        lean_del_object(v___x_2765_);
                                                        lean_dec(v_fst_2763_);
                                                        lean_dec_ref(v_step_2752_);
                                                        lean_dec_ref(v_result_2750_);
                                                        v_a_2932_ = lean_ctor_get(v___x_2808_, 0);
                                                        v_isSharedCheck_2939_ =
                                                            (!lean_is_exclusive(v___x_2808_)) as u8;
                                                        if v_isSharedCheck_2939_ == 0 {
                                                            v___x_2934_ = v___x_2808_;
                                                            v_isShared_2935_ =
                                                                v_isSharedCheck_2939_;
                                                            state = 24;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_2932_);
                                                            lean_dec(v___x_2808_);
                                                            v___x_2934_ = lean_box(0);
                                                            v_isShared_2935_ =
                                                                v_isSharedCheck_2939_;
                                                            state = 24;
                                                            continue;
                                                        }
                                                    }
                                                } else {
                                                    lean_dec(v_a_2804_);
                                                    lean_dec(v_a_2802_);
                                                    lean_dec(v_a_2800_);
                                                    lean_dec(v_a_2798_);
                                                    lean_dec(v_a_2796_);
                                                    lean_dec(v_a_2794_);
                                                    lean_dec(v_a_2792_);
                                                    lean_dec(v_a_2790_);
                                                    lean_del_object(v___x_2787_);
                                                    lean_dec(v_snd_2785_);
                                                    lean_del_object(v___x_2783_);
                                                    lean_dec(v_fst_2781_);
                                                    lean_del_object(v___x_2778_);
                                                    lean_del_object(v___x_2770_);
                                                    lean_dec(v_snd_2768_);
                                                    lean_dec(v_fst_2767_);
                                                    lean_del_object(v___x_2765_);
                                                    lean_dec(v_fst_2763_);
                                                    lean_dec_ref(v_step_2752_);
                                                    lean_dec_ref(v_result_2750_);
                                                    v_a_2940_ = lean_ctor_get(v___x_2805_, 0);
                                                    v_isSharedCheck_2947_ =
                                                        (!lean_is_exclusive(v___x_2805_)) as u8;
                                                    if v_isSharedCheck_2947_ == 0 {
                                                        v___x_2942_ = v___x_2805_;
                                                        v_isShared_2943_ = v_isSharedCheck_2947_;
                                                        state = 26;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_2940_);
                                                        lean_dec(v___x_2805_);
                                                        v___x_2942_ = lean_box(0);
                                                        v_isShared_2943_ = v_isSharedCheck_2947_;
                                                        state = 26;
                                                        continue;
                                                    }
                                                }
                                            } else {
                                                lean_dec(v_a_2802_);
                                                lean_dec(v_a_2800_);
                                                lean_dec(v_a_2798_);
                                                lean_dec(v_a_2796_);
                                                lean_dec(v_a_2794_);
                                                lean_dec(v_a_2792_);
                                                lean_dec(v_a_2790_);
                                                lean_del_object(v___x_2787_);
                                                lean_dec(v_snd_2785_);
                                                lean_del_object(v___x_2783_);
                                                lean_dec(v_fst_2781_);
                                                lean_del_object(v___x_2778_);
                                                lean_del_object(v___x_2770_);
                                                lean_dec(v_snd_2768_);
                                                lean_dec(v_fst_2767_);
                                                lean_del_object(v___x_2765_);
                                                lean_dec(v_fst_2763_);
                                                lean_dec_ref(v_step_2752_);
                                                lean_dec_ref(v_result_2750_);
                                                v_a_2948_ = lean_ctor_get(v___x_2803_, 0);
                                                v_isSharedCheck_2955_ =
                                                    (!lean_is_exclusive(v___x_2803_)) as u8;
                                                if v_isSharedCheck_2955_ == 0 {
                                                    v___x_2950_ = v___x_2803_;
                                                    v_isShared_2951_ = v_isSharedCheck_2955_;
                                                    state = 28;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_2948_);
                                                    lean_dec(v___x_2803_);
                                                    v___x_2950_ = lean_box(0);
                                                    v_isShared_2951_ = v_isSharedCheck_2955_;
                                                    state = 28;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            lean_dec(v_a_2800_);
                                            lean_dec(v_a_2798_);
                                            lean_dec(v_a_2796_);
                                            lean_dec(v_a_2794_);
                                            lean_dec(v_a_2792_);
                                            lean_dec(v_a_2790_);
                                            lean_del_object(v___x_2787_);
                                            lean_dec(v_snd_2785_);
                                            lean_del_object(v___x_2783_);
                                            lean_dec(v_fst_2781_);
                                            lean_del_object(v___x_2778_);
                                            lean_del_object(v___x_2770_);
                                            lean_dec(v_snd_2768_);
                                            lean_dec(v_fst_2767_);
                                            lean_del_object(v___x_2765_);
                                            lean_dec(v_fst_2763_);
                                            lean_dec_ref(v_step_2752_);
                                            lean_dec_ref(v_result_2750_);
                                            v_a_2956_ = lean_ctor_get(v___x_2801_, 0);
                                            v_isSharedCheck_2963_ =
                                                (!lean_is_exclusive(v___x_2801_)) as u8;
                                            if v_isSharedCheck_2963_ == 0 {
                                                v___x_2958_ = v___x_2801_;
                                                v_isShared_2959_ = v_isSharedCheck_2963_;
                                                state = 30;
                                                continue;
                                            } else {
                                                lean_inc(v_a_2956_);
                                                lean_dec(v___x_2801_);
                                                v___x_2958_ = lean_box(0);
                                                v_isShared_2959_ = v_isSharedCheck_2963_;
                                                state = 30;
                                                continue;
                                            }
                                        }
                                    } else {
                                        lean_dec(v_a_2798_);
                                        lean_dec(v_a_2796_);
                                        lean_dec(v_a_2794_);
                                        lean_dec(v_a_2792_);
                                        lean_dec(v_a_2790_);
                                        lean_del_object(v___x_2787_);
                                        lean_dec(v_snd_2785_);
                                        lean_del_object(v___x_2783_);
                                        lean_dec(v_fst_2781_);
                                        lean_del_object(v___x_2778_);
                                        lean_del_object(v___x_2770_);
                                        lean_dec(v_snd_2768_);
                                        lean_dec(v_fst_2767_);
                                        lean_del_object(v___x_2765_);
                                        lean_dec(v_fst_2763_);
                                        lean_dec_ref(v_step_2752_);
                                        lean_dec_ref(v_result_2750_);
                                        v_a_2964_ = lean_ctor_get(v___x_2799_, 0);
                                        v_isSharedCheck_2971_ =
                                            (!lean_is_exclusive(v___x_2799_)) as u8;
                                        if v_isSharedCheck_2971_ == 0 {
                                            v___x_2966_ = v___x_2799_;
                                            v_isShared_2967_ = v_isSharedCheck_2971_;
                                            state = 32;
                                            continue;
                                        } else {
                                            lean_inc(v_a_2964_);
                                            lean_dec(v___x_2799_);
                                            v___x_2966_ = lean_box(0);
                                            v_isShared_2967_ = v_isSharedCheck_2971_;
                                            state = 32;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec(v_a_2796_);
                                    lean_dec(v_a_2794_);
                                    lean_dec(v_a_2792_);
                                    lean_dec(v_a_2790_);
                                    lean_del_object(v___x_2787_);
                                    lean_dec(v_snd_2785_);
                                    lean_del_object(v___x_2783_);
                                    lean_dec(v_fst_2781_);
                                    lean_del_object(v___x_2778_);
                                    lean_del_object(v___x_2770_);
                                    lean_dec(v_snd_2768_);
                                    lean_dec(v_fst_2767_);
                                    lean_del_object(v___x_2765_);
                                    lean_dec(v_fst_2763_);
                                    lean_dec_ref(v_step_2752_);
                                    lean_dec_ref(v_result_2750_);
                                    v_a_2972_ = lean_ctor_get(v___x_2797_, 0);
                                    v_isSharedCheck_2979_ = (!lean_is_exclusive(v___x_2797_)) as u8;
                                    if v_isSharedCheck_2979_ == 0 {
                                        v___x_2974_ = v___x_2797_;
                                        v_isShared_2975_ = v_isSharedCheck_2979_;
                                        state = 34;
                                        continue;
                                    } else {
                                        lean_inc(v_a_2972_);
                                        lean_dec(v___x_2797_);
                                        v___x_2974_ = lean_box(0);
                                        v_isShared_2975_ = v_isSharedCheck_2979_;
                                        state = 34;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_a_2794_);
                                lean_dec(v_a_2792_);
                                lean_dec(v_a_2790_);
                                lean_del_object(v___x_2787_);
                                lean_dec(v_snd_2785_);
                                lean_del_object(v___x_2783_);
                                lean_dec(v_fst_2781_);
                                lean_del_object(v___x_2778_);
                                lean_del_object(v___x_2770_);
                                lean_dec(v_snd_2768_);
                                lean_dec(v_fst_2767_);
                                lean_del_object(v___x_2765_);
                                lean_dec(v_fst_2763_);
                                lean_dec_ref(v_step_2752_);
                                lean_dec_ref(v_result_2750_);
                                v_a_2980_ = lean_ctor_get(v___x_2795_, 0);
                                v_isSharedCheck_2987_ = (!lean_is_exclusive(v___x_2795_)) as u8;
                                if v_isSharedCheck_2987_ == 0 {
                                    v___x_2982_ = v___x_2795_;
                                    v_isShared_2983_ = v_isSharedCheck_2987_;
                                    state = 36;
                                    continue;
                                } else {
                                    lean_inc(v_a_2980_);
                                    lean_dec(v___x_2795_);
                                    v___x_2982_ = lean_box(0);
                                    v_isShared_2983_ = v_isSharedCheck_2987_;
                                    state = 36;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_2792_);
                            lean_dec(v_a_2790_);
                            lean_del_object(v___x_2787_);
                            lean_dec(v_snd_2785_);
                            lean_del_object(v___x_2783_);
                            lean_dec(v_fst_2781_);
                            lean_del_object(v___x_2778_);
                            lean_del_object(v___x_2770_);
                            lean_dec(v_snd_2768_);
                            lean_dec(v_fst_2767_);
                            lean_del_object(v___x_2765_);
                            lean_dec(v_fst_2763_);
                            lean_dec_ref(v_step_2752_);
                            lean_dec_ref(v_result_2750_);
                            v_a_2988_ = lean_ctor_get(v___x_2793_, 0);
                            v_isSharedCheck_2995_ = (!lean_is_exclusive(v___x_2793_)) as u8;
                            if v_isSharedCheck_2995_ == 0 {
                                v___x_2990_ = v___x_2793_;
                                v_isShared_2991_ = v_isSharedCheck_2995_;
                                state = 38;
                                continue;
                            } else {
                                lean_inc(v_a_2988_);
                                lean_dec(v___x_2793_);
                                v___x_2990_ = lean_box(0);
                                v_isShared_2991_ = v_isSharedCheck_2995_;
                                state = 38;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_2790_);
                        lean_del_object(v___x_2787_);
                        lean_dec(v_snd_2785_);
                        lean_del_object(v___x_2783_);
                        lean_dec(v_fst_2781_);
                        lean_del_object(v___x_2778_);
                        lean_del_object(v___x_2770_);
                        lean_dec(v_snd_2768_);
                        lean_dec(v_fst_2767_);
                        lean_del_object(v___x_2765_);
                        lean_dec(v_fst_2763_);
                        lean_dec_ref(v_step_2752_);
                        lean_dec_ref(v_result_2750_);
                        v_a_2996_ = lean_ctor_get(v___x_2791_, 0);
                        v_isSharedCheck_3003_ = (!lean_is_exclusive(v___x_2791_)) as u8;
                        if v_isSharedCheck_3003_ == 0 {
                            v___x_2998_ = v___x_2791_;
                            v_isShared_2999_ = v_isSharedCheck_3003_;
                            state = 40;
                            continue;
                        } else {
                            lean_inc(v_a_2996_);
                            lean_dec(v___x_2791_);
                            v___x_2998_ = lean_box(0);
                            v_isShared_2999_ = v_isSharedCheck_3003_;
                            state = 40;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_2787_);
                    lean_dec(v_snd_2785_);
                    lean_del_object(v___x_2783_);
                    lean_dec(v_fst_2781_);
                    lean_del_object(v___x_2778_);
                    lean_del_object(v___x_2770_);
                    lean_dec(v_snd_2768_);
                    lean_dec(v_fst_2767_);
                    lean_del_object(v___x_2765_);
                    lean_dec(v_fst_2763_);
                    lean_dec_ref(v_step_2752_);
                    lean_dec_ref(v_result_2750_);
                    v_a_3004_ = lean_ctor_get(v___x_2789_, 0);
                    v_isSharedCheck_3011_ = (!lean_is_exclusive(v___x_2789_)) as u8;
                    if v_isSharedCheck_3011_ == 0 {
                        v___x_3006_ = v___x_2789_;
                        v_isShared_3007_ = v_isSharedCheck_3011_;
                        state = 42;
                        continue;
                    } else {
                        lean_inc(v_a_3004_);
                        lean_dec(v___x_2789_);
                        v___x_3006_ = lean_box(0);
                        v_isShared_3007_ = v_isSharedCheck_3011_;
                        state = 42;
                        continue;
                    }
                }
            }
            6 => {
                v___x_2814_ = 0;
                v___x_2815_ = lean_box(0);
                v___x_2816_ = l_Lean_Meta_mkFreshExprMVar(
                    v___x_2813_,
                    v___x_2814_,
                    v___x_2815_,
                    v_a_2754_,
                    v_a_2755_,
                    v_a_2756_,
                    v_a_2757_,
                );
                if lean_obj_tag(v___x_2816_) == 0 {
                    v_a_2817_ = lean_ctor_get(v___x_2816_, 0);
                    lean_inc(v_a_2817_);
                    lean_dec_ref_known(v___x_2816_, 1);
                    v___x_2818_ = l_Lean_Elab_Term_mkCalcTrans___closed__1;
                    v___x_2819_ = lean_box(0);
                    if v_isShared_2784_ == 0 {
                        lean_ctor_set_tag(v___x_2783_, 1);
                        lean_ctor_set(v___x_2783_, 1, v___x_2819_);
                        lean_ctor_set(v___x_2783_, 0, v_a_2804_);
                        v___x_2821_ = v___x_2783_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_2914_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2914_, 0, v_a_2804_);
                        lean_ctor_set(v_reuseFailAlloc_2914_, 1, v___x_2819_);
                        v___x_2821_ = v_reuseFailAlloc_2914_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_dec(v_a_2806_);
                    lean_dec(v_a_2804_);
                    lean_dec(v_a_2802_);
                    lean_dec(v_a_2800_);
                    lean_dec(v_a_2798_);
                    lean_dec(v_a_2796_);
                    lean_dec(v_a_2794_);
                    lean_dec(v_a_2792_);
                    lean_dec(v_a_2790_);
                    lean_del_object(v___x_2787_);
                    lean_dec(v_snd_2785_);
                    lean_del_object(v___x_2783_);
                    lean_dec(v_fst_2781_);
                    lean_del_object(v___x_2770_);
                    lean_dec(v_snd_2768_);
                    lean_dec(v_fst_2767_);
                    lean_del_object(v___x_2765_);
                    lean_dec(v_fst_2763_);
                    lean_dec_ref(v_step_2752_);
                    lean_dec_ref(v_result_2750_);
                    v_a_2915_ = lean_ctor_get(v___x_2816_, 0);
                    v_isSharedCheck_2922_ = (!lean_is_exclusive(v___x_2816_)) as u8;
                    if v_isSharedCheck_2922_ == 0 {
                        v___x_2917_ = v___x_2816_;
                        v_isShared_2918_ = v_isSharedCheck_2922_;
                        state = 20;
                        continue;
                    } else {
                        lean_inc(v_a_2915_);
                        lean_dec(v___x_2816_);
                        v___x_2917_ = lean_box(0);
                        v_isShared_2918_ = v_isSharedCheck_2922_;
                        state = 20;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_2771_ == 0 {
                    lean_ctor_set_tag(v___x_2770_, 1);
                    lean_ctor_set(v___x_2770_, 1, v___x_2821_);
                    lean_ctor_set(v___x_2770_, 0, v_a_2802_);
                    v___x_2823_ = v___x_2770_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2913_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2913_, 0, v_a_2802_);
                    lean_ctor_set(v_reuseFailAlloc_2913_, 1, v___x_2821_);
                    v___x_2823_ = v_reuseFailAlloc_2913_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_2766_ == 0 {
                    lean_ctor_set_tag(v___x_2765_, 1);
                    lean_ctor_set(v___x_2765_, 1, v___x_2823_);
                    lean_ctor_set(v___x_2765_, 0, v_a_2800_);
                    v___x_2825_ = v___x_2765_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2912_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_a_2800_);
                    lean_ctor_set(v_reuseFailAlloc_2912_, 1, v___x_2823_);
                    v___x_2825_ = v_reuseFailAlloc_2912_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_2826_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2826_, 0, v_a_2806_);
                lean_ctor_set(v___x_2826_, 1, v___x_2825_);
                v___x_2827_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2827_, 0, v_a_2792_);
                lean_ctor_set(v___x_2827_, 1, v___x_2826_);
                v___x_2828_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2828_, 0, v_a_2790_);
                lean_ctor_set(v___x_2828_, 1, v___x_2827_);
                lean_inc_ref(v___x_2828_);
                v___x_2829_ = l_Lean_mkConst(v___x_2818_, v___x_2828_);
                v___x_2830_ = lean_unsigned_to_nat(6);
                v___x_2831_ = lean_mk_empty_array_with_capacity(v___x_2830_);
                lean_inc(v_a_2794_);
                v___x_2832_ = lean_array_push(v___x_2831_, v_a_2794_);
                lean_inc(v_a_2796_);
                v___x_2833_ = lean_array_push(v___x_2832_, v_a_2796_);
                lean_inc(v_a_2798_);
                v___x_2834_ = lean_array_push(v___x_2833_, v_a_2798_);
                lean_inc(v_fst_2763_);
                v___x_2835_ = lean_array_push(v___x_2834_, v_fst_2763_);
                lean_inc(v_fst_2781_);
                v___x_2836_ = lean_array_push(v___x_2835_, v_fst_2781_);
                lean_inc(v_a_2817_);
                v___x_2837_ = lean_array_push(v___x_2836_, v_a_2817_);
                v___x_2838_ = l_Lean_mkAppN(v___x_2829_, v___x_2837_);
                lean_dec_ref(v___x_2837_);
                v___x_2839_ = lean_box(0);
                lean_inc_ref(v___x_2838_);
                v___x_2840_ = l_Lean_Meta_trySynthInstance(
                    v___x_2838_,
                    v___x_2839_,
                    v_a_2754_,
                    v_a_2755_,
                    v_a_2756_,
                    v_a_2757_,
                );
                if lean_obj_tag(v___x_2840_) == 0 {
                    v_a_2841_ = lean_ctor_get(v___x_2840_, 0);
                    lean_inc(v_a_2841_);
                    lean_dec_ref_known(v___x_2840_, 1);
                    if lean_obj_tag(v_a_2841_) == 1 {
                        lean_dec_ref(v___x_2838_);
                        v_a_2842_ = lean_ctor_get(v_a_2841_, 0);
                        lean_inc(v_a_2842_);
                        lean_dec_ref_known(v_a_2841_, 1);
                        v___x_2843_ = l_Lean_Elab_Term_mkCalcTrans___closed__3;
                        v___x_2844_ = l_Lean_mkConst(v___x_2843_, v___x_2828_);
                        v___x_2845_ = lean_unsigned_to_nat(12);
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
                        lean_dec_ref(v___x_2858_);
                        lean_inc(v_a_2757_);
                        lean_inc_ref(v_a_2756_);
                        lean_inc(v_a_2755_);
                        lean_inc_ref(v_a_2754_);
                        lean_inc_ref(v___x_2859_);
                        v___x_2860_ = lean_infer_type(
                            v___x_2859_,
                            v_a_2754_,
                            v_a_2755_,
                            v_a_2756_,
                            v_a_2757_,
                        );
                        if lean_obj_tag(v___x_2860_) == 0 {
                            v_a_2861_ = lean_ctor_get(v___x_2860_, 0);
                            lean_inc(v_a_2861_);
                            lean_dec_ref_known(v___x_2860_, 1);
                            v___x_2862_ = l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0___redArg(v_a_2861_, v_a_2755_);
                            v_a_2863_ = lean_ctor_get(v___x_2862_, 0);
                            v_isSharedCheck_2889_ = (!lean_is_exclusive(v___x_2862_)) as u8;
                            if v_isSharedCheck_2889_ == 0 {
                                v___x_2865_ = v___x_2862_;
                                v_isShared_2866_ = v_isSharedCheck_2889_;
                                state = 10;
                                continue;
                            } else {
                                lean_inc(v_a_2863_);
                                lean_dec(v___x_2862_);
                                v___x_2865_ = lean_box(0);
                                v_isShared_2866_ = v_isSharedCheck_2889_;
                                state = 10;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v___x_2859_);
                            lean_del_object(v___x_2787_);
                            v_a_2890_ = lean_ctor_get(v___x_2860_, 0);
                            v_isSharedCheck_2897_ = (!lean_is_exclusive(v___x_2860_)) as u8;
                            if v_isSharedCheck_2897_ == 0 {
                                v___x_2892_ = v___x_2860_;
                                v_isShared_2893_ = v_isSharedCheck_2897_;
                                state = 16;
                                continue;
                            } else {
                                lean_inc(v_a_2890_);
                                lean_dec(v___x_2860_);
                                v___x_2892_ = lean_box(0);
                                v_isShared_2893_ = v_isSharedCheck_2897_;
                                state = 16;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_2841_);
                        lean_dec_ref_known(v___x_2828_, 2);
                        lean_dec(v_a_2817_);
                        lean_dec(v_a_2798_);
                        lean_dec(v_a_2796_);
                        lean_dec(v_a_2794_);
                        lean_del_object(v___x_2787_);
                        lean_dec(v_snd_2785_);
                        lean_dec(v_fst_2781_);
                        lean_dec(v_snd_2768_);
                        lean_dec(v_fst_2767_);
                        lean_dec(v_fst_2763_);
                        lean_dec_ref(v_step_2752_);
                        lean_dec_ref(v_result_2750_);
                        v___x_2898_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Elab_Term_mkCalcTrans___closed__7),
                            core::ptr::addr_of_mut!(l_Lean_Elab_Term_mkCalcTrans___closed__7_once),
                            _init_l_Lean_Elab_Term_mkCalcTrans___closed__7,
                        );
                        v___x_2899_ = l_Lean_indentExpr(v___x_2838_);
                        v___x_2900_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_2900_, 0, v___x_2898_);
                        lean_ctor_set(v___x_2900_, 1, v___x_2899_);
                        v___x_2901_ = l_Lean_useDiagnosticMsg;
                        v___x_2902_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_2902_, 0, v___x_2900_);
                        lean_ctor_set(v___x_2902_, 1, v___x_2901_);
                        v___x_2903_ = l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0___redArg(v___x_2902_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_);
                        return v___x_2903_;
                    }
                } else {
                    lean_dec_ref(v___x_2838_);
                    lean_dec_ref_known(v___x_2828_, 2);
                    lean_dec(v_a_2817_);
                    lean_dec(v_a_2798_);
                    lean_dec(v_a_2796_);
                    lean_dec(v_a_2794_);
                    lean_del_object(v___x_2787_);
                    lean_dec(v_snd_2785_);
                    lean_dec(v_fst_2781_);
                    lean_dec(v_snd_2768_);
                    lean_dec(v_fst_2767_);
                    lean_dec(v_fst_2763_);
                    lean_dec_ref(v_step_2752_);
                    lean_dec_ref(v_result_2750_);
                    v_a_2904_ = lean_ctor_get(v___x_2840_, 0);
                    v_isSharedCheck_2911_ = (!lean_is_exclusive(v___x_2840_)) as u8;
                    if v_isSharedCheck_2911_ == 0 {
                        v___x_2906_ = v___x_2840_;
                        v_isShared_2907_ = v_isSharedCheck_2911_;
                        state = 18;
                        continue;
                    } else {
                        lean_inc(v_a_2904_);
                        lean_dec(v___x_2840_);
                        v___x_2906_ = lean_box(0);
                        v_isShared_2907_ = v_isSharedCheck_2911_;
                        state = 18;
                        continue;
                    }
                }
            }
            10 => {
                v___x_2867_ = l_Lean_Expr_headBeta(v_a_2863_);
                v___x_2875_ = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(v___x_2867_);
                v_a_2876_ = lean_ctor_get(v___x_2875_, 0);
                lean_inc(v_a_2876_);
                lean_dec_ref(v___x_2875_);
                if lean_obj_tag(v_a_2876_) == 0 {
                    lean_del_object(v___x_2865_);
                    lean_dec_ref(v___x_2859_);
                    lean_del_object(v___x_2787_);
                    v___x_2877_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_Term_mkCalcTrans___closed__5),
                        core::ptr::addr_of_mut!(l_Lean_Elab_Term_mkCalcTrans___closed__5_once),
                        _init_l_Lean_Elab_Term_mkCalcTrans___closed__5,
                    );
                    v___x_2878_ = l_Lean_indentExpr(v___x_2867_);
                    v___x_2879_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2879_, 0, v___x_2877_);
                    lean_ctor_set(v___x_2879_, 1, v___x_2878_);
                    v___x_2880_ = l_Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0___redArg(v___x_2879_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_);
                    v_a_2881_ = lean_ctor_get(v___x_2880_, 0);
                    v_isSharedCheck_2888_ = (!lean_is_exclusive(v___x_2880_)) as u8;
                    if v_isSharedCheck_2888_ == 0 {
                        v___x_2883_ = v___x_2880_;
                        v_isShared_2884_ = v_isSharedCheck_2888_;
                        state = 14;
                        continue;
                    } else {
                        lean_inc(v_a_2881_);
                        lean_dec(v___x_2880_);
                        v___x_2883_ = lean_box(0);
                        v_isShared_2884_ = v_isSharedCheck_2888_;
                        state = 14;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v_a_2876_, 1);
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_2788_ == 0 {
                    lean_ctor_set(v___x_2787_, 1, v___x_2867_);
                    lean_ctor_set(v___x_2787_, 0, v___x_2859_);
                    v___x_2870_ = v___x_2787_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2874_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2874_, 0, v___x_2859_);
                    lean_ctor_set(v_reuseFailAlloc_2874_, 1, v___x_2867_);
                    v___x_2870_ = v_reuseFailAlloc_2874_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_2866_ == 0 {
                    lean_ctor_set(v___x_2865_, 0, v___x_2870_);
                    v___x_2872_ = v___x_2865_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2873_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2873_, 0, v___x_2870_);
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
                    v_reuseFailAlloc_2887_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2887_, 0, v_a_2881_);
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
                    v_reuseFailAlloc_2896_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2896_, 0, v_a_2890_);
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
                    v_reuseFailAlloc_2910_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2910_, 0, v_a_2904_);
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
                    v_reuseFailAlloc_2921_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2921_, 0, v_a_2915_);
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
                    v_reuseFailAlloc_2930_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2930_, 0, v_a_2924_);
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
                    v_reuseFailAlloc_2938_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2938_, 0, v_a_2932_);
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
                    v_reuseFailAlloc_2946_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2946_, 0, v_a_2940_);
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
                    v_reuseFailAlloc_2954_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2954_, 0, v_a_2948_);
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
                    v_reuseFailAlloc_2962_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2962_, 0, v_a_2956_);
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
                    v_reuseFailAlloc_2970_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2970_, 0, v_a_2964_);
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
                    v_reuseFailAlloc_2978_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2978_, 0, v_a_2972_);
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
                    v_reuseFailAlloc_2986_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2986_, 0, v_a_2980_);
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
                    v_reuseFailAlloc_2994_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2994_, 0, v_a_2988_);
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
                    v_reuseFailAlloc_3002_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3002_, 0, v_a_2996_);
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
                    v_reuseFailAlloc_3010_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3010_, 0, v_a_3004_);
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
    mut v_result_3022_: *mut LeanObject,
    mut v_resultType_3023_: *mut LeanObject,
    mut v_step_3024_: *mut LeanObject,
    mut v_stepType_3025_: *mut LeanObject,
    mut v_a_3026_: *mut LeanObject,
    mut v_a_3027_: *mut LeanObject,
    mut v_a_3028_: *mut LeanObject,
    mut v_a_3029_: *mut LeanObject,
    mut v_a_3030_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3031_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_3029_);
    lean_dec_ref(v_a_3028_);
    lean_dec(v_a_3027_);
    lean_dec_ref(v_a_3026_);
    lean_dec_ref(v_resultType_3023_);
    return v_res_3031_;
}
pub unsafe fn _init_l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__12()
-> *mut LeanObject {
    let mut v___x_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut LeanObject = core::ptr::null_mut();
    v___x_3053_ =
        l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__11;
    v___x_3054_ = l_String_toRawSubstring_x27(v___x_3053_);
    return v___x_3054_;
}
pub unsafe fn l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go(
    mut v_type_3079_: *mut LeanObject,
    mut v_t_3080_: *mut LeanObject,
    mut v_a_3081_: u8,
    mut v_a_3082_: *mut LeanObject,
    mut v_a_3083_: *mut LeanObject,
    mut v_a_3084_: *mut LeanObject,
    mut v_a_3085_: *mut LeanObject,
    mut v_a_3086_: *mut LeanObject,
    mut v_a_3087_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_info_3092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_3093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_3094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3097_: u8 = 0;
    let mut v___y_3098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3104_: usize = 0;
    let mut v___x_3105_: usize = 0;
    let mut v___x_3106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3110_: u8 = 0;
    let mut v_fst_3111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3115_: u8 = 0;
    let mut v___x_3116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3123_: u8 = 0;
    let mut v_isSharedCheck_3124_: u8 = 0;
    let mut v_a_3125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3128_: u8 = 0;
    let mut v___x_3130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3132_: u8 = 0;
    let mut v_pre_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_3134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_3135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_3136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_3137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_3138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_3139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_3140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: u8 = 0;
    let mut v___x_3143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: u8 = 0;
    let mut v___x_3145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: u8 = 0;
    let mut v___x_3151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: u8 = 0;
    let mut v___x_3157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3165_: u8 = 0;
    let mut v_ref_3166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: u8 = 0;
    let mut v___x_3170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3194_: u8 = 0;
    let mut v_a_3195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3198_: u8 = 0;
    let mut v___x_3200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3202_: u8 = 0;
    let mut v___x_3203_: u8 = 0;
    let mut v___x_3204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_a_3081_ == 0 {
                    lean_dec_ref(v_type_3079_);
                    v___x_3089_ = lean_box((v_a_3081_) as usize);
                    v___x_3090_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3090_, 0, v_t_3080_);
                    lean_ctor_set(v___x_3090_, 1, v___x_3089_);
                    v___x_3091_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3091_, 0, v___x_3090_);
                    return v___x_3091_;
                } else {
                    if lean_obj_tag(v_t_3080_) == 1 {
                        v_info_3092_ = lean_ctor_get(v_t_3080_, 0);
                        v_kind_3093_ = lean_ctor_get(v_t_3080_, 1);
                        v_args_3094_ = lean_ctor_get(v_t_3080_, 2);
                        if lean_obj_tag(v_kind_3093_) == 1 {
                            v_pre_3133_ = lean_ctor_get(v_kind_3093_, 0);
                            if lean_obj_tag(v_pre_3133_) == 1 {
                                v_pre_3134_ = lean_ctor_get(v_pre_3133_, 0);
                                if lean_obj_tag(v_pre_3134_) == 1 {
                                    v_pre_3135_ = lean_ctor_get(v_pre_3134_, 0);
                                    if lean_obj_tag(v_pre_3135_) == 1 {
                                        v_pre_3136_ = lean_ctor_get(v_pre_3135_, 0);
                                        if lean_obj_tag(v_pre_3136_) == 0 {
                                            v_str_3137_ = lean_ctor_get(v_kind_3093_, 1);
                                            v_str_3138_ = lean_ctor_get(v_pre_3133_, 1);
                                            v_str_3139_ = lean_ctor_get(v_pre_3134_, 1);
                                            v_str_3140_ = lean_ctor_get(v_pre_3135_, 1);
                                            v___x_3141_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__0;
                                            v___x_3142_ =
                                                lean_string_dec_eq(v_str_3140_, v___x_3141_);
                                            if v___x_3142_ == 0 {
                                                lean_inc_ref(v_kind_3093_);
                                                lean_inc_ref(v_args_3094_);
                                                lean_inc(v_info_3092_);
                                                lean_dec_ref_known(v_t_3080_, 3);
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
                                                    lean_inc_ref(v_str_3139_);
                                                    lean_inc_ref(v_str_3138_);
                                                    lean_inc(v_pre_3136_);
                                                    lean_inc_ref(v_str_3137_);
                                                    lean_inc_ref(v_args_3094_);
                                                    lean_inc(v_info_3092_);
                                                    lean_dec_ref_known(v_t_3080_, 3);
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
                                                        lean_inc_ref(v_str_3138_);
                                                        lean_inc(v_pre_3136_);
                                                        lean_inc_ref(v_str_3137_);
                                                        lean_inc_ref(v_args_3094_);
                                                        lean_inc(v_info_3092_);
                                                        lean_dec_ref_known(v_t_3080_, 3);
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
                                                            lean_inc_ref(v_str_3137_);
                                                            lean_inc(v_pre_3136_);
                                                            lean_inc_ref(v_args_3094_);
                                                            lean_inc(v_info_3092_);
                                                            lean_dec_ref_known(v_t_3080_, 3);
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
                                                            if lean_obj_tag(v___x_3161_) == 0 {
                                                                v_a_3162_ =
                                                                    lean_ctor_get(v___x_3161_, 0);
                                                                v_isSharedCheck_3194_ =
                                                                    (!lean_is_exclusive(
                                                                        v___x_3161_,
                                                                    ))
                                                                        as u8;
                                                                if v_isSharedCheck_3194_ == 0 {
                                                                    v___x_3164_ = v___x_3161_;
                                                                    v_isShared_3165_ =
                                                                        v_isSharedCheck_3194_;
                                                                    state = 8;
                                                                    continue;
                                                                } else {
                                                                    lean_inc(v_a_3162_);
                                                                    lean_dec(v___x_3161_);
                                                                    v___x_3164_ = lean_box(0);
                                                                    v_isShared_3165_ =
                                                                        v_isSharedCheck_3194_;
                                                                    state = 8;
                                                                    continue;
                                                                }
                                                            } else {
                                                                lean_dec_ref_known(v_t_3080_, 3);
                                                                v_a_3195_ =
                                                                    lean_ctor_get(v___x_3161_, 0);
                                                                v_isSharedCheck_3202_ =
                                                                    (!lean_is_exclusive(
                                                                        v___x_3161_,
                                                                    ))
                                                                        as u8;
                                                                if v_isSharedCheck_3202_ == 0 {
                                                                    v___x_3197_ = v___x_3161_;
                                                                    v_isShared_3198_ =
                                                                        v_isSharedCheck_3202_;
                                                                    state = 10;
                                                                    continue;
                                                                } else {
                                                                    lean_inc(v_a_3195_);
                                                                    lean_dec(v___x_3161_);
                                                                    v___x_3197_ = lean_box(0);
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
                                            lean_inc_ref(v_kind_3093_);
                                            lean_inc_ref(v_args_3094_);
                                            lean_inc(v_info_3092_);
                                            lean_dec_ref_known(v_t_3080_, 3);
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
                                        lean_inc_ref(v_kind_3093_);
                                        lean_inc_ref(v_args_3094_);
                                        lean_inc(v_info_3092_);
                                        lean_dec_ref_known(v_t_3080_, 3);
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
                                    lean_inc_ref(v_kind_3093_);
                                    lean_inc_ref(v_args_3094_);
                                    lean_inc(v_info_3092_);
                                    lean_dec_ref_known(v_t_3080_, 3);
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
                                lean_inc_ref(v_kind_3093_);
                                lean_inc_ref(v_args_3094_);
                                lean_inc(v_info_3092_);
                                lean_dec_ref_known(v_t_3080_, 3);
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
                            lean_inc_ref(v_args_3094_);
                            lean_inc(v_kind_3093_);
                            lean_inc(v_info_3092_);
                            lean_dec_ref_known(v_t_3080_, 3);
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
                        lean_dec_ref(v_type_3079_);
                        v___x_3203_ = 0;
                        v___x_3204_ = lean_box((v___x_3203_) as usize);
                        v___x_3205_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_3205_, 0, v_t_3080_);
                        lean_ctor_set(v___x_3205_, 1, v___x_3204_);
                        v___x_3206_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_3206_, 0, v___x_3205_);
                        return v___x_3206_;
                    }
                }
            }
            1 => {
                v_sz_3104_ = lean_array_size(v_args_3094_);
                v___x_3105_ = 0usize;
                v___x_3106_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go_spec__0(v_type_3079_, v_sz_3104_, v___x_3105_, v_args_3094_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_);
                if lean_obj_tag(v___x_3106_) == 0 {
                    v_a_3107_ = lean_ctor_get(v___x_3106_, 0);
                    v_isSharedCheck_3124_ = (!lean_is_exclusive(v___x_3106_)) as u8;
                    if v_isSharedCheck_3124_ == 0 {
                        v___x_3109_ = v___x_3106_;
                        v_isShared_3110_ = v_isSharedCheck_3124_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3107_);
                        lean_dec(v___x_3106_);
                        v___x_3109_ = lean_box(0);
                        v_isShared_3110_ = v_isSharedCheck_3124_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_k_3096_);
                    lean_dec(v_info_3092_);
                    v_a_3125_ = lean_ctor_get(v___x_3106_, 0);
                    v_isSharedCheck_3132_ = (!lean_is_exclusive(v___x_3106_)) as u8;
                    if v_isSharedCheck_3132_ == 0 {
                        v___x_3127_ = v___x_3106_;
                        v_isShared_3128_ = v_isSharedCheck_3132_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_3125_);
                        lean_dec(v___x_3106_);
                        v___x_3127_ = lean_box(0);
                        v_isShared_3128_ = v_isSharedCheck_3132_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_3111_ = lean_ctor_get(v_a_3107_, 0);
                v_snd_3112_ = lean_ctor_get(v_a_3107_, 1);
                v_isSharedCheck_3123_ = (!lean_is_exclusive(v_a_3107_)) as u8;
                if v_isSharedCheck_3123_ == 0 {
                    v___x_3114_ = v_a_3107_;
                    v_isShared_3115_ = v_isSharedCheck_3123_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_snd_3112_);
                    lean_inc(v_fst_3111_);
                    lean_dec(v_a_3107_);
                    v___x_3114_ = lean_box(0);
                    v_isShared_3115_ = v_isSharedCheck_3123_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3116_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_3116_, 0, v_info_3092_);
                lean_ctor_set(v___x_3116_, 1, v_k_3096_);
                lean_ctor_set(v___x_3116_, 2, v_fst_3111_);
                if v_isShared_3115_ == 0 {
                    lean_ctor_set(v___x_3114_, 0, v___x_3116_);
                    v___x_3118_ = v___x_3114_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3122_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3122_, 0, v___x_3116_);
                    lean_ctor_set(v_reuseFailAlloc_3122_, 1, v_snd_3112_);
                    v___x_3118_ = v_reuseFailAlloc_3122_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3110_ == 0 {
                    lean_ctor_set(v___x_3109_, 0, v___x_3118_);
                    v___x_3120_ = v___x_3109_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3121_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3121_, 0, v___x_3118_);
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
                    v_reuseFailAlloc_3131_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3131_, 0, v_a_3125_);
                    v___x_3130_ = v_reuseFailAlloc_3131_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3130_;
            }
            8 => {
                v_ref_3166_ = lean_ctor_get(v_a_3086_, 5);
                v_quotContext_3167_ = lean_ctor_get(v_a_3086_, 10);
                v_currMacroScope_3168_ = lean_ctor_get(v_a_3086_, 11);
                v___x_3169_ = 0;
                v___x_3170_ = l_Lean_SourceInfo_fromRef(v_ref_3166_, v___x_3169_);
                v___x_3171_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__5;
                v___x_3172_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__7;
                v___x_3173_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__8;
                lean_inc_n(v___x_3170_, 7);
                v___x_3174_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3174_, 0, v___x_3170_);
                lean_ctor_set(v___x_3174_, 1, v___x_3173_);
                v___x_3175_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__10;
                v___x_3176_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__12), core::ptr::addr_of_mut!(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__12_once), _init_l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__12);
                lean_inc(v_currMacroScope_3168_);
                lean_inc(v_quotContext_3167_);
                v___x_3177_ =
                    l_Lean_addMacroScope(v_quotContext_3167_, v_pre_3136_, v_currMacroScope_3168_);
                v___x_3178_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__20;
                v___x_3179_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_3179_, 0, v___x_3170_);
                lean_ctor_set(v___x_3179_, 1, v___x_3176_);
                lean_ctor_set(v___x_3179_, 2, v___x_3177_);
                lean_ctor_set(v___x_3179_, 3, v___x_3178_);
                v___x_3180_ = l_Lean_Syntax_node1(v___x_3170_, v___x_3175_, v___x_3179_);
                v___x_3181_ =
                    l_Lean_Syntax_node2(v___x_3170_, v___x_3172_, v___x_3174_, v___x_3180_);
                v___x_3182_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__21;
                v___x_3183_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3183_, 0, v___x_3170_);
                lean_ctor_set(v___x_3183_, 1, v___x_3182_);
                v___x_3184_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__23;
                v___x_3185_ = l_Lean_Syntax_node1(v___x_3170_, v___x_3184_, v_a_3162_);
                v___x_3186_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__24;
                v___x_3187_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3187_, 0, v___x_3170_);
                lean_ctor_set(v___x_3187_, 1, v___x_3186_);
                v___x_3188_ = l_Lean_Syntax_node5(
                    v___x_3170_,
                    v___x_3171_,
                    v___x_3181_,
                    v_t_3080_,
                    v___x_3183_,
                    v___x_3185_,
                    v___x_3187_,
                );
                v___x_3189_ = lean_box((v___x_3169_) as usize);
                v___x_3190_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3190_, 0, v___x_3188_);
                lean_ctor_set(v___x_3190_, 1, v___x_3189_);
                if v_isShared_3165_ == 0 {
                    lean_ctor_set(v___x_3164_, 0, v___x_3190_);
                    v___x_3192_ = v___x_3164_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3193_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3193_, 0, v___x_3190_);
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
                    v_reuseFailAlloc_3201_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3201_, 0, v_a_3195_);
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
    mut v_type_3207_: *mut LeanObject,
    mut v_sz_3208_: usize,
    mut v_i_3209_: usize,
    mut v_bs_3210_: *mut LeanObject,
    mut v___y_3211_: u8,
    mut v___y_3212_: *mut LeanObject,
    mut v___y_3213_: *mut LeanObject,
    mut v___y_3214_: *mut LeanObject,
    mut v___y_3215_: *mut LeanObject,
    mut v___y_3216_: *mut LeanObject,
    mut v___y_3217_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3219_: u8 = 0;
    let mut v___x_3220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: usize = 0;
    let mut v___x_3231_: usize = 0;
    let mut v___x_3232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: u8 = 0;
    let mut v_a_3235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3238_: u8 = 0;
    let mut v___x_3240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3242_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3219_ = lean_usize_dec_lt(v_i_3209_, v_sz_3208_);
                if v___x_3219_ == 0 {
                    lean_dec_ref(v_type_3207_);
                    v___x_3220_ = lean_box((v___y_3211_) as usize);
                    v___x_3221_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3221_, 0, v_bs_3210_);
                    lean_ctor_set(v___x_3221_, 1, v___x_3220_);
                    v___x_3222_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3222_, 0, v___x_3221_);
                    return v___x_3222_;
                } else {
                    v_v_3223_ = lean_array_uget_borrowed(v_bs_3210_, v_i_3209_);
                    lean_inc(v_v_3223_);
                    lean_inc_ref(v_type_3207_);
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
                    if lean_obj_tag(v___x_3224_) == 0 {
                        v_a_3225_ = lean_ctor_get(v___x_3224_, 0);
                        lean_inc(v_a_3225_);
                        lean_dec_ref_known(v___x_3224_, 1);
                        v_fst_3226_ = lean_ctor_get(v_a_3225_, 0);
                        lean_inc(v_fst_3226_);
                        v_snd_3227_ = lean_ctor_get(v_a_3225_, 1);
                        lean_inc(v_snd_3227_);
                        lean_dec(v_a_3225_);
                        v___x_3228_ = lean_unsigned_to_nat(0);
                        v_bs_x27_3229_ = lean_array_uset(v_bs_3210_, v_i_3209_, v___x_3228_);
                        v___x_3230_ = 1usize;
                        v___x_3231_ = lean_usize_add(v_i_3209_, v___x_3230_);
                        v___x_3232_ = lean_array_uset(v_bs_x27_3229_, v_i_3209_, v_fst_3226_);
                        v___x_3233_ = (lean_unbox(v_snd_3227_) as u8);
                        lean_dec(v_snd_3227_);
                        v_i_3209_ = v___x_3231_;
                        v_bs_3210_ = v___x_3232_;
                        v___y_3211_ = v___x_3233_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_3210_);
                        lean_dec_ref(v_type_3207_);
                        v_a_3235_ = lean_ctor_get(v___x_3224_, 0);
                        v_isSharedCheck_3242_ = (!lean_is_exclusive(v___x_3224_)) as u8;
                        if v_isSharedCheck_3242_ == 0 {
                            v___x_3237_ = v___x_3224_;
                            v_isShared_3238_ = v_isSharedCheck_3242_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3235_);
                            lean_dec(v___x_3224_);
                            v___x_3237_ = lean_box(0);
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
                    v_reuseFailAlloc_3241_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3241_, 0, v_a_3235_);
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
    mut v_type_3243_: *mut LeanObject,
    mut v_sz_3244_: *mut LeanObject,
    mut v_i_3245_: *mut LeanObject,
    mut v_bs_3246_: *mut LeanObject,
    mut v___y_3247_: *mut LeanObject,
    mut v___y_3248_: *mut LeanObject,
    mut v___y_3249_: *mut LeanObject,
    mut v___y_3250_: *mut LeanObject,
    mut v___y_3251_: *mut LeanObject,
    mut v___y_3252_: *mut LeanObject,
    mut v___y_3253_: *mut LeanObject,
    mut v___y_3254_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3255_: usize = 0;
    let mut v_i_boxed_3256_: usize = 0;
    let mut v___y_7883__boxed_3257_: u8 = 0;
    let mut v_res_3258_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3255_ = lean_unbox_usize(v_sz_3244_);
    lean_dec(v_sz_3244_);
    v_i_boxed_3256_ = lean_unbox_usize(v_i_3245_);
    lean_dec(v_i_3245_);
    v___y_7883__boxed_3257_ = (lean_unbox(v___y_3247_) as u8);
    v_res_3258_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go_spec__0(v_type_3243_, v_sz_boxed_3255_, v_i_boxed_3256_, v_bs_3246_, v___y_7883__boxed_3257_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_);
    lean_dec(v___y_3253_);
    lean_dec_ref(v___y_3252_);
    lean_dec(v___y_3251_);
    lean_dec_ref(v___y_3250_);
    lean_dec(v___y_3249_);
    lean_dec_ref(v___y_3248_);
    return v_res_3258_;
}
pub unsafe fn l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___boxed(
    mut v_type_3259_: *mut LeanObject,
    mut v_t_3260_: *mut LeanObject,
    mut v_a_3261_: *mut LeanObject,
    mut v_a_3262_: *mut LeanObject,
    mut v_a_3263_: *mut LeanObject,
    mut v_a_3264_: *mut LeanObject,
    mut v_a_3265_: *mut LeanObject,
    mut v_a_3266_: *mut LeanObject,
    mut v_a_3267_: *mut LeanObject,
    mut v_a_3268_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_7952__boxed_3269_: u8 = 0;
    let mut v_res_3270_: *mut LeanObject = core::ptr::null_mut();
    v_a_7952__boxed_3269_ = (lean_unbox(v_a_3261_) as u8);
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
    lean_dec(v_a_3267_);
    lean_dec_ref(v_a_3266_);
    lean_dec(v_a_3265_);
    lean_dec_ref(v_a_3264_);
    lean_dec(v_a_3263_);
    lean_dec_ref(v_a_3262_);
    return v_res_3270_;
}
pub unsafe fn l_Lean_Elab_Term_annotateFirstHoleWithType(
    mut v_t_3271_: *mut LeanObject,
    mut v_type_3272_: *mut LeanObject,
    mut v_a_3273_: *mut LeanObject,
    mut v_a_3274_: *mut LeanObject,
    mut v_a_3275_: *mut LeanObject,
    mut v_a_3276_: *mut LeanObject,
    mut v_a_3277_: *mut LeanObject,
    mut v_a_3278_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3280_: u8 = 0;
    let mut v___x_3281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3285_: u8 = 0;
    let mut v_fst_3286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3290_: u8 = 0;
    let mut v_a_3291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3294_: u8 = 0;
    let mut v___x_3296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3297_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_3281_) == 0 {
                    v_a_3282_ = lean_ctor_get(v___x_3281_, 0);
                    v_isSharedCheck_3290_ = (!lean_is_exclusive(v___x_3281_)) as u8;
                    if v_isSharedCheck_3290_ == 0 {
                        v___x_3284_ = v___x_3281_;
                        v_isShared_3285_ = v_isSharedCheck_3290_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3282_);
                        lean_dec(v___x_3281_);
                        v___x_3284_ = lean_box(0);
                        v_isShared_3285_ = v_isSharedCheck_3290_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3291_ = lean_ctor_get(v___x_3281_, 0);
                    v_isSharedCheck_3298_ = (!lean_is_exclusive(v___x_3281_)) as u8;
                    if v_isSharedCheck_3298_ == 0 {
                        v___x_3293_ = v___x_3281_;
                        v_isShared_3294_ = v_isSharedCheck_3298_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3291_);
                        lean_dec(v___x_3281_);
                        v___x_3293_ = lean_box(0);
                        v_isShared_3294_ = v_isSharedCheck_3298_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3286_ = lean_ctor_get(v_a_3282_, 0);
                lean_inc(v_fst_3286_);
                lean_dec(v_a_3282_);
                if v_isShared_3285_ == 0 {
                    lean_ctor_set(v___x_3284_, 0, v_fst_3286_);
                    v___x_3288_ = v___x_3284_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3289_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3289_, 0, v_fst_3286_);
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
                    v_reuseFailAlloc_3297_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3297_, 0, v_a_3291_);
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
    mut v_t_3299_: *mut LeanObject,
    mut v_type_3300_: *mut LeanObject,
    mut v_a_3301_: *mut LeanObject,
    mut v_a_3302_: *mut LeanObject,
    mut v_a_3303_: *mut LeanObject,
    mut v_a_3304_: *mut LeanObject,
    mut v_a_3305_: *mut LeanObject,
    mut v_a_3306_: *mut LeanObject,
    mut v_a_3307_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3308_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_3306_);
    lean_dec_ref(v_a_3305_);
    lean_dec(v_a_3304_);
    lean_dec_ref(v_a_3303_);
    lean_dec(v_a_3302_);
    lean_dec_ref(v_a_3301_);
    return v_res_3308_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_3313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: *mut LeanObject = core::ptr::null_mut();
    v___x_3313_ = lean_box(0);
    v___x_3314_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_3315_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_3315_, 0, v___x_3314_);
    lean_ctor_set(v___x_3315_, 1, v___x_3313_);
    return v___x_3315_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg()
-> *mut LeanObject {
    let mut v___x_3317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: *mut LeanObject = core::ptr::null_mut();
    v___x_3317_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg___closed__0);
    v___x_3318_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_3318_, 0, v___x_3317_);
    return v___x_3318_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg___boxed(
    mut v___y_3319_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3320_: *mut LeanObject = core::ptr::null_mut();
    v_res_3320_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
    return v_res_3320_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0(
    mut v_00_u03b1_3321_: *mut LeanObject,
    mut v___y_3322_: *mut LeanObject,
    mut v___y_3323_: *mut LeanObject,
    mut v___y_3324_: *mut LeanObject,
    mut v___y_3325_: *mut LeanObject,
    mut v___y_3326_: *mut LeanObject,
    mut v___y_3327_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3329_: *mut LeanObject = core::ptr::null_mut();
    v___x_3329_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
    return v___x_3329_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___boxed(
    mut v_00_u03b1_3330_: *mut LeanObject,
    mut v___y_3331_: *mut LeanObject,
    mut v___y_3332_: *mut LeanObject,
    mut v___y_3333_: *mut LeanObject,
    mut v___y_3334_: *mut LeanObject,
    mut v___y_3335_: *mut LeanObject,
    mut v___y_3336_: *mut LeanObject,
    mut v___y_3337_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3338_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_3336_);
    lean_dec_ref(v___y_3335_);
    lean_dec(v___y_3334_);
    lean_dec_ref(v___y_3333_);
    lean_dec(v___y_3332_);
    lean_dec_ref(v___y_3331_);
    return v_res_3338_;
}
pub unsafe fn _init_l_Lean_Elab_Term_mkCalcFirstStepView___closed__8() -> *mut LeanObject {
    let mut v___x_3354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: *mut LeanObject = core::ptr::null_mut();
    v___x_3354_ = l_Lean_Elab_Term_mkCalcFirstStepView___closed__7;
    v___x_3355_ = l_String_toRawSubstring_x27(v___x_3354_);
    return v___x_3355_;
}
pub unsafe fn l_Lean_Elab_Term_mkCalcFirstStepView(
    mut v_step0_3364_: *mut LeanObject,
    mut v_a_3365_: *mut LeanObject,
    mut v_a_3366_: *mut LeanObject,
    mut v_a_3367_: *mut LeanObject,
    mut v_a_3368_: *mut LeanObject,
    mut v_a_3369_: *mut LeanObject,
    mut v_a_3370_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_3372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: u8 = 0;
    v_ref_3372_ = lean_ctor_get(v_a_3369_, 5);
    v_quotContext_3373_ = lean_ctor_get(v_a_3369_, 10);
    v_currMacroScope_3374_ = lean_ctor_get(v_a_3369_, 11);
    v___x_3375_ = l_Lean_Elab_Term_mkCalcFirstStepView___closed__1;
    lean_inc(v_step0_3364_);
    v___x_3376_ = l_Lean_Syntax_isOfKind(v_step0_3364_, v___x_3375_);
    if v___x_3376_ == 0 {
        let mut v___x_3377_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_step0_3364_);
        v___x_3377_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
        return v___x_3377_;
    } else {
        let mut v___x_3378_: *mut LeanObject = core::ptr::null_mut();
        let mut v_term_3379_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3380_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3381_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3382_: u8 = 0;
        v___x_3378_ = lean_unsigned_to_nat(0);
        v_term_3379_ = l_Lean_Syntax_getArg(v_step0_3364_, v___x_3378_);
        v___x_3380_ = lean_unsigned_to_nat(1);
        v___x_3381_ = l_Lean_Syntax_getArg(v_step0_3364_, v___x_3380_);
        lean_inc(v___x_3381_);
        v___x_3382_ = l_Lean_Syntax_matchesNull(v___x_3381_, v___x_3378_);
        if v___x_3382_ == 0 {
            let mut v___x_3383_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3384_: u8 = 0;
            v___x_3383_ = lean_unsigned_to_nat(2);
            lean_inc(v___x_3381_);
            v___x_3384_ = l_Lean_Syntax_matchesNull(v___x_3381_, v___x_3383_);
            if v___x_3384_ == 0 {
                let mut v___x_3385_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___x_3381_);
                lean_dec(v_term_3379_);
                lean_dec(v_step0_3364_);
                v___x_3385_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
                return v___x_3385_;
            } else {
                let mut v_proof_3386_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3387_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3388_: *mut LeanObject = core::ptr::null_mut();
                v_proof_3386_ = l_Lean_Syntax_getArg(v___x_3381_, v___x_3380_);
                lean_dec(v___x_3381_);
                v___x_3387_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_3387_, 0, v_step0_3364_);
                lean_ctor_set(v___x_3387_, 1, v_term_3379_);
                lean_ctor_set(v___x_3387_, 2, v_proof_3386_);
                v___x_3388_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3388_, 0, v___x_3387_);
                return v___x_3388_;
            }
        } else {
            let mut v_ref_3389_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3390_: u8 = 0;
            let mut v___x_3391_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3392_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3393_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3394_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3395_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3396_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3397_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3398_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3399_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3400_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3401_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3402_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3403_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3404_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3405_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3406_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_3381_);
            v_ref_3389_ = l_Lean_replaceRef(v_step0_3364_, v_ref_3372_);
            v___x_3390_ = 0;
            v___x_3391_ = l_Lean_SourceInfo_fromRef(v_ref_3389_, v___x_3390_);
            lean_dec(v_ref_3389_);
            v___x_3392_ = l_Lean_Elab_Term_mkCalcFirstStepView___closed__3;
            v___x_3393_ = l_Lean_Elab_Term_mkCalcFirstStepView___closed__4;
            lean_inc_n(v___x_3391_, 4);
            v___x_3394_ = lean_alloc_ctor(2, 2, (0) as u32);
            lean_ctor_set(v___x_3394_, 0, v___x_3391_);
            lean_ctor_set(v___x_3394_, 1, v___x_3393_);
            v___x_3395_ = l_Lean_Elab_Term_mkCalcFirstStepView___closed__5;
            v___x_3396_ = l_Lean_Elab_Term_mkCalcFirstStepView___closed__6;
            v___x_3397_ = lean_alloc_ctor(2, 2, (0) as u32);
            lean_ctor_set(v___x_3397_, 0, v___x_3391_);
            lean_ctor_set(v___x_3397_, 1, v___x_3396_);
            v___x_3398_ = l_Lean_Syntax_node1(v___x_3391_, v___x_3395_, v___x_3397_);
            v___x_3399_ = l_Lean_Syntax_node3(
                v___x_3391_,
                v___x_3392_,
                v_term_3379_,
                v___x_3394_,
                v___x_3398_,
            );
            v___x_3400_ = lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Elab_Term_mkCalcFirstStepView___closed__8),
                core::ptr::addr_of_mut!(l_Lean_Elab_Term_mkCalcFirstStepView___closed__8_once),
                _init_l_Lean_Elab_Term_mkCalcFirstStepView___closed__8,
            );
            v___x_3401_ = l_Lean_Elab_Term_mkCalcFirstStepView___closed__9;
            lean_inc(v_currMacroScope_3374_);
            lean_inc(v_quotContext_3373_);
            v___x_3402_ =
                l_Lean_addMacroScope(v_quotContext_3373_, v___x_3401_, v_currMacroScope_3374_);
            v___x_3403_ = l_Lean_Elab_Term_mkCalcFirstStepView___closed__11;
            v___x_3404_ = lean_alloc_ctor(3, 4, (0) as u32);
            lean_ctor_set(v___x_3404_, 0, v___x_3391_);
            lean_ctor_set(v___x_3404_, 1, v___x_3400_);
            lean_ctor_set(v___x_3404_, 2, v___x_3402_);
            lean_ctor_set(v___x_3404_, 3, v___x_3403_);
            v___x_3405_ = lean_alloc_ctor(0, 3, (0) as u32);
            lean_ctor_set(v___x_3405_, 0, v_step0_3364_);
            lean_ctor_set(v___x_3405_, 1, v___x_3399_);
            lean_ctor_set(v___x_3405_, 2, v___x_3404_);
            v___x_3406_ = lean_alloc_ctor(0, 1, (0) as u32);
            lean_ctor_set(v___x_3406_, 0, v___x_3405_);
            return v___x_3406_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_mkCalcFirstStepView___boxed(
    mut v_step0_3407_: *mut LeanObject,
    mut v_a_3408_: *mut LeanObject,
    mut v_a_3409_: *mut LeanObject,
    mut v_a_3410_: *mut LeanObject,
    mut v_a_3411_: *mut LeanObject,
    mut v_a_3412_: *mut LeanObject,
    mut v_a_3413_: *mut LeanObject,
    mut v_a_3414_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3415_: *mut LeanObject = core::ptr::null_mut();
    v_res_3415_ = l_Lean_Elab_Term_mkCalcFirstStepView(
        v_step0_3407_,
        v_a_3408_,
        v_a_3409_,
        v_a_3410_,
        v_a_3411_,
        v_a_3412_,
        v_a_3413_,
    );
    lean_dec(v_a_3413_);
    lean_dec_ref(v_a_3412_);
    lean_dec(v_a_3411_);
    lean_dec_ref(v_a_3410_);
    lean_dec(v_a_3409_);
    lean_dec_ref(v_a_3408_);
    return v_res_3415_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg(
    mut v_as_3420_: *mut LeanObject,
    mut v_sz_3421_: usize,
    mut v_i_3422_: usize,
    mut v_b_3423_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: usize = 0;
    let mut v___x_3428_: usize = 0;
    let mut v___x_3430_: u8 = 0;
    let mut v___x_3431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: u8 = 0;
    let mut v___x_3435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3439_: u8 = 0;
    let mut v___x_3441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3443_: u8 = 0;
    let mut v___x_3444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3430_ = lean_usize_dec_lt(v_i_3422_, v_sz_3421_);
                if v___x_3430_ == 0 {
                    v___x_3431_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3431_, 0, v_b_3423_);
                    return v___x_3431_;
                } else {
                    v___x_3432_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg___closed__1;
                    v_a_3433_ = lean_array_uget_borrowed(v_as_3420_, v_i_3422_);
                    lean_inc(v_a_3433_);
                    v___x_3434_ = l_Lean_Syntax_isOfKind(v_a_3433_, v___x_3432_);
                    if v___x_3434_ == 0 {
                        v___x_3435_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
                        if lean_obj_tag(v___x_3435_) == 0 {
                            lean_dec_ref_known(v___x_3435_, 1);
                            v_a_3426_ = v_b_3423_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec_ref(v_b_3423_);
                            v_a_3436_ = lean_ctor_get(v___x_3435_, 0);
                            v_isSharedCheck_3443_ = (!lean_is_exclusive(v___x_3435_)) as u8;
                            if v_isSharedCheck_3443_ == 0 {
                                v___x_3438_ = v___x_3435_;
                                v_isShared_3439_ = v_isSharedCheck_3443_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_a_3436_);
                                lean_dec(v___x_3435_);
                                v___x_3438_ = lean_box(0);
                                v_isShared_3439_ = v_isSharedCheck_3443_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        v___x_3444_ = lean_unsigned_to_nat(0);
                        v___x_3445_ = l_Lean_Syntax_getArg(v_a_3433_, v___x_3444_);
                        v___x_3446_ = lean_unsigned_to_nat(2);
                        v___x_3447_ = l_Lean_Syntax_getArg(v_a_3433_, v___x_3446_);
                        lean_inc(v_a_3433_);
                        v___x_3448_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v___x_3448_, 0, v_a_3433_);
                        lean_ctor_set(v___x_3448_, 1, v___x_3445_);
                        lean_ctor_set(v___x_3448_, 2, v___x_3447_);
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
                    v_reuseFailAlloc_3442_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3442_, 0, v_a_3436_);
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
    mut v_as_3450_: *mut LeanObject,
    mut v_sz_3451_: *mut LeanObject,
    mut v_i_3452_: *mut LeanObject,
    mut v_b_3453_: *mut LeanObject,
    mut v___y_3454_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3455_: usize = 0;
    let mut v_i_boxed_3456_: usize = 0;
    let mut v_res_3457_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3455_ = lean_unbox_usize(v_sz_3451_);
    lean_dec(v_sz_3451_);
    v_i_boxed_3456_ = lean_unbox_usize(v_i_3452_);
    lean_dec(v_i_3452_);
    v_res_3457_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg(v_as_3450_, v_sz_boxed_3455_, v_i_boxed_3456_, v_b_3453_);
    lean_dec_ref(v_as_3450_);
    return v_res_3457_;
}
pub unsafe fn l_Lean_Elab_Term_mkCalcStepViews(
    mut v_steps_3462_: *mut LeanObject,
    mut v_a_3463_: *mut LeanObject,
    mut v_a_3464_: *mut LeanObject,
    mut v_a_3465_: *mut LeanObject,
    mut v_a_3466_: *mut LeanObject,
    mut v_a_3467_: *mut LeanObject,
    mut v_a_3468_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: u8 = 0;
    let mut v___x_3472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_step0_3474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: u8 = 0;
    let mut v___x_3477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rest_3482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3485_: usize = 0;
    let mut v___x_3486_: usize = 0;
    let mut v___x_3487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3491_: u8 = 0;
    let mut v___x_3493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3495_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3470_ = l_Lean_Elab_Term_mkCalcStepViews___closed__1;
                lean_inc(v_steps_3462_);
                v___x_3471_ = l_Lean_Syntax_isOfKind(v_steps_3462_, v___x_3470_);
                if v___x_3471_ == 0 {
                    lean_dec(v_steps_3462_);
                    v___x_3472_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
                    return v___x_3472_;
                } else {
                    v___x_3473_ = lean_unsigned_to_nat(0);
                    v_step0_3474_ = l_Lean_Syntax_getArg(v_steps_3462_, v___x_3473_);
                    v___x_3475_ = l_Lean_Elab_Term_mkCalcFirstStepView___closed__1;
                    lean_inc(v_step0_3474_);
                    v___x_3476_ = l_Lean_Syntax_isOfKind(v_step0_3474_, v___x_3475_);
                    if v___x_3476_ == 0 {
                        lean_dec(v_step0_3474_);
                        lean_dec(v_steps_3462_);
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
                        if lean_obj_tag(v___x_3478_) == 0 {
                            v_a_3479_ = lean_ctor_get(v___x_3478_, 0);
                            lean_inc(v_a_3479_);
                            lean_dec_ref_known(v___x_3478_, 1);
                            v___x_3480_ = lean_unsigned_to_nat(1);
                            v___x_3481_ = l_Lean_Syntax_getArg(v_steps_3462_, v___x_3480_);
                            lean_dec(v_steps_3462_);
                            v_rest_3482_ = l_Lean_Syntax_getArgs(v___x_3481_);
                            lean_dec(v___x_3481_);
                            v___x_3483_ = lean_mk_empty_array_with_capacity(v___x_3480_);
                            v___x_3484_ = lean_array_push(v___x_3483_, v_a_3479_);
                            v_sz_3485_ = lean_array_size(v_rest_3482_);
                            v___x_3486_ = 0usize;
                            v___x_3487_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg(v_rest_3482_, v_sz_3485_, v___x_3486_, v___x_3484_);
                            lean_dec_ref(v_rest_3482_);
                            return v___x_3487_;
                        } else {
                            lean_dec(v_steps_3462_);
                            v_a_3488_ = lean_ctor_get(v___x_3478_, 0);
                            v_isSharedCheck_3495_ = (!lean_is_exclusive(v___x_3478_)) as u8;
                            if v_isSharedCheck_3495_ == 0 {
                                v___x_3490_ = v___x_3478_;
                                v_isShared_3491_ = v_isSharedCheck_3495_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_3488_);
                                lean_dec(v___x_3478_);
                                v___x_3490_ = lean_box(0);
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
                    v_reuseFailAlloc_3494_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3494_, 0, v_a_3488_);
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
    mut v_steps_3496_: *mut LeanObject,
    mut v_a_3497_: *mut LeanObject,
    mut v_a_3498_: *mut LeanObject,
    mut v_a_3499_: *mut LeanObject,
    mut v_a_3500_: *mut LeanObject,
    mut v_a_3501_: *mut LeanObject,
    mut v_a_3502_: *mut LeanObject,
    mut v_a_3503_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3504_: *mut LeanObject = core::ptr::null_mut();
    v_res_3504_ = l_Lean_Elab_Term_mkCalcStepViews(
        v_steps_3496_,
        v_a_3497_,
        v_a_3498_,
        v_a_3499_,
        v_a_3500_,
        v_a_3501_,
        v_a_3502_,
    );
    lean_dec(v_a_3502_);
    lean_dec_ref(v_a_3501_);
    lean_dec(v_a_3500_);
    lean_dec_ref(v_a_3499_);
    lean_dec(v_a_3498_);
    lean_dec_ref(v_a_3497_);
    return v_res_3504_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0(
    mut v_as_3505_: *mut LeanObject,
    mut v_sz_3506_: usize,
    mut v_i_3507_: usize,
    mut v_b_3508_: *mut LeanObject,
    mut v___y_3509_: *mut LeanObject,
    mut v___y_3510_: *mut LeanObject,
    mut v___y_3511_: *mut LeanObject,
    mut v___y_3512_: *mut LeanObject,
    mut v___y_3513_: *mut LeanObject,
    mut v___y_3514_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3516_: *mut LeanObject = core::ptr::null_mut();
    v___x_3516_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___redArg(v_as_3505_, v_sz_3506_, v_i_3507_, v_b_3508_);
    return v___x_3516_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0___boxed(
    mut v_as_3517_: *mut LeanObject,
    mut v_sz_3518_: *mut LeanObject,
    mut v_i_3519_: *mut LeanObject,
    mut v_b_3520_: *mut LeanObject,
    mut v___y_3521_: *mut LeanObject,
    mut v___y_3522_: *mut LeanObject,
    mut v___y_3523_: *mut LeanObject,
    mut v___y_3524_: *mut LeanObject,
    mut v___y_3525_: *mut LeanObject,
    mut v___y_3526_: *mut LeanObject,
    mut v___y_3527_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3528_: usize = 0;
    let mut v_i_boxed_3529_: usize = 0;
    let mut v_res_3530_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3528_ = lean_unbox_usize(v_sz_3518_);
    lean_dec(v_sz_3518_);
    v_i_boxed_3529_ = lean_unbox_usize(v_i_3519_);
    lean_dec(v_i_3519_);
    v_res_3530_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_mkCalcStepViews_spec__0(v_as_3517_, v_sz_boxed_3528_, v_i_boxed_3529_, v_b_3520_, v___y_3521_, v___y_3522_, v___y_3523_, v___y_3524_, v___y_3525_, v___y_3526_);
    lean_dec(v___y_3526_);
    lean_dec_ref(v___y_3525_);
    lean_dec(v___y_3524_);
    lean_dec_ref(v___y_3523_);
    lean_dec(v___y_3522_);
    lean_dec_ref(v___y_3521_);
    lean_dec_ref(v_as_3517_);
    return v_res_3530_;
}
pub unsafe fn _init_l_panic___at___00Lean_Elab_Term_elabCalcSteps_spec__2___closed__0()
-> *mut LeanObject {
    let mut v___x_3531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut LeanObject = core::ptr::null_mut();
    v___x_3531_ = l_Lean_instInhabitedExpr;
    v___x_3532_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3532_, 0, v___x_3531_);
    lean_ctor_set(v___x_3532_, 1, v___x_3531_);
    return v___x_3532_;
}
pub unsafe fn l_panic___at___00Lean_Elab_Term_elabCalcSteps_spec__2(
    mut v_msg_3533_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut LeanObject = core::ptr::null_mut();
    v___x_3534_ = lean_obj_once(
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
    mut v_opts_3536_: *mut LeanObject,
    mut v_opt_3537_: *mut LeanObject,
) -> u8 {
    let mut v_name_3538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_3539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut LeanObject = core::ptr::null_mut();
    v_name_3538_ = lean_ctor_get(v_opt_3537_, 0);
    v_defValue_3539_ = lean_ctor_get(v_opt_3537_, 1);
    v_map_3540_ = lean_ctor_get(v_opts_3536_, 0);
    v___x_3541_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3540_,
            v_name_3538_,
        );
    if lean_obj_tag(v___x_3541_) == 0 {
        let mut v___x_3542_: u8 = 0;
        v___x_3542_ = (lean_unbox(v_defValue_3539_) as u8);
        return v___x_3542_;
    } else {
        let mut v_val_3543_: *mut LeanObject = core::ptr::null_mut();
        v_val_3543_ = lean_ctor_get(v___x_3541_, 0);
        lean_inc(v_val_3543_);
        lean_dec_ref_known(v___x_3541_, 1);
        if lean_obj_tag(v_val_3543_) == 1 {
            let mut v_v_3544_: u8 = 0;
            v_v_3544_ = lean_ctor_get_uint8(v_val_3543_, 0 as u32);
            lean_dec_ref_known(v_val_3543_, 0);
            return v_v_3544_;
        } else {
            let mut v___x_3545_: u8 = 0;
            lean_dec(v_val_3543_);
            v___x_3545_ = (lean_unbox(v_defValue_3539_) as u8);
            return v___x_3545_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__4___boxed(
    mut v_opts_3546_: *mut LeanObject,
    mut v_opt_3547_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3548_: u8 = 0;
    let mut v_r_3549_: *mut LeanObject = core::ptr::null_mut();
    v_res_3548_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__4(v_opts_3546_, v_opt_3547_);
    lean_dec_ref(v_opt_3547_);
    lean_dec_ref(v_opts_3546_);
    v_r_3549_ = lean_box((v_res_3548_) as usize);
    return v_r_3549_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__0()
-> *mut LeanObject {
    let mut v___x_3550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: *mut LeanObject = core::ptr::null_mut();
    v___x_3550_ = lean_box(1);
    v___x_3551_ = l_Lean_MessageData_ofFormat(v___x_3550_);
    return v___x_3551_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__3()
-> *mut LeanObject {
    let mut v___x_3555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: *mut LeanObject = core::ptr::null_mut();
    v___x_3555_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__2;
    v___x_3556_ = l_Lean_MessageData_ofFormat(v___x_3555_);
    return v___x_3556_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5(
    mut v_x_3557_: *mut LeanObject,
    mut v_x_3558_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_3559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3563_: u8 = 0;
    let mut v_before_3564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3567_: u8 = 0;
    let mut v___x_3568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3580_: u8 = 0;
    let mut v_unused_3581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3582_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3558_) == 0 {
                    return v_x_3557_;
                } else {
                    v_head_3559_ = lean_ctor_get(v_x_3558_, 0);
                    v_tail_3560_ = lean_ctor_get(v_x_3558_, 1);
                    v_isSharedCheck_3582_ = (!lean_is_exclusive(v_x_3558_)) as u8;
                    if v_isSharedCheck_3582_ == 0 {
                        v___x_3562_ = v_x_3558_;
                        v_isShared_3563_ = v_isSharedCheck_3582_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3560_);
                        lean_inc(v_head_3559_);
                        lean_dec(v_x_3558_);
                        v___x_3562_ = lean_box(0);
                        v_isShared_3563_ = v_isSharedCheck_3582_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_3564_ = lean_ctor_get(v_head_3559_, 0);
                v_isSharedCheck_3580_ = (!lean_is_exclusive(v_head_3559_)) as u8;
                if v_isSharedCheck_3580_ == 0 {
                    v_unused_3581_ = lean_ctor_get(v_head_3559_, 1);
                    lean_dec(v_unused_3581_);
                    v___x_3566_ = v_head_3559_;
                    v_isShared_3567_ = v_isSharedCheck_3580_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_before_3564_);
                    lean_dec(v_head_3559_);
                    v___x_3566_ = lean_box(0);
                    v_isShared_3567_ = v_isSharedCheck_3580_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3568_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__0);
                if v_isShared_3567_ == 0 {
                    lean_ctor_set_tag(v___x_3566_, 7);
                    lean_ctor_set(v___x_3566_, 1, v___x_3568_);
                    lean_ctor_set(v___x_3566_, 0, v_x_3557_);
                    v___x_3570_ = v___x_3566_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3579_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3579_, 0, v_x_3557_);
                    lean_ctor_set(v_reuseFailAlloc_3579_, 1, v___x_3568_);
                    v___x_3570_ = v_reuseFailAlloc_3579_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3571_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__3);
                if v_isShared_3563_ == 0 {
                    lean_ctor_set_tag(v___x_3562_, 7);
                    lean_ctor_set(v___x_3562_, 1, v___x_3571_);
                    lean_ctor_set(v___x_3562_, 0, v___x_3570_);
                    v___x_3573_ = v___x_3562_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3578_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3578_, 0, v___x_3570_);
                    lean_ctor_set(v_reuseFailAlloc_3578_, 1, v___x_3571_);
                    v___x_3573_ = v_reuseFailAlloc_3578_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3574_ = l_Lean_MessageData_ofSyntax(v_before_3564_);
                v___x_3575_ = l_Lean_indentD(v___x_3574_);
                v___x_3576_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3576_, 0, v___x_3573_);
                lean_ctor_set(v___x_3576_, 1, v___x_3575_);
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
-> *mut LeanObject {
    let mut v___x_3586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3587_: *mut LeanObject = core::ptr::null_mut();
    v___x_3586_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___closed__1;
    v___x_3587_ = l_Lean_MessageData_ofFormat(v___x_3586_);
    return v___x_3587_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg(
    mut v_msgData_3588_: *mut LeanObject,
    mut v_macroStack_3589_: *mut LeanObject,
    mut v___y_3590_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_options_3592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: u8 = 0;
    let mut v___x_3595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_after_3598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3601_: u8 = 0;
    let mut v___x_3602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msgData_3609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3613_: u8 = 0;
    let mut v_unused_3614_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_3592_ = lean_ctor_get(v___y_3590_, 2);
                v___x_3593_ = l_Lean_Elab_pp_macroStack;
                v___x_3594_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__4(v_options_3592_, v___x_3593_);
                if v___x_3594_ == 0 {
                    lean_dec(v_macroStack_3589_);
                    v___x_3595_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3595_, 0, v_msgData_3588_);
                    return v___x_3595_;
                } else {
                    if lean_obj_tag(v_macroStack_3589_) == 0 {
                        v___x_3596_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_3596_, 0, v_msgData_3588_);
                        return v___x_3596_;
                    } else {
                        v_head_3597_ = lean_ctor_get(v_macroStack_3589_, 0);
                        lean_inc(v_head_3597_);
                        v_after_3598_ = lean_ctor_get(v_head_3597_, 1);
                        v_isSharedCheck_3613_ = (!lean_is_exclusive(v_head_3597_)) as u8;
                        if v_isSharedCheck_3613_ == 0 {
                            v_unused_3614_ = lean_ctor_get(v_head_3597_, 0);
                            lean_dec(v_unused_3614_);
                            v___x_3600_ = v_head_3597_;
                            v_isShared_3601_ = v_isSharedCheck_3613_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_after_3598_);
                            lean_dec(v_head_3597_);
                            v___x_3600_ = lean_box(0);
                            v_isShared_3601_ = v_isSharedCheck_3613_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3602_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5___closed__0);
                if v_isShared_3601_ == 0 {
                    lean_ctor_set_tag(v___x_3600_, 7);
                    lean_ctor_set(v___x_3600_, 1, v___x_3602_);
                    lean_ctor_set(v___x_3600_, 0, v_msgData_3588_);
                    v___x_3604_ = v___x_3600_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3612_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3612_, 0, v_msgData_3588_);
                    lean_ctor_set(v_reuseFailAlloc_3612_, 1, v___x_3602_);
                    v___x_3604_ = v_reuseFailAlloc_3612_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3605_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___closed__2);
                v___x_3606_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3606_, 0, v___x_3604_);
                lean_ctor_set(v___x_3606_, 1, v___x_3605_);
                v___x_3607_ = l_Lean_MessageData_ofSyntax(v_after_3598_);
                v___x_3608_ = l_Lean_indentD(v___x_3607_);
                v_msgData_3609_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v_msgData_3609_, 0, v___x_3606_);
                lean_ctor_set(v_msgData_3609_, 1, v___x_3608_);
                v___x_3610_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2_spec__5(v_msgData_3609_, v_macroStack_3589_);
                v___x_3611_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3611_, 0, v___x_3610_);
                return v___x_3611_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_msgData_3615_: *mut LeanObject,
    mut v_macroStack_3616_: *mut LeanObject,
    mut v___y_3617_: *mut LeanObject,
    mut v___y_3618_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3619_: *mut LeanObject = core::ptr::null_mut();
    v_res_3619_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg(v_msgData_3615_, v_macroStack_3616_, v___y_3617_);
    lean_dec_ref(v___y_3617_);
    return v_res_3619_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0___redArg(
    mut v_msg_3620_: *mut LeanObject,
    mut v___y_3621_: *mut LeanObject,
    mut v___y_3622_: *mut LeanObject,
    mut v___y_3623_: *mut LeanObject,
    mut v___y_3624_: *mut LeanObject,
    mut v___y_3625_: *mut LeanObject,
    mut v___y_3626_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_3628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_macroStack_3631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3637_: u8 = 0;
    let mut v___x_3638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3642_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3628_ = lean_ctor_get(v___y_3625_, 5);
                v___x_3629_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0_spec__0(v_msg_3620_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_);
                v_a_3630_ = lean_ctor_get(v___x_3629_, 0);
                lean_inc(v_a_3630_);
                lean_dec_ref(v___x_3629_);
                v_macroStack_3631_ = lean_ctor_get(v___y_3621_, 1);
                v___x_3632_ = l_Lean_Elab_getBetterRef(v_ref_3628_, v_macroStack_3631_);
                lean_inc(v_macroStack_3631_);
                v___x_3633_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg(v_a_3630_, v_macroStack_3631_, v___y_3625_);
                v_a_3634_ = lean_ctor_get(v___x_3633_, 0);
                v_isSharedCheck_3642_ = (!lean_is_exclusive(v___x_3633_)) as u8;
                if v_isSharedCheck_3642_ == 0 {
                    v___x_3636_ = v___x_3633_;
                    v_isShared_3637_ = v_isSharedCheck_3642_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3634_);
                    lean_dec(v___x_3633_);
                    v___x_3636_ = lean_box(0);
                    v_isShared_3637_ = v_isSharedCheck_3642_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3638_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3638_, 0, v___x_3632_);
                lean_ctor_set(v___x_3638_, 1, v_a_3634_);
                if v_isShared_3637_ == 0 {
                    lean_ctor_set_tag(v___x_3636_, 1);
                    lean_ctor_set(v___x_3636_, 0, v___x_3638_);
                    v___x_3640_ = v___x_3636_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3641_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3641_, 0, v___x_3638_);
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
    mut v_msg_3643_: *mut LeanObject,
    mut v___y_3644_: *mut LeanObject,
    mut v___y_3645_: *mut LeanObject,
    mut v___y_3646_: *mut LeanObject,
    mut v___y_3647_: *mut LeanObject,
    mut v___y_3648_: *mut LeanObject,
    mut v___y_3649_: *mut LeanObject,
    mut v___y_3650_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3651_: *mut LeanObject = core::ptr::null_mut();
    v_res_3651_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0___redArg(v_msg_3643_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_);
    lean_dec(v___y_3649_);
    lean_dec_ref(v___y_3648_);
    lean_dec(v___y_3647_);
    lean_dec_ref(v___y_3646_);
    lean_dec(v___y_3645_);
    lean_dec_ref(v___y_3644_);
    return v_res_3651_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0___redArg(
    mut v_ref_3652_: *mut LeanObject,
    mut v_msg_3653_: *mut LeanObject,
    mut v___y_3654_: *mut LeanObject,
    mut v___y_3655_: *mut LeanObject,
    mut v___y_3656_: *mut LeanObject,
    mut v___y_3657_: *mut LeanObject,
    mut v___y_3658_: *mut LeanObject,
    mut v___y_3659_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_3661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_3673_: u8 = 0;
    let mut v_cancelTk_x3f_3674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3675_: u8 = 0;
    let mut v_inheritedTraceOptions_3676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut LeanObject = core::ptr::null_mut();
    v_fileName_3661_ = lean_ctor_get(v___y_3658_, 0);
    v_fileMap_3662_ = lean_ctor_get(v___y_3658_, 1);
    v_options_3663_ = lean_ctor_get(v___y_3658_, 2);
    v_currRecDepth_3664_ = lean_ctor_get(v___y_3658_, 3);
    v_maxRecDepth_3665_ = lean_ctor_get(v___y_3658_, 4);
    v_ref_3666_ = lean_ctor_get(v___y_3658_, 5);
    v_currNamespace_3667_ = lean_ctor_get(v___y_3658_, 6);
    v_openDecls_3668_ = lean_ctor_get(v___y_3658_, 7);
    v_initHeartbeats_3669_ = lean_ctor_get(v___y_3658_, 8);
    v_maxHeartbeats_3670_ = lean_ctor_get(v___y_3658_, 9);
    v_quotContext_3671_ = lean_ctor_get(v___y_3658_, 10);
    v_currMacroScope_3672_ = lean_ctor_get(v___y_3658_, 11);
    v_diag_3673_ = lean_ctor_get_uint8(
        v___y_3658_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_3674_ = lean_ctor_get(v___y_3658_, 12);
    v_suppressElabErrors_3675_ = lean_ctor_get_uint8(
        v___y_3658_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_3676_ = lean_ctor_get(v___y_3658_, 13);
    v_ref_3677_ = l_Lean_replaceRef(v_ref_3652_, v_ref_3666_);
    lean_inc_ref(v_inheritedTraceOptions_3676_);
    lean_inc(v_cancelTk_x3f_3674_);
    lean_inc(v_currMacroScope_3672_);
    lean_inc(v_quotContext_3671_);
    lean_inc(v_maxHeartbeats_3670_);
    lean_inc(v_initHeartbeats_3669_);
    lean_inc(v_openDecls_3668_);
    lean_inc(v_currNamespace_3667_);
    lean_inc(v_maxRecDepth_3665_);
    lean_inc(v_currRecDepth_3664_);
    lean_inc_ref(v_options_3663_);
    lean_inc_ref(v_fileMap_3662_);
    lean_inc_ref(v_fileName_3661_);
    v___x_3678_ = lean_alloc_ctor(0, 14, (2) as u32);
    lean_ctor_set(v___x_3678_, 0, v_fileName_3661_);
    lean_ctor_set(v___x_3678_, 1, v_fileMap_3662_);
    lean_ctor_set(v___x_3678_, 2, v_options_3663_);
    lean_ctor_set(v___x_3678_, 3, v_currRecDepth_3664_);
    lean_ctor_set(v___x_3678_, 4, v_maxRecDepth_3665_);
    lean_ctor_set(v___x_3678_, 5, v_ref_3677_);
    lean_ctor_set(v___x_3678_, 6, v_currNamespace_3667_);
    lean_ctor_set(v___x_3678_, 7, v_openDecls_3668_);
    lean_ctor_set(v___x_3678_, 8, v_initHeartbeats_3669_);
    lean_ctor_set(v___x_3678_, 9, v_maxHeartbeats_3670_);
    lean_ctor_set(v___x_3678_, 10, v_quotContext_3671_);
    lean_ctor_set(v___x_3678_, 11, v_currMacroScope_3672_);
    lean_ctor_set(v___x_3678_, 12, v_cancelTk_x3f_3674_);
    lean_ctor_set(v___x_3678_, 13, v_inheritedTraceOptions_3676_);
    lean_ctor_set_uint8(
        v___x_3678_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
        v_diag_3673_,
    );
    lean_ctor_set_uint8(
        v___x_3678_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_3675_,
    );
    v___x_3679_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0___redArg(v_msg_3653_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_, v___x_3678_, v___y_3659_);
    lean_dec_ref_known(v___x_3678_, 14);
    return v___x_3679_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0___redArg___boxed(
    mut v_ref_3680_: *mut LeanObject,
    mut v_msg_3681_: *mut LeanObject,
    mut v___y_3682_: *mut LeanObject,
    mut v___y_3683_: *mut LeanObject,
    mut v___y_3684_: *mut LeanObject,
    mut v___y_3685_: *mut LeanObject,
    mut v___y_3686_: *mut LeanObject,
    mut v___y_3687_: *mut LeanObject,
    mut v___y_3688_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3689_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_3687_);
    lean_dec_ref(v___y_3686_);
    lean_dec(v___y_3685_);
    lean_dec_ref(v___y_3684_);
    lean_dec(v___y_3683_);
    lean_dec_ref(v___y_3682_);
    lean_dec(v_ref_3680_);
    return v_res_3689_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__1()
-> *mut LeanObject {
    let mut v___x_3691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3692_: *mut LeanObject = core::ptr::null_mut();
    v___x_3691_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__0;
    v___x_3692_ = l_Lean_stringToMessageData(v___x_3691_);
    return v___x_3692_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3()
-> *mut LeanObject {
    let mut v___x_3694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: *mut LeanObject = core::ptr::null_mut();
    v___x_3694_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__2;
    v___x_3695_ = l_Lean_stringToMessageData(v___x_3694_);
    return v___x_3695_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__5()
-> *mut LeanObject {
    let mut v___x_3697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut LeanObject = core::ptr::null_mut();
    v___x_3697_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__4;
    v___x_3698_ = l_Lean_stringToMessageData(v___x_3697_);
    return v___x_3698_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__7()
-> *mut LeanObject {
    let mut v___x_3700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: *mut LeanObject = core::ptr::null_mut();
    v___x_3700_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__6;
    v___x_3701_ = l_Lean_stringToMessageData(v___x_3700_);
    return v___x_3701_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1(
    mut v_as_3702_: *mut LeanObject,
    mut v_sz_3703_: usize,
    mut v_i_3704_: usize,
    mut v_b_3705_: *mut LeanObject,
    mut v___y_3706_: *mut LeanObject,
    mut v___y_3707_: *mut LeanObject,
    mut v___y_3708_: *mut LeanObject,
    mut v___y_3709_: *mut LeanObject,
    mut v___y_3710_: *mut LeanObject,
    mut v___y_3711_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: usize = 0;
    let mut v___x_3716_: usize = 0;
    let mut v___y_3719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: u8 = 0;
    let mut v___x_3725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3730_: u8 = 0;
    let mut v_a_3731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_term_3741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_3742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_3754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_3766_: u8 = 0;
    let mut v_cancelTk_x3f_3767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3768_: u8 = 0;
    let mut v_inheritedTraceOptions_3769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3777_: u8 = 0;
    let mut v___x_3779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3781_: u8 = 0;
    let mut v_a_3782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3785_: u8 = 0;
    let mut v___x_3787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3789_: u8 = 0;
    let mut v_a_3790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3797_: u8 = 0;
    let mut v___x_3799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3801_: u8 = 0;
    let mut v_a_3803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3812_: u8 = 0;
    let mut v_fst_3813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3817_: u8 = 0;
    let mut v_val_3818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3821_: u8 = 0;
    let mut v___x_3822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_term_3826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3849_: u8 = 0;
    let mut v___x_3851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3853_: u8 = 0;
    let mut v_reuseFailAlloc_3854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3859_: u8 = 0;
    let mut v___x_3861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3863_: u8 = 0;
    let mut v_a_3864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3867_: u8 = 0;
    let mut v___x_3869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3871_: u8 = 0;
    let mut v_a_3872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3875_: u8 = 0;
    let mut v___x_3877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3879_: u8 = 0;
    let mut v_isSharedCheck_3880_: u8 = 0;
    let mut v_snd_3881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3882_: u8 = 0;
    let mut v_unused_3883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_term_3884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3893_: u8 = 0;
    let mut v___x_3895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3897_: u8 = 0;
    let mut v_a_3898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3901_: u8 = 0;
    let mut v___x_3903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3905_: u8 = 0;
    let mut v_a_3906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3909_: u8 = 0;
    let mut v___x_3911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3913_: u8 = 0;
    let mut v_val_3914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_term_3917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3923_: u8 = 0;
    let mut v___x_3925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3927_: u8 = 0;
    let mut v_a_3928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3931_: u8 = 0;
    let mut v___x_3933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3935_: u8 = 0;
    let mut v_term_3936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3937_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3724_ = lean_usize_dec_lt(v_i_3704_, v_sz_3703_);
                if v___x_3724_ == 0 {
                    v___x_3725_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3725_, 0, v_b_3705_);
                    return v___x_3725_;
                } else {
                    v_fst_3726_ = lean_ctor_get(v_b_3705_, 0);
                    v_snd_3727_ = lean_ctor_get(v_b_3705_, 1);
                    v_isSharedCheck_3937_ = (!lean_is_exclusive(v_b_3705_)) as u8;
                    if v_isSharedCheck_3937_ == 0 {
                        v___x_3729_ = v_b_3705_;
                        v_isShared_3730_ = v_isSharedCheck_3937_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_snd_3727_);
                        lean_inc(v_fst_3726_);
                        lean_dec(v_b_3705_);
                        v___x_3729_ = lean_box(0);
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
                v___x_3721_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3721_, 0, v_a_3720_);
                v___x_3722_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3722_, 0, v___y_3719_);
                v___x_3723_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3723_, 0, v___x_3721_);
                lean_ctor_set(v___x_3723_, 1, v___x_3722_);
                v_a_3714_ = v___x_3723_;
                state = 1;
                continue;
            }
            3 => {
                v_a_3731_ = lean_array_uget_borrowed(v_as_3702_, v_i_3704_);
                if lean_obj_tag(v_snd_3727_) == 1 {
                    v_val_3914_ = lean_ctor_get(v_snd_3727_, 0);
                    lean_inc(v___y_3711_);
                    lean_inc_ref(v___y_3710_);
                    lean_inc(v___y_3709_);
                    lean_inc_ref(v___y_3708_);
                    lean_inc(v_val_3914_);
                    v___x_3915_ = lean_infer_type(
                        v_val_3914_,
                        v___y_3708_,
                        v___y_3709_,
                        v___y_3710_,
                        v___y_3711_,
                    );
                    if lean_obj_tag(v___x_3915_) == 0 {
                        v_a_3916_ = lean_ctor_get(v___x_3915_, 0);
                        lean_inc(v_a_3916_);
                        lean_dec_ref_known(v___x_3915_, 1);
                        v_term_3917_ = lean_ctor_get(v_a_3731_, 1);
                        lean_inc(v_term_3917_);
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
                        if lean_obj_tag(v___x_3918_) == 0 {
                            v_a_3919_ = lean_ctor_get(v___x_3918_, 0);
                            lean_inc(v_a_3919_);
                            lean_dec_ref_known(v___x_3918_, 1);
                            v_a_3803_ = v_a_3919_;
                            state = 12;
                            continue;
                        } else {
                            lean_dec_ref_known(v_snd_3727_, 1);
                            lean_del_object(v___x_3729_);
                            lean_dec(v_fst_3726_);
                            v_a_3920_ = lean_ctor_get(v___x_3918_, 0);
                            v_isSharedCheck_3927_ = (!lean_is_exclusive(v___x_3918_)) as u8;
                            if v_isSharedCheck_3927_ == 0 {
                                v___x_3922_ = v___x_3918_;
                                v_isShared_3923_ = v_isSharedCheck_3927_;
                                state = 31;
                                continue;
                            } else {
                                lean_inc(v_a_3920_);
                                lean_dec(v___x_3918_);
                                v___x_3922_ = lean_box(0);
                                v_isShared_3923_ = v_isSharedCheck_3927_;
                                state = 31;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref_known(v_snd_3727_, 1);
                        lean_del_object(v___x_3729_);
                        lean_dec(v_fst_3726_);
                        v_a_3928_ = lean_ctor_get(v___x_3915_, 0);
                        v_isSharedCheck_3935_ = (!lean_is_exclusive(v___x_3915_)) as u8;
                        if v_isSharedCheck_3935_ == 0 {
                            v___x_3930_ = v___x_3915_;
                            v_isShared_3931_ = v_isSharedCheck_3935_;
                            state = 33;
                            continue;
                        } else {
                            lean_inc(v_a_3928_);
                            lean_dec(v___x_3915_);
                            v___x_3930_ = lean_box(0);
                            v_isShared_3931_ = v_isSharedCheck_3935_;
                            state = 33;
                            continue;
                        }
                    }
                } else {
                    v_term_3936_ = lean_ctor_get(v_a_3731_, 1);
                    lean_inc(v_term_3936_);
                    v_a_3803_ = v_term_3936_;
                    state = 12;
                    continue;
                }
            }
            4 => {
                v_term_3741_ = lean_ctor_get(v_a_3731_, 1);
                v_proof_3742_ = lean_ctor_get(v_a_3731_, 2);
                lean_inc_ref(v___y_3734_);
                v___x_3743_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3743_, 0, v___y_3734_);
                v___x_3744_ = lean_box(0);
                v___x_3745_ = lean_box((v___x_3724_) as usize);
                v___x_3746_ = lean_box((v___x_3724_) as usize);
                lean_inc(v___y_3738_);
                lean_inc_ref(v___y_3737_);
                lean_inc(v___y_3736_);
                lean_inc_ref(v___y_3735_);
                lean_inc(v_proof_3742_);
                v___x_3747_ = lean_alloc_closure(
                    l_Lean_Elab_Term_elabTermEnsuringType___boxed as *mut core::ffi::c_void,
                    12,
                    9,
                );
                lean_closure_set(v___x_3747_, 0, v_proof_3742_);
                lean_closure_set(v___x_3747_, 1, v___x_3743_);
                lean_closure_set(v___x_3747_, 2, v___x_3745_);
                lean_closure_set(v___x_3747_, 3, v___x_3746_);
                lean_closure_set(v___x_3747_, 4, v___x_3744_);
                lean_closure_set(v___x_3747_, 5, v___y_3735_);
                lean_closure_set(v___x_3747_, 6, v___y_3736_);
                lean_closure_set(v___x_3747_, 7, v___y_3737_);
                lean_closure_set(v___x_3747_, 8, v___y_3738_);
                v___x_3748_ =
                    l_Lean_Core_withFreshMacroScope___redArg(v___x_3747_, v___y_3739_, v___y_3740_);
                if lean_obj_tag(v___x_3748_) == 0 {
                    if lean_obj_tag(v_fst_3726_) == 1 {
                        lean_del_object(v___x_3729_);
                        v_val_3749_ = lean_ctor_get(v_fst_3726_, 0);
                        lean_inc(v_val_3749_);
                        lean_dec_ref_known(v_fst_3726_, 1);
                        v_a_3750_ = lean_ctor_get(v___x_3748_, 0);
                        lean_inc(v_a_3750_);
                        lean_dec_ref_known(v___x_3748_, 1);
                        v_fst_3751_ = lean_ctor_get(v_val_3749_, 0);
                        lean_inc(v_fst_3751_);
                        v_snd_3752_ = lean_ctor_get(v_val_3749_, 1);
                        lean_inc(v_snd_3752_);
                        lean_dec(v_val_3749_);
                        v___x_3753_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsUsingDefault(
                            v___y_3735_,
                            v___y_3736_,
                            v___y_3737_,
                            v___y_3738_,
                            v___y_3739_,
                            v___y_3740_,
                        );
                        if lean_obj_tag(v___x_3753_) == 0 {
                            lean_dec_ref_known(v___x_3753_, 1);
                            v_fileName_3754_ = lean_ctor_get(v___y_3739_, 0);
                            v_fileMap_3755_ = lean_ctor_get(v___y_3739_, 1);
                            v_options_3756_ = lean_ctor_get(v___y_3739_, 2);
                            v_currRecDepth_3757_ = lean_ctor_get(v___y_3739_, 3);
                            v_maxRecDepth_3758_ = lean_ctor_get(v___y_3739_, 4);
                            v_ref_3759_ = lean_ctor_get(v___y_3739_, 5);
                            v_currNamespace_3760_ = lean_ctor_get(v___y_3739_, 6);
                            v_openDecls_3761_ = lean_ctor_get(v___y_3739_, 7);
                            v_initHeartbeats_3762_ = lean_ctor_get(v___y_3739_, 8);
                            v_maxHeartbeats_3763_ = lean_ctor_get(v___y_3739_, 9);
                            v_quotContext_3764_ = lean_ctor_get(v___y_3739_, 10);
                            v_currMacroScope_3765_ = lean_ctor_get(v___y_3739_, 11);
                            v_diag_3766_ = lean_ctor_get_uint8(
                                v___y_3739_,
                                (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                            );
                            v_cancelTk_x3f_3767_ = lean_ctor_get(v___y_3739_, 12);
                            v_suppressElabErrors_3768_ = lean_ctor_get_uint8(
                                v___y_3739_,
                                (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                            );
                            v_inheritedTraceOptions_3769_ = lean_ctor_get(v___y_3739_, 13);
                            v_ref_3770_ = l_Lean_replaceRef(v_term_3741_, v_ref_3759_);
                            lean_inc_ref(v_inheritedTraceOptions_3769_);
                            lean_inc(v_cancelTk_x3f_3767_);
                            lean_inc(v_currMacroScope_3765_);
                            lean_inc(v_quotContext_3764_);
                            lean_inc(v_maxHeartbeats_3763_);
                            lean_inc(v_initHeartbeats_3762_);
                            lean_inc(v_openDecls_3761_);
                            lean_inc(v_currNamespace_3760_);
                            lean_inc(v_maxRecDepth_3758_);
                            lean_inc(v_currRecDepth_3757_);
                            lean_inc_ref(v_options_3756_);
                            lean_inc_ref(v_fileMap_3755_);
                            lean_inc_ref(v_fileName_3754_);
                            v___x_3771_ = lean_alloc_ctor(0, 14, (2) as u32);
                            lean_ctor_set(v___x_3771_, 0, v_fileName_3754_);
                            lean_ctor_set(v___x_3771_, 1, v_fileMap_3755_);
                            lean_ctor_set(v___x_3771_, 2, v_options_3756_);
                            lean_ctor_set(v___x_3771_, 3, v_currRecDepth_3757_);
                            lean_ctor_set(v___x_3771_, 4, v_maxRecDepth_3758_);
                            lean_ctor_set(v___x_3771_, 5, v_ref_3770_);
                            lean_ctor_set(v___x_3771_, 6, v_currNamespace_3760_);
                            lean_ctor_set(v___x_3771_, 7, v_openDecls_3761_);
                            lean_ctor_set(v___x_3771_, 8, v_initHeartbeats_3762_);
                            lean_ctor_set(v___x_3771_, 9, v_maxHeartbeats_3763_);
                            lean_ctor_set(v___x_3771_, 10, v_quotContext_3764_);
                            lean_ctor_set(v___x_3771_, 11, v_currMacroScope_3765_);
                            lean_ctor_set(v___x_3771_, 12, v_cancelTk_x3f_3767_);
                            lean_ctor_set(v___x_3771_, 13, v_inheritedTraceOptions_3769_);
                            lean_ctor_set_uint8(
                                v___x_3771_,
                                (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                                v_diag_3766_,
                            );
                            lean_ctor_set_uint8(
                                v___x_3771_,
                                (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
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
                            lean_dec_ref_known(v___x_3771_, 14);
                            lean_dec(v_snd_3752_);
                            if lean_obj_tag(v___x_3772_) == 0 {
                                v_a_3773_ = lean_ctor_get(v___x_3772_, 0);
                                lean_inc(v_a_3773_);
                                lean_dec_ref_known(v___x_3772_, 1);
                                v___y_3719_ = v___y_3733_;
                                v_a_3720_ = v_a_3773_;
                                state = 2;
                                continue;
                            } else {
                                lean_dec_ref(v___y_3733_);
                                v_a_3774_ = lean_ctor_get(v___x_3772_, 0);
                                v_isSharedCheck_3781_ = (!lean_is_exclusive(v___x_3772_)) as u8;
                                if v_isSharedCheck_3781_ == 0 {
                                    v___x_3776_ = v___x_3772_;
                                    v_isShared_3777_ = v_isSharedCheck_3781_;
                                    state = 5;
                                    continue;
                                } else {
                                    lean_inc(v_a_3774_);
                                    lean_dec(v___x_3772_);
                                    v___x_3776_ = lean_box(0);
                                    v_isShared_3777_ = v_isSharedCheck_3781_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_snd_3752_);
                            lean_dec(v_fst_3751_);
                            lean_dec(v_a_3750_);
                            lean_dec_ref(v___y_3734_);
                            lean_dec_ref(v___y_3733_);
                            v_a_3782_ = lean_ctor_get(v___x_3753_, 0);
                            v_isSharedCheck_3789_ = (!lean_is_exclusive(v___x_3753_)) as u8;
                            if v_isSharedCheck_3789_ == 0 {
                                v___x_3784_ = v___x_3753_;
                                v_isShared_3785_ = v_isSharedCheck_3789_;
                                state = 7;
                                continue;
                            } else {
                                lean_inc(v_a_3782_);
                                lean_dec(v___x_3753_);
                                v___x_3784_ = lean_box(0);
                                v_isShared_3785_ = v_isSharedCheck_3789_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_fst_3726_);
                        v_a_3790_ = lean_ctor_get(v___x_3748_, 0);
                        lean_inc(v_a_3790_);
                        lean_dec_ref_known(v___x_3748_, 1);
                        if v_isShared_3730_ == 0 {
                            lean_ctor_set(v___x_3729_, 1, v___y_3734_);
                            lean_ctor_set(v___x_3729_, 0, v_a_3790_);
                            v___x_3792_ = v___x_3729_;
                            state = 9;
                            continue;
                        } else {
                            v_reuseFailAlloc_3793_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3793_, 0, v_a_3790_);
                            lean_ctor_set(v_reuseFailAlloc_3793_, 1, v___y_3734_);
                            v___x_3792_ = v_reuseFailAlloc_3793_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_3734_);
                    lean_dec_ref(v___y_3733_);
                    lean_del_object(v___x_3729_);
                    lean_dec(v_fst_3726_);
                    v_a_3794_ = lean_ctor_get(v___x_3748_, 0);
                    v_isSharedCheck_3801_ = (!lean_is_exclusive(v___x_3748_)) as u8;
                    if v_isSharedCheck_3801_ == 0 {
                        v___x_3796_ = v___x_3748_;
                        v_isShared_3797_ = v_isSharedCheck_3801_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_3794_);
                        lean_dec(v___x_3748_);
                        v___x_3796_ = lean_box(0);
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
                    v_reuseFailAlloc_3780_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3780_, 0, v_a_3774_);
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
                    v_reuseFailAlloc_3788_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3788_, 0, v_a_3782_);
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
                    v_reuseFailAlloc_3800_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3800_, 0, v_a_3794_);
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
                if lean_obj_tag(v___x_3804_) == 0 {
                    v_a_3805_ = lean_ctor_get(v___x_3804_, 0);
                    lean_inc(v_a_3805_);
                    lean_dec_ref_known(v___x_3804_, 1);
                    v___x_3806_ = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(v_a_3805_);
                    if lean_obj_tag(v___x_3806_) == 0 {
                        v_a_3807_ = lean_ctor_get(v___x_3806_, 0);
                        lean_inc(v_a_3807_);
                        lean_dec_ref_known(v___x_3806_, 1);
                        if lean_obj_tag(v_a_3807_) == 1 {
                            v_val_3808_ = lean_ctor_get(v_a_3807_, 0);
                            lean_inc(v_val_3808_);
                            lean_dec_ref_known(v_a_3807_, 1);
                            v_snd_3809_ = lean_ctor_get(v_val_3808_, 1);
                            v_isSharedCheck_3882_ = (!lean_is_exclusive(v_val_3808_)) as u8;
                            if v_isSharedCheck_3882_ == 0 {
                                v_unused_3883_ = lean_ctor_get(v_val_3808_, 0);
                                lean_dec(v_unused_3883_);
                                v___x_3811_ = v_val_3808_;
                                v_isShared_3812_ = v_isSharedCheck_3882_;
                                state = 13;
                                continue;
                            } else {
                                lean_inc(v_snd_3809_);
                                lean_dec(v_val_3808_);
                                v___x_3811_ = lean_box(0);
                                v_isShared_3812_ = v_isSharedCheck_3882_;
                                state = 13;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_3807_);
                            lean_del_object(v___x_3729_);
                            v_term_3884_ = lean_ctor_get(v_a_3731_, 1);
                            v___x_3885_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__7), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__7_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__7);
                            v___x_3886_ = l_Lean_indentExpr(v_a_3805_);
                            v___x_3887_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_3887_, 0, v___x_3885_);
                            lean_ctor_set(v___x_3887_, 1, v___x_3886_);
                            v___x_3888_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0___redArg(v_term_3884_, v___x_3887_, v___y_3706_, v___y_3707_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_);
                            if lean_obj_tag(v___x_3888_) == 0 {
                                lean_dec_ref_known(v___x_3888_, 1);
                                v___x_3889_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v___x_3889_, 0, v_fst_3726_);
                                lean_ctor_set(v___x_3889_, 1, v_snd_3727_);
                                v_a_3714_ = v___x_3889_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec(v_snd_3727_);
                                lean_dec(v_fst_3726_);
                                v_a_3890_ = lean_ctor_get(v___x_3888_, 0);
                                v_isSharedCheck_3897_ = (!lean_is_exclusive(v___x_3888_)) as u8;
                                if v_isSharedCheck_3897_ == 0 {
                                    v___x_3892_ = v___x_3888_;
                                    v_isShared_3893_ = v_isSharedCheck_3897_;
                                    state = 25;
                                    continue;
                                } else {
                                    lean_inc(v_a_3890_);
                                    lean_dec(v___x_3888_);
                                    v___x_3892_ = lean_box(0);
                                    v_isShared_3893_ = v_isSharedCheck_3897_;
                                    state = 25;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec(v_a_3805_);
                        lean_del_object(v___x_3729_);
                        lean_dec(v_snd_3727_);
                        lean_dec(v_fst_3726_);
                        v_a_3898_ = lean_ctor_get(v___x_3806_, 0);
                        v_isSharedCheck_3905_ = (!lean_is_exclusive(v___x_3806_)) as u8;
                        if v_isSharedCheck_3905_ == 0 {
                            v___x_3900_ = v___x_3806_;
                            v_isShared_3901_ = v_isSharedCheck_3905_;
                            state = 27;
                            continue;
                        } else {
                            lean_inc(v_a_3898_);
                            lean_dec(v___x_3806_);
                            v___x_3900_ = lean_box(0);
                            v_isShared_3901_ = v_isSharedCheck_3905_;
                            state = 27;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_3729_);
                    lean_dec(v_snd_3727_);
                    lean_dec(v_fst_3726_);
                    v_a_3906_ = lean_ctor_get(v___x_3804_, 0);
                    v_isSharedCheck_3913_ = (!lean_is_exclusive(v___x_3804_)) as u8;
                    if v_isSharedCheck_3913_ == 0 {
                        v___x_3908_ = v___x_3804_;
                        v_isShared_3909_ = v_isSharedCheck_3913_;
                        state = 29;
                        continue;
                    } else {
                        lean_inc(v_a_3906_);
                        lean_dec(v___x_3804_);
                        v___x_3908_ = lean_box(0);
                        v_isShared_3909_ = v_isSharedCheck_3913_;
                        state = 29;
                        continue;
                    }
                }
            }
            13 => {
                if lean_obj_tag(v_snd_3727_) == 1 {
                    v_fst_3813_ = lean_ctor_get(v_snd_3809_, 0);
                    v_snd_3814_ = lean_ctor_get(v_snd_3809_, 1);
                    v_isSharedCheck_3880_ = (!lean_is_exclusive(v_snd_3809_)) as u8;
                    if v_isSharedCheck_3880_ == 0 {
                        v___x_3816_ = v_snd_3809_;
                        v_isShared_3817_ = v_isSharedCheck_3880_;
                        state = 14;
                        continue;
                    } else {
                        lean_inc(v_snd_3814_);
                        lean_inc(v_fst_3813_);
                        lean_dec(v_snd_3809_);
                        v___x_3816_ = lean_box(0);
                        v_isShared_3817_ = v_isSharedCheck_3880_;
                        state = 14;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3811_);
                    lean_dec(v_snd_3727_);
                    v_snd_3881_ = lean_ctor_get(v_snd_3809_, 1);
                    lean_inc(v_snd_3881_);
                    lean_dec(v_snd_3809_);
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
                v_val_3818_ = lean_ctor_get(v_snd_3727_, 0);
                lean_inc_n(v_val_3818_, 2);
                lean_dec_ref_known(v_snd_3727_, 1);
                lean_inc(v_fst_3813_);
                v___x_3819_ = l_Lean_Meta_isExprDefEqGuarded(
                    v_fst_3813_,
                    v_val_3818_,
                    v___y_3708_,
                    v___y_3709_,
                    v___y_3710_,
                    v___y_3711_,
                );
                if lean_obj_tag(v___x_3819_) == 0 {
                    v_a_3820_ = lean_ctor_get(v___x_3819_, 0);
                    lean_inc(v_a_3820_);
                    lean_dec_ref_known(v___x_3819_, 1);
                    v___x_3821_ = (lean_unbox(v_a_3820_) as u8);
                    lean_dec(v_a_3820_);
                    if v___x_3821_ == 0 {
                        lean_inc(v___y_3711_);
                        lean_inc_ref(v___y_3710_);
                        lean_inc(v___y_3709_);
                        lean_inc_ref(v___y_3708_);
                        lean_inc(v_fst_3813_);
                        v___x_3822_ = lean_infer_type(
                            v_fst_3813_,
                            v___y_3708_,
                            v___y_3709_,
                            v___y_3710_,
                            v___y_3711_,
                        );
                        if lean_obj_tag(v___x_3822_) == 0 {
                            v_a_3823_ = lean_ctor_get(v___x_3822_, 0);
                            lean_inc(v_a_3823_);
                            lean_dec_ref_known(v___x_3822_, 1);
                            lean_inc(v___y_3711_);
                            lean_inc_ref(v___y_3710_);
                            lean_inc(v___y_3709_);
                            lean_inc_ref(v___y_3708_);
                            lean_inc(v_val_3818_);
                            v___x_3824_ = lean_infer_type(
                                v_val_3818_,
                                v___y_3708_,
                                v___y_3709_,
                                v___y_3710_,
                                v___y_3711_,
                            );
                            if lean_obj_tag(v___x_3824_) == 0 {
                                v_a_3825_ = lean_ctor_get(v___x_3824_, 0);
                                lean_inc(v_a_3825_);
                                lean_dec_ref_known(v___x_3824_, 1);
                                v_term_3826_ = lean_ctor_get(v_a_3731_, 1);
                                v___x_3827_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__1);
                                v___x_3828_ = l_Lean_MessageData_ofExpr(v_fst_3813_);
                                v___x_3829_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3);
                                if v_isShared_3817_ == 0 {
                                    lean_ctor_set_tag(v___x_3816_, 7);
                                    lean_ctor_set(v___x_3816_, 1, v___x_3829_);
                                    lean_ctor_set(v___x_3816_, 0, v___x_3828_);
                                    v___x_3831_ = v___x_3816_;
                                    state = 15;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3855_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_3855_, 0, v___x_3828_);
                                    lean_ctor_set(v_reuseFailAlloc_3855_, 1, v___x_3829_);
                                    v___x_3831_ = v_reuseFailAlloc_3855_;
                                    state = 15;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_3823_);
                                lean_dec(v_val_3818_);
                                lean_del_object(v___x_3816_);
                                lean_dec(v_snd_3814_);
                                lean_dec(v_fst_3813_);
                                lean_del_object(v___x_3811_);
                                lean_dec(v_a_3805_);
                                lean_del_object(v___x_3729_);
                                lean_dec(v_fst_3726_);
                                v_a_3856_ = lean_ctor_get(v___x_3824_, 0);
                                v_isSharedCheck_3863_ = (!lean_is_exclusive(v___x_3824_)) as u8;
                                if v_isSharedCheck_3863_ == 0 {
                                    v___x_3858_ = v___x_3824_;
                                    v_isShared_3859_ = v_isSharedCheck_3863_;
                                    state = 19;
                                    continue;
                                } else {
                                    lean_inc(v_a_3856_);
                                    lean_dec(v___x_3824_);
                                    v___x_3858_ = lean_box(0);
                                    v_isShared_3859_ = v_isSharedCheck_3863_;
                                    state = 19;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_val_3818_);
                            lean_del_object(v___x_3816_);
                            lean_dec(v_snd_3814_);
                            lean_dec(v_fst_3813_);
                            lean_del_object(v___x_3811_);
                            lean_dec(v_a_3805_);
                            lean_del_object(v___x_3729_);
                            lean_dec(v_fst_3726_);
                            v_a_3864_ = lean_ctor_get(v___x_3822_, 0);
                            v_isSharedCheck_3871_ = (!lean_is_exclusive(v___x_3822_)) as u8;
                            if v_isSharedCheck_3871_ == 0 {
                                v___x_3866_ = v___x_3822_;
                                v_isShared_3867_ = v_isSharedCheck_3871_;
                                state = 21;
                                continue;
                            } else {
                                lean_inc(v_a_3864_);
                                lean_dec(v___x_3822_);
                                v___x_3866_ = lean_box(0);
                                v_isShared_3867_ = v_isSharedCheck_3871_;
                                state = 21;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_val_3818_);
                        lean_del_object(v___x_3816_);
                        lean_dec(v_fst_3813_);
                        lean_del_object(v___x_3811_);
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
                    lean_dec(v_val_3818_);
                    lean_del_object(v___x_3816_);
                    lean_dec(v_snd_3814_);
                    lean_dec(v_fst_3813_);
                    lean_del_object(v___x_3811_);
                    lean_dec(v_a_3805_);
                    lean_del_object(v___x_3729_);
                    lean_dec(v_fst_3726_);
                    v_a_3872_ = lean_ctor_get(v___x_3819_, 0);
                    v_isSharedCheck_3879_ = (!lean_is_exclusive(v___x_3819_)) as u8;
                    if v_isSharedCheck_3879_ == 0 {
                        v___x_3874_ = v___x_3819_;
                        v_isShared_3875_ = v_isSharedCheck_3879_;
                        state = 23;
                        continue;
                    } else {
                        lean_inc(v_a_3872_);
                        lean_dec(v___x_3819_);
                        v___x_3874_ = lean_box(0);
                        v_isShared_3875_ = v_isSharedCheck_3879_;
                        state = 23;
                        continue;
                    }
                }
            }
            15 => {
                v___x_3832_ = l_Lean_MessageData_ofExpr(v_a_3823_);
                if v_isShared_3812_ == 0 {
                    lean_ctor_set_tag(v___x_3811_, 7);
                    lean_ctor_set(v___x_3811_, 1, v___x_3832_);
                    lean_ctor_set(v___x_3811_, 0, v___x_3831_);
                    v___x_3834_ = v___x_3811_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3854_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3854_, 0, v___x_3831_);
                    lean_ctor_set(v_reuseFailAlloc_3854_, 1, v___x_3832_);
                    v___x_3834_ = v_reuseFailAlloc_3854_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___x_3835_ = l_Lean_indentD(v___x_3834_);
                v___x_3836_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3836_, 0, v___x_3827_);
                lean_ctor_set(v___x_3836_, 1, v___x_3835_);
                v___x_3837_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__5), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__5_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__5);
                v___x_3838_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3838_, 0, v___x_3836_);
                lean_ctor_set(v___x_3838_, 1, v___x_3837_);
                v___x_3839_ = l_Lean_MessageData_ofExpr(v_val_3818_);
                v___x_3840_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3840_, 0, v___x_3839_);
                lean_ctor_set(v___x_3840_, 1, v___x_3829_);
                v___x_3841_ = l_Lean_MessageData_ofExpr(v_a_3825_);
                v___x_3842_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3842_, 0, v___x_3840_);
                lean_ctor_set(v___x_3842_, 1, v___x_3841_);
                v___x_3843_ = l_Lean_indentD(v___x_3842_);
                v___x_3844_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3844_, 0, v___x_3838_);
                lean_ctor_set(v___x_3844_, 1, v___x_3843_);
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
                if lean_obj_tag(v___x_3845_) == 0 {
                    lean_dec_ref_known(v___x_3845_, 1);
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
                    lean_dec(v_snd_3814_);
                    lean_dec(v_a_3805_);
                    lean_del_object(v___x_3729_);
                    lean_dec(v_fst_3726_);
                    v_a_3846_ = lean_ctor_get(v___x_3845_, 0);
                    v_isSharedCheck_3853_ = (!lean_is_exclusive(v___x_3845_)) as u8;
                    if v_isSharedCheck_3853_ == 0 {
                        v___x_3848_ = v___x_3845_;
                        v_isShared_3849_ = v_isSharedCheck_3853_;
                        state = 17;
                        continue;
                    } else {
                        lean_inc(v_a_3846_);
                        lean_dec(v___x_3845_);
                        v___x_3848_ = lean_box(0);
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
                    v_reuseFailAlloc_3852_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3852_, 0, v_a_3846_);
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
                    v_reuseFailAlloc_3862_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3862_, 0, v_a_3856_);
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
                    v_reuseFailAlloc_3870_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3870_, 0, v_a_3864_);
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
                    v_reuseFailAlloc_3878_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3878_, 0, v_a_3872_);
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
                    v_reuseFailAlloc_3896_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3896_, 0, v_a_3890_);
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
                    v_reuseFailAlloc_3904_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3904_, 0, v_a_3898_);
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
                    v_reuseFailAlloc_3912_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3912_, 0, v_a_3906_);
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
                    v_reuseFailAlloc_3926_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3926_, 0, v_a_3920_);
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
                    v_reuseFailAlloc_3934_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3934_, 0, v_a_3928_);
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
    mut v_as_3938_: *mut LeanObject,
    mut v_sz_3939_: *mut LeanObject,
    mut v_i_3940_: *mut LeanObject,
    mut v_b_3941_: *mut LeanObject,
    mut v___y_3942_: *mut LeanObject,
    mut v___y_3943_: *mut LeanObject,
    mut v___y_3944_: *mut LeanObject,
    mut v___y_3945_: *mut LeanObject,
    mut v___y_3946_: *mut LeanObject,
    mut v___y_3947_: *mut LeanObject,
    mut v___y_3948_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3949_: usize = 0;
    let mut v_i_boxed_3950_: usize = 0;
    let mut v_res_3951_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3949_ = lean_unbox_usize(v_sz_3939_);
    lean_dec(v_sz_3939_);
    v_i_boxed_3950_ = lean_unbox_usize(v_i_3940_);
    lean_dec(v_i_3940_);
    v_res_3951_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1(v_as_3938_, v_sz_boxed_3949_, v_i_boxed_3950_, v_b_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_, v___y_3947_);
    lean_dec(v___y_3947_);
    lean_dec_ref(v___y_3946_);
    lean_dec(v___y_3945_);
    lean_dec_ref(v___y_3944_);
    lean_dec(v___y_3943_);
    lean_dec_ref(v___y_3942_);
    lean_dec_ref(v_as_3938_);
    return v_res_3951_;
}
pub unsafe fn _init_l_Lean_Elab_Term_elabCalcSteps___closed__4() -> *mut LeanObject {
    let mut v___x_3957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut LeanObject = core::ptr::null_mut();
    v___x_3957_ = l_Lean_Elab_Term_elabCalcSteps___closed__3;
    v___x_3958_ = lean_unsigned_to_nat(14);
    v___x_3959_ = lean_unsigned_to_nat(22);
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
    mut v_steps_3963_: *mut LeanObject,
    mut v_a_3964_: *mut LeanObject,
    mut v_a_3965_: *mut LeanObject,
    mut v_a_3966_: *mut LeanObject,
    mut v_a_3967_: *mut LeanObject,
    mut v_a_3968_: *mut LeanObject,
    mut v_a_3969_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3972_: usize = 0;
    let mut v___x_3973_: usize = 0;
    let mut v___x_3974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3979_: u8 = 0;
    let mut v_fst_3980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3990_: u8 = 0;
    let mut v_unused_3991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3995_: u8 = 0;
    let mut v___x_3997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3999_: u8 = 0;
    let mut v_a_4000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4003_: u8 = 0;
    let mut v___x_4005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4007_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3971_ = l_Lean_Elab_Term_elabCalcSteps___closed__0;
                v_sz_3972_ = lean_array_size(v_steps_3963_);
                v___x_3973_ = 0usize;
                v___x_3974_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1(v_steps_3963_, v_sz_3972_, v___x_3973_, v___x_3971_, v_a_3964_, v_a_3965_, v_a_3966_, v_a_3967_, v_a_3968_, v_a_3969_);
                if lean_obj_tag(v___x_3974_) == 0 {
                    v_a_3975_ = lean_ctor_get(v___x_3974_, 0);
                    lean_inc(v_a_3975_);
                    lean_dec_ref_known(v___x_3974_, 1);
                    v___x_3976_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsUsingDefault(
                        v_a_3964_, v_a_3965_, v_a_3966_, v_a_3967_, v_a_3968_, v_a_3969_,
                    );
                    if lean_obj_tag(v___x_3976_) == 0 {
                        v_isSharedCheck_3990_ = (!lean_is_exclusive(v___x_3976_)) as u8;
                        if v_isSharedCheck_3990_ == 0 {
                            v_unused_3991_ = lean_ctor_get(v___x_3976_, 0);
                            lean_dec(v_unused_3991_);
                            v___x_3978_ = v___x_3976_;
                            v_isShared_3979_ = v_isSharedCheck_3990_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___x_3976_);
                            v___x_3978_ = lean_box(0);
                            v_isShared_3979_ = v_isSharedCheck_3990_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_3975_);
                        v_a_3992_ = lean_ctor_get(v___x_3976_, 0);
                        v_isSharedCheck_3999_ = (!lean_is_exclusive(v___x_3976_)) as u8;
                        if v_isSharedCheck_3999_ == 0 {
                            v___x_3994_ = v___x_3976_;
                            v_isShared_3995_ = v_isSharedCheck_3999_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_3992_);
                            lean_dec(v___x_3976_);
                            v___x_3994_ = lean_box(0);
                            v_isShared_3995_ = v_isSharedCheck_3999_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_a_4000_ = lean_ctor_get(v___x_3974_, 0);
                    v_isSharedCheck_4007_ = (!lean_is_exclusive(v___x_3974_)) as u8;
                    if v_isSharedCheck_4007_ == 0 {
                        v___x_4002_ = v___x_3974_;
                        v_isShared_4003_ = v_isSharedCheck_4007_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_4000_);
                        lean_dec(v___x_3974_);
                        v___x_4002_ = lean_box(0);
                        v_isShared_4003_ = v_isSharedCheck_4007_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3980_ = lean_ctor_get(v_a_3975_, 0);
                lean_inc(v_fst_3980_);
                lean_dec(v_a_3975_);
                if lean_obj_tag(v_fst_3980_) == 0 {
                    v___x_3981_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_Term_elabCalcSteps___closed__4),
                        core::ptr::addr_of_mut!(l_Lean_Elab_Term_elabCalcSteps___closed__4_once),
                        _init_l_Lean_Elab_Term_elabCalcSteps___closed__4,
                    );
                    v___x_3982_ =
                        l_panic___at___00Lean_Elab_Term_elabCalcSteps_spec__2(v___x_3981_);
                    if v_isShared_3979_ == 0 {
                        lean_ctor_set(v___x_3978_, 0, v___x_3982_);
                        v___x_3984_ = v___x_3978_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3985_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3985_, 0, v___x_3982_);
                        v___x_3984_ = v_reuseFailAlloc_3985_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_val_3986_ = lean_ctor_get(v_fst_3980_, 0);
                    lean_inc(v_val_3986_);
                    lean_dec_ref_known(v_fst_3980_, 1);
                    if v_isShared_3979_ == 0 {
                        lean_ctor_set(v___x_3978_, 0, v_val_3986_);
                        v___x_3988_ = v___x_3978_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3989_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3989_, 0, v_val_3986_);
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
                    v_reuseFailAlloc_3998_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3998_, 0, v_a_3992_);
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
                    v_reuseFailAlloc_4006_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4006_, 0, v_a_4000_);
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
    mut v_steps_4008_: *mut LeanObject,
    mut v_a_4009_: *mut LeanObject,
    mut v_a_4010_: *mut LeanObject,
    mut v_a_4011_: *mut LeanObject,
    mut v_a_4012_: *mut LeanObject,
    mut v_a_4013_: *mut LeanObject,
    mut v_a_4014_: *mut LeanObject,
    mut v_a_4015_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4016_: *mut LeanObject = core::ptr::null_mut();
    v_res_4016_ = l_Lean_Elab_Term_elabCalcSteps(
        v_steps_4008_,
        v_a_4009_,
        v_a_4010_,
        v_a_4011_,
        v_a_4012_,
        v_a_4013_,
        v_a_4014_,
    );
    lean_dec(v_a_4014_);
    lean_dec_ref(v_a_4013_);
    lean_dec(v_a_4012_);
    lean_dec_ref(v_a_4011_);
    lean_dec(v_a_4010_);
    lean_dec_ref(v_a_4009_);
    lean_dec_ref(v_steps_4008_);
    return v_res_4016_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0(
    mut v_00_u03b1_4017_: *mut LeanObject,
    mut v_ref_4018_: *mut LeanObject,
    mut v_msg_4019_: *mut LeanObject,
    mut v___y_4020_: *mut LeanObject,
    mut v___y_4021_: *mut LeanObject,
    mut v___y_4022_: *mut LeanObject,
    mut v___y_4023_: *mut LeanObject,
    mut v___y_4024_: *mut LeanObject,
    mut v___y_4025_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4027_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_4028_: *mut LeanObject,
    mut v_ref_4029_: *mut LeanObject,
    mut v_msg_4030_: *mut LeanObject,
    mut v___y_4031_: *mut LeanObject,
    mut v___y_4032_: *mut LeanObject,
    mut v___y_4033_: *mut LeanObject,
    mut v___y_4034_: *mut LeanObject,
    mut v___y_4035_: *mut LeanObject,
    mut v___y_4036_: *mut LeanObject,
    mut v___y_4037_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4038_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_4036_);
    lean_dec_ref(v___y_4035_);
    lean_dec(v___y_4034_);
    lean_dec_ref(v___y_4033_);
    lean_dec(v___y_4032_);
    lean_dec_ref(v___y_4031_);
    lean_dec(v_ref_4029_);
    return v_res_4038_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0(
    mut v_00_u03b1_4039_: *mut LeanObject,
    mut v_msg_4040_: *mut LeanObject,
    mut v___y_4041_: *mut LeanObject,
    mut v___y_4042_: *mut LeanObject,
    mut v___y_4043_: *mut LeanObject,
    mut v___y_4044_: *mut LeanObject,
    mut v___y_4045_: *mut LeanObject,
    mut v___y_4046_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4048_: *mut LeanObject = core::ptr::null_mut();
    v___x_4048_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0___redArg(v_msg_4040_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_);
    return v___x_4048_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0___boxed(
    mut v_00_u03b1_4049_: *mut LeanObject,
    mut v_msg_4050_: *mut LeanObject,
    mut v___y_4051_: *mut LeanObject,
    mut v___y_4052_: *mut LeanObject,
    mut v___y_4053_: *mut LeanObject,
    mut v___y_4054_: *mut LeanObject,
    mut v___y_4055_: *mut LeanObject,
    mut v___y_4056_: *mut LeanObject,
    mut v___y_4057_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4058_: *mut LeanObject = core::ptr::null_mut();
    v_res_4058_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0(v_00_u03b1_4049_, v_msg_4050_, v___y_4051_, v___y_4052_, v___y_4053_, v___y_4054_, v___y_4055_, v___y_4056_);
    lean_dec(v___y_4056_);
    lean_dec_ref(v___y_4055_);
    lean_dec(v___y_4054_);
    lean_dec_ref(v___y_4053_);
    lean_dec(v___y_4052_);
    lean_dec_ref(v___y_4051_);
    return v_res_4058_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2(
    mut v_msgData_4059_: *mut LeanObject,
    mut v_macroStack_4060_: *mut LeanObject,
    mut v___y_4061_: *mut LeanObject,
    mut v___y_4062_: *mut LeanObject,
    mut v___y_4063_: *mut LeanObject,
    mut v___y_4064_: *mut LeanObject,
    mut v___y_4065_: *mut LeanObject,
    mut v___y_4066_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4068_: *mut LeanObject = core::ptr::null_mut();
    v___x_4068_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___redArg(v_msgData_4059_, v_macroStack_4060_, v___y_4065_);
    return v___x_4068_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2___boxed(
    mut v_msgData_4069_: *mut LeanObject,
    mut v_macroStack_4070_: *mut LeanObject,
    mut v___y_4071_: *mut LeanObject,
    mut v___y_4072_: *mut LeanObject,
    mut v___y_4073_: *mut LeanObject,
    mut v___y_4074_: *mut LeanObject,
    mut v___y_4075_: *mut LeanObject,
    mut v___y_4076_: *mut LeanObject,
    mut v___y_4077_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4078_: *mut LeanObject = core::ptr::null_mut();
    v_res_4078_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_elabCalcSteps_spec__0_spec__0_spec__2(v_msgData_4069_, v_macroStack_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_);
    lean_dec(v___y_4076_);
    lean_dec_ref(v___y_4075_);
    lean_dec(v___y_4074_);
    lean_dec_ref(v___y_4073_);
    lean_dec(v___y_4072_);
    lean_dec_ref(v___y_4071_);
    return v_res_4078_;
}
pub unsafe fn _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_4079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: *mut LeanObject = core::ptr::null_mut();
    v___x_4079_ = lean_box(0);
    v___x_4080_ = l_Lean_Elab_abortTermExceptionId;
    v___x_4081_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_4081_, 0, v___x_4080_);
    lean_ctor_set(v___x_4081_, 1, v___x_4079_);
    return v___x_4081_;
}
pub unsafe fn l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg()
-> *mut LeanObject {
    let mut v___x_4083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: *mut LeanObject = core::ptr::null_mut();
    v___x_4083_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg___closed__0);
    v___x_4084_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4084_, 0, v___x_4083_);
    return v___x_4084_;
}
pub unsafe fn l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg___boxed(
    mut v___y_4085_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4086_: *mut LeanObject = core::ptr::null_mut();
    v_res_4086_ =
        l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg();
    return v_res_4086_;
}
pub unsafe fn l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0(
    mut v_00_u03b1_4087_: *mut LeanObject,
    mut v___y_4088_: *mut LeanObject,
    mut v___y_4089_: *mut LeanObject,
    mut v___y_4090_: *mut LeanObject,
    mut v___y_4091_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4093_: *mut LeanObject = core::ptr::null_mut();
    v___x_4093_ =
        l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___redArg();
    return v___x_4093_;
}
pub unsafe fn l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0___boxed(
    mut v_00_u03b1_4094_: *mut LeanObject,
    mut v___y_4095_: *mut LeanObject,
    mut v___y_4096_: *mut LeanObject,
    mut v___y_4097_: *mut LeanObject,
    mut v___y_4098_: *mut LeanObject,
    mut v___y_4099_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4100_: *mut LeanObject = core::ptr::null_mut();
    v_res_4100_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_Term_throwCalcFailure_spec__0(
        v_00_u03b1_4094_,
        v___y_4095_,
        v___y_4096_,
        v___y_4097_,
        v___y_4098_,
    );
    lean_dec(v___y_4098_);
    lean_dec_ref(v___y_4097_);
    lean_dec(v___y_4096_);
    lean_dec_ref(v___y_4095_);
    return v_res_4100_;
}
pub unsafe fn l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2___redArg(
    mut v_msg_4101_: *mut LeanObject,
    mut v___y_4102_: *mut LeanObject,
    mut v___y_4103_: *mut LeanObject,
    mut v___y_4104_: *mut LeanObject,
    mut v___y_4105_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6547__overap_4108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: *mut LeanObject = core::ptr::null_mut();
    v___f_4107_ = l_panic___at___00Lean_Elab_Term_mkCalcTrans_spec__1___closed__0;
    v___x_6547__overap_4108_ = lean_panic_fn_borrowed(v___f_4107_, v_msg_4101_);
    lean_inc(v___y_4105_);
    lean_inc_ref(v___y_4104_);
    lean_inc(v___y_4103_);
    lean_inc_ref(v___y_4102_);
    v___x_4109_ = lean_apply_5(
        v___x_6547__overap_4108_,
        v___y_4102_,
        v___y_4103_,
        v___y_4104_,
        v___y_4105_,
        lean_box(0),
    );
    return v___x_4109_;
}
pub unsafe fn l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2___redArg___boxed(
    mut v_msg_4110_: *mut LeanObject,
    mut v___y_4111_: *mut LeanObject,
    mut v___y_4112_: *mut LeanObject,
    mut v___y_4113_: *mut LeanObject,
    mut v___y_4114_: *mut LeanObject,
    mut v___y_4115_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4116_: *mut LeanObject = core::ptr::null_mut();
    v_res_4116_ = l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2___redArg(
        v_msg_4110_,
        v___y_4111_,
        v___y_4112_,
        v___y_4113_,
        v___y_4114_,
    );
    lean_dec(v___y_4114_);
    lean_dec_ref(v___y_4113_);
    lean_dec(v___y_4112_);
    lean_dec_ref(v___y_4111_);
    return v_res_4116_;
}
pub unsafe fn l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2(
    mut v_00_u03b1_4117_: *mut LeanObject,
    mut v_msg_4118_: *mut LeanObject,
    mut v___y_4119_: *mut LeanObject,
    mut v___y_4120_: *mut LeanObject,
    mut v___y_4121_: *mut LeanObject,
    mut v___y_4122_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4124_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_4125_: *mut LeanObject,
    mut v_msg_4126_: *mut LeanObject,
    mut v___y_4127_: *mut LeanObject,
    mut v___y_4128_: *mut LeanObject,
    mut v___y_4129_: *mut LeanObject,
    mut v___y_4130_: *mut LeanObject,
    mut v___y_4131_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4132_: *mut LeanObject = core::ptr::null_mut();
    v_res_4132_ = l_panic___at___00Lean_Elab_Term_throwCalcFailure_spec__2(
        v_00_u03b1_4125_,
        v_msg_4126_,
        v___y_4127_,
        v___y_4128_,
        v___y_4129_,
        v___y_4130_,
    );
    lean_dec(v___y_4130_);
    lean_dec_ref(v___y_4129_);
    lean_dec(v___y_4128_);
    lean_dec_ref(v___y_4127_);
    return v_res_4132_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0(
    mut v___y_4140_: u8,
    mut v_suppressElabErrors_4141_: u8,
    mut v_x_4142_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_4142_) == 1 {
        let mut v_pre_4143_: *mut LeanObject = core::ptr::null_mut();
        v_pre_4143_ = lean_ctor_get(v_x_4142_, 0);
        match lean_obj_tag(v_pre_4143_) {
            1 => {
                let mut v_pre_4144_: *mut LeanObject = core::ptr::null_mut();
                v_pre_4144_ = lean_ctor_get(v_pre_4143_, 0);
                match lean_obj_tag(v_pre_4144_) {
                    0 => {
                        let mut v_str_4145_: *mut LeanObject = core::ptr::null_mut();
                        let mut v_str_4146_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_4147_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_4148_: u8 = 0;
                        v_str_4145_ = lean_ctor_get(v_x_4142_, 1);
                        v_str_4146_ = lean_ctor_get(v_pre_4143_, 1);
                        v___x_4147_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__13;
                        v___x_4148_ = lean_string_dec_eq(v_str_4146_, v___x_4147_);
                        if v___x_4148_ == 0 {
                            let mut v___x_4149_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_4150_: u8 = 0;
                            v___x_4149_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__0;
                            v___x_4150_ = lean_string_dec_eq(v_str_4146_, v___x_4149_);
                            if v___x_4150_ == 0 {
                                return v___y_4140_;
                            } else {
                                let mut v___x_4151_: *mut LeanObject = core::ptr::null_mut();
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
                            let mut v___x_4153_: *mut LeanObject = core::ptr::null_mut();
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
                        let mut v_pre_4155_: *mut LeanObject = core::ptr::null_mut();
                        v_pre_4155_ = lean_ctor_get(v_pre_4144_, 0);
                        if lean_obj_tag(v_pre_4155_) == 0 {
                            let mut v_str_4156_: *mut LeanObject = core::ptr::null_mut();
                            let mut v_str_4157_: *mut LeanObject = core::ptr::null_mut();
                            let mut v_str_4158_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_4159_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_4160_: u8 = 0;
                            v_str_4156_ = lean_ctor_get(v_x_4142_, 1);
                            v_str_4157_ = lean_ctor_get(v_pre_4143_, 1);
                            v_str_4158_ = lean_ctor_get(v_pre_4144_, 1);
                            v___x_4159_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__3;
                            v___x_4160_ = lean_string_dec_eq(v_str_4158_, v___x_4159_);
                            if v___x_4160_ == 0 {
                                return v___y_4140_;
                            } else {
                                let mut v___x_4161_: *mut LeanObject = core::ptr::null_mut();
                                let mut v___x_4162_: u8 = 0;
                                v___x_4161_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___closed__4;
                                v___x_4162_ = lean_string_dec_eq(v_str_4157_, v___x_4161_);
                                if v___x_4162_ == 0 {
                                    return v___y_4140_;
                                } else {
                                    let mut v___x_4163_: *mut LeanObject = core::ptr::null_mut();
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
                let mut v_str_4165_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4166_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4167_: u8 = 0;
                v_str_4165_ = lean_ctor_get(v_x_4142_, 1);
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
    mut v___y_4168_: *mut LeanObject,
    mut v_suppressElabErrors_4169_: *mut LeanObject,
    mut v_x_4170_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_8930__boxed_4171_: u8 = 0;
    let mut v_suppressElabErrors_boxed_4172_: u8 = 0;
    let mut v_res_4173_: u8 = 0;
    let mut v_r_4174_: *mut LeanObject = core::ptr::null_mut();
    v___y_8930__boxed_4171_ = (lean_unbox(v___y_4168_) as u8);
    v_suppressElabErrors_boxed_4172_ = (lean_unbox(v_suppressElabErrors_4169_) as u8);
    v_res_4173_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0(v___y_8930__boxed_4171_, v_suppressElabErrors_boxed_4172_, v_x_4170_);
    lean_dec(v_x_4170_);
    v_r_4174_ = lean_box((v_res_4173_) as usize);
    return v_r_4174_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1(
    mut v_ref_4175_: *mut LeanObject,
    mut v_msgData_4176_: *mut LeanObject,
    mut v_severity_4177_: u8,
    mut v_isSilent_4178_: u8,
    mut v___y_4179_: *mut LeanObject,
    mut v___y_4180_: *mut LeanObject,
    mut v___y_4181_: *mut LeanObject,
    mut v___y_4182_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4187_: u8 = 0;
    let mut v___y_4188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4189_: u8 = 0;
    let mut v___y_4190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_4199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_4201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_4202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_4203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_4204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4208_: u8 = 0;
    let mut v___x_4209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4219_: u8 = 0;
    let mut v___y_4221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4223_: u8 = 0;
    let mut v___y_4224_: u8 = 0;
    let mut v___y_4225_: u8 = 0;
    let mut v___y_4226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4234_: u8 = 0;
    let mut v___x_4235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: u8 = 0;
    let mut v___x_4240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4244_: u8 = 0;
    let mut v___y_4246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4248_: u8 = 0;
    let mut v___y_4249_: u8 = 0;
    let mut v___y_4250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4251_: u8 = 0;
    let mut v___y_4252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4259_: u8 = 0;
    let mut v___y_4260_: u8 = 0;
    let mut v___y_4261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4263_: u8 = 0;
    let mut v_ref_4264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: u8 = 0;
    let mut v___y_4270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4271_: u8 = 0;
    let mut v___y_4272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4275_: u8 = 0;
    let mut v___y_4276_: u8 = 0;
    let mut v___y_4278_: u8 = 0;
    let mut v_fileName_4279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4283_: u8 = 0;
    let mut v___x_4284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: u8 = 0;
    let mut v___x_4288_: u8 = 0;
    let mut v___x_4289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: u8 = 0;
    let mut v___x_4291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4292_: *mut LeanObject = core::ptr::null_mut();
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
                    lean_inc_ref(v_msgData_4176_);
                    v___x_4294_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_4176_);
                    v___y_4278_ = v___x_4294_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_4194_ = lean_st_ref_take(v___y_4193_);
                v_currNamespace_4195_ = lean_ctor_get(v___y_4192_, 6);
                v_openDecls_4196_ = lean_ctor_get(v___y_4192_, 7);
                v_env_4197_ = lean_ctor_get(v___x_4194_, 0);
                v_nextMacroScope_4198_ = lean_ctor_get(v___x_4194_, 1);
                v_ngen_4199_ = lean_ctor_get(v___x_4194_, 2);
                v_auxDeclNGen_4200_ = lean_ctor_get(v___x_4194_, 3);
                v_traceState_4201_ = lean_ctor_get(v___x_4194_, 4);
                v_cache_4202_ = lean_ctor_get(v___x_4194_, 5);
                v_messages_4203_ = lean_ctor_get(v___x_4194_, 6);
                v_infoState_4204_ = lean_ctor_get(v___x_4194_, 7);
                v_snapshotTasks_4205_ = lean_ctor_get(v___x_4194_, 8);
                v_isSharedCheck_4219_ = (!lean_is_exclusive(v___x_4194_)) as u8;
                if v_isSharedCheck_4219_ == 0 {
                    v___x_4207_ = v___x_4194_;
                    v_isShared_4208_ = v_isSharedCheck_4219_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_4205_);
                    lean_inc(v_infoState_4204_);
                    lean_inc(v_messages_4203_);
                    lean_inc(v_cache_4202_);
                    lean_inc(v_traceState_4201_);
                    lean_inc(v_auxDeclNGen_4200_);
                    lean_inc(v_ngen_4199_);
                    lean_inc(v_nextMacroScope_4198_);
                    lean_inc(v_env_4197_);
                    lean_dec(v___x_4194_);
                    v___x_4207_ = lean_box(0);
                    v_isShared_4208_ = v_isSharedCheck_4219_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc(v_openDecls_4196_);
                lean_inc(v_currNamespace_4195_);
                v___x_4209_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4209_, 0, v_currNamespace_4195_);
                lean_ctor_set(v___x_4209_, 1, v_openDecls_4196_);
                v___x_4210_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4210_, 0, v___x_4209_);
                lean_ctor_set(v___x_4210_, 1, v___y_4191_);
                lean_inc_ref(v___y_4186_);
                lean_inc_ref(v___y_4190_);
                v___x_4211_ = lean_alloc_ctor(0, 5, (3) as u32);
                lean_ctor_set(v___x_4211_, 0, v___y_4190_);
                lean_ctor_set(v___x_4211_, 1, v___y_4185_);
                lean_ctor_set(v___x_4211_, 2, v___y_4188_);
                lean_ctor_set(v___x_4211_, 3, v___y_4186_);
                lean_ctor_set(v___x_4211_, 4, v___x_4210_);
                lean_ctor_set_uint8(
                    v___x_4211_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    v___y_4187_,
                );
                lean_ctor_set_uint8(
                    v___x_4211_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                    v___y_4189_,
                );
                lean_ctor_set_uint8(
                    v___x_4211_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 2) as u32,
                    v_isSilent_4178_,
                );
                v___x_4212_ = l_Lean_MessageLog_add(v___x_4211_, v_messages_4203_);
                if v_isShared_4208_ == 0 {
                    lean_ctor_set(v___x_4207_, 6, v___x_4212_);
                    v___x_4214_ = v___x_4207_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4218_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4218_, 0, v_env_4197_);
                    lean_ctor_set(v_reuseFailAlloc_4218_, 1, v_nextMacroScope_4198_);
                    lean_ctor_set(v_reuseFailAlloc_4218_, 2, v_ngen_4199_);
                    lean_ctor_set(v_reuseFailAlloc_4218_, 3, v_auxDeclNGen_4200_);
                    lean_ctor_set(v_reuseFailAlloc_4218_, 4, v_traceState_4201_);
                    lean_ctor_set(v_reuseFailAlloc_4218_, 5, v_cache_4202_);
                    lean_ctor_set(v_reuseFailAlloc_4218_, 6, v___x_4212_);
                    lean_ctor_set(v_reuseFailAlloc_4218_, 7, v_infoState_4204_);
                    lean_ctor_set(v_reuseFailAlloc_4218_, 8, v_snapshotTasks_4205_);
                    v___x_4214_ = v_reuseFailAlloc_4218_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4215_ = lean_st_ref_set(v___y_4193_, v___x_4214_);
                v___x_4216_ = lean_box(0);
                v___x_4217_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4217_, 0, v___x_4216_);
                return v___x_4217_;
            }
            4 => {
                v___x_4229_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_4176_,
                    );
                v___x_4230_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv_spec__0_spec__0(v___x_4229_, v___y_4179_, v___y_4180_, v___y_4181_, v___y_4182_);
                v_a_4231_ = lean_ctor_get(v___x_4230_, 0);
                v_isSharedCheck_4244_ = (!lean_is_exclusive(v___x_4230_)) as u8;
                if v_isSharedCheck_4244_ == 0 {
                    v___x_4233_ = v___x_4230_;
                    v_isShared_4234_ = v_isSharedCheck_4244_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_a_4231_);
                    lean_dec(v___x_4230_);
                    v___x_4233_ = lean_box(0);
                    v_isShared_4234_ = v_isSharedCheck_4244_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                lean_inc_ref_n(v___y_4222_, 2);
                v___x_4235_ = l_Lean_FileMap_toPosition(v___y_4222_, v___y_4227_);
                lean_dec(v___y_4227_);
                v___x_4236_ = l_Lean_FileMap_toPosition(v___y_4222_, v___y_4228_);
                lean_dec(v___y_4228_);
                v___x_4237_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4237_, 0, v___x_4236_);
                v___x_4238_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_annotateFirstHoleWithType_go___closed__11;
                if v___y_4223_ == 0 {
                    lean_del_object(v___x_4233_);
                    lean_dec_ref(v___y_4221_);
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
                    lean_inc(v_a_4231_);
                    v___x_4239_ = l_Lean_MessageData_hasTag(v___y_4221_, v_a_4231_);
                    if v___x_4239_ == 0 {
                        lean_dec_ref_known(v___x_4237_, 1);
                        lean_dec_ref(v___x_4235_);
                        lean_dec(v_a_4231_);
                        v___x_4240_ = lean_box(0);
                        if v_isShared_4234_ == 0 {
                            lean_ctor_set(v___x_4233_, 0, v___x_4240_);
                            v___x_4242_ = v___x_4233_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_4243_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4243_, 0, v___x_4240_);
                            v___x_4242_ = v_reuseFailAlloc_4243_;
                            state = 6;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_4233_);
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
                lean_dec(v___y_4250_);
                if lean_obj_tag(v___x_4254_) == 0 {
                    lean_inc(v___y_4253_);
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
                    v_val_4255_ = lean_ctor_get(v___x_4254_, 0);
                    lean_inc(v_val_4255_);
                    lean_dec_ref_known(v___x_4254_, 1);
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
                if lean_obj_tag(v___x_4265_) == 0 {
                    v___x_4266_ = lean_unsigned_to_nat(0);
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
                    v_val_4267_ = lean_ctor_get(v___x_4265_, 0);
                    lean_inc(v_val_4267_);
                    lean_dec_ref_known(v___x_4265_, 1);
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
                    v_fileName_4279_ = lean_ctor_get(v___y_4181_, 0);
                    v_fileMap_4280_ = lean_ctor_get(v___y_4181_, 1);
                    v_options_4281_ = lean_ctor_get(v___y_4181_, 2);
                    v_ref_4282_ = lean_ctor_get(v___y_4181_, 5);
                    v_suppressElabErrors_4283_ = lean_ctor_get_uint8(
                        v___y_4181_,
                        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_4284_ = lean_box((v___y_4278_) as usize);
                    v___x_4285_ = lean_box((v_suppressElabErrors_4283_) as usize);
                    v___f_4286_ = lean_alloc_closure(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    lean_closure_set(v___f_4286_, 0, v___x_4284_);
                    lean_closure_set(v___f_4286_, 1, v___x_4285_);
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
                    lean_dec_ref(v_msgData_4176_);
                    v___x_4291_ = lean_box(0);
                    v___x_4292_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4292_, 0, v___x_4291_);
                    return v___x_4292_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1___boxed(
    mut v_ref_4295_: *mut LeanObject,
    mut v_msgData_4296_: *mut LeanObject,
    mut v_severity_4297_: *mut LeanObject,
    mut v_isSilent_4298_: *mut LeanObject,
    mut v___y_4299_: *mut LeanObject,
    mut v___y_4300_: *mut LeanObject,
    mut v___y_4301_: *mut LeanObject,
    mut v___y_4302_: *mut LeanObject,
    mut v___y_4303_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_4304_: u8 = 0;
    let mut v_isSilent_boxed_4305_: u8 = 0;
    let mut v_res_4306_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_4304_ = (lean_unbox(v_severity_4297_) as u8);
    v_isSilent_boxed_4305_ = (lean_unbox(v_isSilent_4298_) as u8);
    v_res_4306_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1(v_ref_4295_, v_msgData_4296_, v_severity_boxed_4304_, v_isSilent_boxed_4305_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_);
    lean_dec(v___y_4302_);
    lean_dec_ref(v___y_4301_);
    lean_dec(v___y_4300_);
    lean_dec_ref(v___y_4299_);
    lean_dec(v_ref_4295_);
    return v_res_4306_;
}
pub unsafe fn l_Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1(
    mut v_ref_4307_: *mut LeanObject,
    mut v_msgData_4308_: *mut LeanObject,
    mut v___y_4309_: *mut LeanObject,
    mut v___y_4310_: *mut LeanObject,
    mut v___y_4311_: *mut LeanObject,
    mut v___y_4312_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4314_: u8 = 0;
    let mut v___x_4315_: u8 = 0;
    let mut v___x_4316_: *mut LeanObject = core::ptr::null_mut();
    v___x_4314_ = 2;
    v___x_4315_ = 0;
    v___x_4316_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1_spec__1(v_ref_4307_, v_msgData_4308_, v___x_4314_, v___x_4315_, v___y_4309_, v___y_4310_, v___y_4311_, v___y_4312_);
    return v___x_4316_;
}
pub unsafe fn l_Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1___boxed(
    mut v_ref_4317_: *mut LeanObject,
    mut v_msgData_4318_: *mut LeanObject,
    mut v___y_4319_: *mut LeanObject,
    mut v___y_4320_: *mut LeanObject,
    mut v___y_4321_: *mut LeanObject,
    mut v___y_4322_: *mut LeanObject,
    mut v___y_4323_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4324_: *mut LeanObject = core::ptr::null_mut();
    v_res_4324_ = l_Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1(
        v_ref_4317_,
        v_msgData_4318_,
        v___y_4319_,
        v___y_4320_,
        v___y_4321_,
        v___y_4322_,
    );
    lean_dec(v___y_4322_);
    lean_dec_ref(v___y_4321_);
    lean_dec(v___y_4320_);
    lean_dec_ref(v___y_4319_);
    lean_dec(v_ref_4317_);
    return v_res_4324_;
}
pub unsafe fn _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__2() -> *mut LeanObject {
    let mut v___x_4328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: *mut LeanObject = core::ptr::null_mut();
    v___x_4328_ = l_Lean_Elab_Term_throwCalcFailure___redArg___closed__1;
    v___x_4329_ = l_Lean_MessageData_ofFormat(v___x_4328_);
    return v___x_4329_;
}
pub unsafe fn _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__3() -> *mut LeanObject {
    let mut v___x_4330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4331_: *mut LeanObject = core::ptr::null_mut();
    v___x_4330_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Term_throwCalcFailure___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_Term_throwCalcFailure___redArg___closed__2_once),
        _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__2,
    );
    v___x_4331_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4331_, 0, v___x_4330_);
    return v___x_4331_;
}
pub unsafe fn _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__5() -> *mut LeanObject {
    let mut v___x_4333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut LeanObject = core::ptr::null_mut();
    v___x_4333_ = l_Lean_Elab_Term_throwCalcFailure___redArg___closed__4;
    v___x_4334_ = l_Lean_stringToMessageData(v___x_4333_);
    return v___x_4334_;
}
pub unsafe fn _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__7() -> *mut LeanObject {
    let mut v___x_4336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4337_: *mut LeanObject = core::ptr::null_mut();
    v___x_4336_ = l_Lean_Elab_Term_throwCalcFailure___redArg___closed__6;
    v___x_4337_ = l_Lean_stringToMessageData(v___x_4336_);
    return v___x_4337_;
}
pub unsafe fn _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__9() -> *mut LeanObject {
    let mut v___x_4339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4344_: *mut LeanObject = core::ptr::null_mut();
    v___x_4339_ = l_Lean_Elab_Term_mkCalcTrans___closed__10;
    v___x_4340_ = lean_unsigned_to_nat(57);
    v___x_4341_ = lean_unsigned_to_nat(133);
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
    mut v_steps_4345_: *mut LeanObject,
    mut v_expectedType_4346_: *mut LeanObject,
    mut v_result_4347_: *mut LeanObject,
    mut v_a_4348_: *mut LeanObject,
    mut v_a_4349_: *mut LeanObject,
    mut v_a_4350_: *mut LeanObject,
    mut v_a_4351_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4375_: u8 = 0;
    let mut v___x_4377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4379_: u8 = 0;
    let mut v___x_4380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4387_: u8 = 0;
    let mut v_fst_4388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4392_: u8 = 0;
    let mut v___x_4393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4400_: u8 = 0;
    let mut v_fst_4401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4405_: u8 = 0;
    let mut v_failed_4407_: u8 = 0;
    let mut v___y_4408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: u8 = 0;
    let mut v___x_4415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4421_: u8 = 0;
    let mut v___x_4422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4432_: u8 = 0;
    let mut v___x_4433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_term_4438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4465_: u8 = 0;
    let mut v___x_4467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4469_: u8 = 0;
    let mut v_reuseFailAlloc_4470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4476_: u8 = 0;
    let mut v_a_4477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4480_: u8 = 0;
    let mut v___x_4482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4484_: u8 = 0;
    let mut v_a_4485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4488_: u8 = 0;
    let mut v___x_4490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4492_: u8 = 0;
    let mut v_a_4493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4496_: u8 = 0;
    let mut v___x_4498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4500_: u8 = 0;
    let mut v_isSharedCheck_4501_: u8 = 0;
    let mut v_a_4502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4505_: u8 = 0;
    let mut v___x_4507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4509_: u8 = 0;
    let mut v_a_4510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4513_: u8 = 0;
    let mut v___x_4515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4517_: u8 = 0;
    let mut v___x_4518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4520_: u8 = 0;
    let mut v___x_4521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4523_: u8 = 0;
    let mut v___x_4524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4530_: u8 = 0;
    let mut v___x_4531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4541_: u8 = 0;
    let mut v___x_4542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_term_4545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: u8 = 0;
    let mut v_a_4566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4569_: u8 = 0;
    let mut v___x_4571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4573_: u8 = 0;
    let mut v_reuseFailAlloc_4574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4576_: u8 = 0;
    let mut v_a_4577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4580_: u8 = 0;
    let mut v___x_4582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4584_: u8 = 0;
    let mut v_a_4585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4588_: u8 = 0;
    let mut v___x_4590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4592_: u8 = 0;
    let mut v_a_4593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4596_: u8 = 0;
    let mut v___x_4598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4600_: u8 = 0;
    let mut v_isSharedCheck_4601_: u8 = 0;
    let mut v_a_4602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4605_: u8 = 0;
    let mut v___x_4607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4609_: u8 = 0;
    let mut v___x_4610_: u8 = 0;
    let mut v_a_4611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4614_: u8 = 0;
    let mut v___x_4616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4618_: u8 = 0;
    let mut v_a_4619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4622_: u8 = 0;
    let mut v___x_4624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4626_: u8 = 0;
    let mut v_isSharedCheck_4627_: u8 = 0;
    let mut v_isSharedCheck_4628_: u8 = 0;
    let mut v_isSharedCheck_4629_: u8 = 0;
    let mut v_isSharedCheck_4630_: u8 = 0;
    let mut v___x_4631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4636_: u8 = 0;
    let mut v___x_4638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4640_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_a_4351_);
                lean_inc_ref(v_a_4350_);
                lean_inc(v_a_4349_);
                lean_inc_ref(v_a_4348_);
                lean_inc_ref(v_result_4347_);
                v___x_4353_ =
                    lean_infer_type(v_result_4347_, v_a_4348_, v_a_4349_, v_a_4350_, v_a_4351_);
                if lean_obj_tag(v___x_4353_) == 0 {
                    v_a_4354_ = lean_ctor_get(v___x_4353_, 0);
                    lean_inc(v_a_4354_);
                    lean_dec_ref_known(v___x_4353_, 1);
                    v___x_4355_ = l_Lean_instantiateMVars___at___00Lean_Elab_Term_mkCalcTrans_spec__0___redArg(v_a_4354_, v_a_4349_);
                    v_a_4356_ = lean_ctor_get(v___x_4355_, 0);
                    lean_inc(v_a_4356_);
                    lean_dec_ref(v___x_4355_);
                    v___x_4357_ = l_Lean_Expr_headBeta(v_a_4356_);
                    v___x_4380_ = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(v___x_4357_);
                    v_a_4381_ = lean_ctor_get(v___x_4380_, 0);
                    lean_inc(v_a_4381_);
                    lean_dec_ref(v___x_4380_);
                    if lean_obj_tag(v_a_4381_) == 1 {
                        v_val_4382_ = lean_ctor_get(v_a_4381_, 0);
                        lean_inc(v_val_4382_);
                        lean_dec_ref_known(v_a_4381_, 1);
                        v_snd_4383_ = lean_ctor_get(v_val_4382_, 1);
                        v_fst_4384_ = lean_ctor_get(v_val_4382_, 0);
                        v_isSharedCheck_4630_ = (!lean_is_exclusive(v_val_4382_)) as u8;
                        if v_isSharedCheck_4630_ == 0 {
                            v___x_4386_ = v_val_4382_;
                            v_isShared_4387_ = v_isSharedCheck_4630_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_snd_4383_);
                            lean_inc(v_fst_4384_);
                            lean_dec(v_val_4382_);
                            v___x_4386_ = lean_box(0);
                            v_isShared_4387_ = v_isSharedCheck_4630_;
                            state = 5;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_4381_);
                        lean_dec_ref(v___x_4357_);
                        lean_dec_ref(v_result_4347_);
                        lean_dec_ref(v_expectedType_4346_);
                        v___x_4631_ = lean_obj_once(
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
                    lean_dec_ref(v_result_4347_);
                    lean_dec_ref(v_expectedType_4346_);
                    v_a_4633_ = lean_ctor_get(v___x_4353_, 0);
                    v_isSharedCheck_4640_ = (!lean_is_exclusive(v___x_4353_)) as u8;
                    if v_isSharedCheck_4640_ == 0 {
                        v___x_4635_ = v___x_4353_;
                        v_isShared_4636_ = v_isSharedCheck_4640_;
                        state = 48;
                        continue;
                    } else {
                        lean_inc(v_a_4633_);
                        lean_dec(v___x_4353_);
                        v___x_4635_ = lean_box(0);
                        v_isShared_4636_ = v_isSharedCheck_4640_;
                        state = 48;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4363_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Term_throwCalcFailure___redArg___closed__3),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Term_throwCalcFailure___redArg___closed__3_once
                    ),
                    _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__3,
                );
                v___x_4364_ = lean_box(0);
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
                v_a_4372_ = lean_ctor_get(v___x_4371_, 0);
                v_isSharedCheck_4379_ = (!lean_is_exclusive(v___x_4371_)) as u8;
                if v_isSharedCheck_4379_ == 0 {
                    v___x_4374_ = v___x_4371_;
                    v_isShared_4375_ = v_isSharedCheck_4379_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_a_4372_);
                    lean_dec(v___x_4371_);
                    v___x_4374_ = lean_box(0);
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
                    v_reuseFailAlloc_4378_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4378_, 0, v_a_4372_);
                    v___x_4377_ = v_reuseFailAlloc_4378_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4377_;
            }
            5 => {
                v_fst_4388_ = lean_ctor_get(v_snd_4383_, 0);
                v_snd_4389_ = lean_ctor_get(v_snd_4383_, 1);
                v_isSharedCheck_4629_ = (!lean_is_exclusive(v_snd_4383_)) as u8;
                if v_isSharedCheck_4629_ == 0 {
                    v___x_4391_ = v_snd_4383_;
                    v_isShared_4392_ = v_isSharedCheck_4629_;
                    state = 6;
                    continue;
                } else {
                    lean_inc(v_snd_4389_);
                    lean_inc(v_fst_4388_);
                    lean_dec(v_snd_4383_);
                    v___x_4391_ = lean_box(0);
                    v_isShared_4392_ = v_isSharedCheck_4629_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_4393_ = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(v_expectedType_4346_);
                v_a_4394_ = lean_ctor_get(v___x_4393_, 0);
                lean_inc(v_a_4394_);
                lean_dec_ref(v___x_4393_);
                if lean_obj_tag(v_a_4394_) == 1 {
                    v_val_4395_ = lean_ctor_get(v_a_4394_, 0);
                    lean_inc(v_val_4395_);
                    lean_dec_ref_known(v_a_4394_, 1);
                    v_snd_4396_ = lean_ctor_get(v_val_4395_, 1);
                    v_fst_4397_ = lean_ctor_get(v_val_4395_, 0);
                    v_isSharedCheck_4628_ = (!lean_is_exclusive(v_val_4395_)) as u8;
                    if v_isSharedCheck_4628_ == 0 {
                        v___x_4399_ = v_val_4395_;
                        v_isShared_4400_ = v_isSharedCheck_4628_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_snd_4396_);
                        lean_inc(v_fst_4397_);
                        lean_dec(v_val_4395_);
                        v___x_4399_ = lean_box(0);
                        v_isShared_4400_ = v_isSharedCheck_4628_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_dec(v_a_4394_);
                    lean_del_object(v___x_4391_);
                    lean_dec(v_snd_4389_);
                    lean_dec(v_fst_4388_);
                    lean_del_object(v___x_4386_);
                    lean_dec(v_fst_4384_);
                    v___y_4359_ = v_a_4348_;
                    v___y_4360_ = v_a_4349_;
                    v___y_4361_ = v_a_4350_;
                    v___y_4362_ = v_a_4351_;
                    state = 1;
                    continue;
                }
            }
            7 => {
                v_fst_4401_ = lean_ctor_get(v_snd_4396_, 0);
                v_snd_4402_ = lean_ctor_get(v_snd_4396_, 1);
                v_isSharedCheck_4627_ = (!lean_is_exclusive(v_snd_4396_)) as u8;
                if v_isSharedCheck_4627_ == 0 {
                    v___x_4404_ = v_snd_4396_;
                    v_isShared_4405_ = v_isSharedCheck_4627_;
                    state = 8;
                    continue;
                } else {
                    lean_inc(v_snd_4402_);
                    lean_inc(v_fst_4401_);
                    lean_dec(v_snd_4396_);
                    v___x_4404_ = lean_box(0);
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
                if lean_obj_tag(v___x_4518_) == 0 {
                    v_a_4519_ = lean_ctor_get(v___x_4518_, 0);
                    lean_inc(v_a_4519_);
                    lean_dec_ref_known(v___x_4518_, 1);
                    v___x_4520_ = (lean_unbox(v_a_4519_) as u8);
                    if v___x_4520_ == 0 {
                        lean_dec(v_a_4519_);
                        lean_del_object(v___x_4404_);
                        lean_dec(v_snd_4402_);
                        lean_dec(v_fst_4401_);
                        lean_del_object(v___x_4399_);
                        lean_del_object(v___x_4391_);
                        lean_dec(v_snd_4389_);
                        lean_dec(v_fst_4388_);
                        lean_del_object(v___x_4386_);
                        v___y_4359_ = v_a_4348_;
                        v___y_4360_ = v_a_4349_;
                        v___y_4361_ = v_a_4350_;
                        v___y_4362_ = v_a_4351_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_fst_4401_);
                        lean_inc(v_fst_4388_);
                        v___x_4521_ = l_Lean_Meta_isExprDefEqGuarded(
                            v_fst_4388_,
                            v_fst_4401_,
                            v_a_4348_,
                            v_a_4349_,
                            v_a_4350_,
                            v_a_4351_,
                        );
                        if lean_obj_tag(v___x_4521_) == 0 {
                            v_a_4522_ = lean_ctor_get(v___x_4521_, 0);
                            lean_inc(v_a_4522_);
                            lean_dec_ref_known(v___x_4521_, 1);
                            v___x_4523_ = (lean_unbox(v_a_4522_) as u8);
                            lean_dec(v_a_4522_);
                            if v___x_4523_ == 0 {
                                v___x_4524_ = l_Lean_Meta_addPPExplicitToExposeDiff(
                                    v_fst_4388_,
                                    v_fst_4401_,
                                    v_a_4348_,
                                    v_a_4349_,
                                    v_a_4350_,
                                    v_a_4351_,
                                );
                                if lean_obj_tag(v___x_4524_) == 0 {
                                    v_a_4525_ = lean_ctor_get(v___x_4524_, 0);
                                    lean_inc(v_a_4525_);
                                    lean_dec_ref_known(v___x_4524_, 1);
                                    v_fst_4526_ = lean_ctor_get(v_a_4525_, 0);
                                    v_snd_4527_ = lean_ctor_get(v_a_4525_, 1);
                                    v_isSharedCheck_4601_ = (!lean_is_exclusive(v_a_4525_)) as u8;
                                    if v_isSharedCheck_4601_ == 0 {
                                        v___x_4529_ = v_a_4525_;
                                        v_isShared_4530_ = v_isSharedCheck_4601_;
                                        state = 30;
                                        continue;
                                    } else {
                                        lean_inc(v_snd_4527_);
                                        lean_inc(v_fst_4526_);
                                        lean_dec(v_a_4525_);
                                        v___x_4529_ = lean_box(0);
                                        v_isShared_4530_ = v_isSharedCheck_4601_;
                                        state = 30;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_a_4519_);
                                    lean_del_object(v___x_4404_);
                                    lean_dec(v_snd_4402_);
                                    lean_del_object(v___x_4399_);
                                    lean_del_object(v___x_4391_);
                                    lean_dec(v_snd_4389_);
                                    lean_del_object(v___x_4386_);
                                    lean_dec_ref(v___x_4357_);
                                    lean_dec_ref(v_result_4347_);
                                    lean_dec_ref(v_expectedType_4346_);
                                    v_a_4602_ = lean_ctor_get(v___x_4524_, 0);
                                    v_isSharedCheck_4609_ = (!lean_is_exclusive(v___x_4524_)) as u8;
                                    if v_isSharedCheck_4609_ == 0 {
                                        v___x_4604_ = v___x_4524_;
                                        v_isShared_4605_ = v_isSharedCheck_4609_;
                                        state = 42;
                                        continue;
                                    } else {
                                        lean_inc(v_a_4602_);
                                        lean_dec(v___x_4524_);
                                        v___x_4604_ = lean_box(0);
                                        v_isShared_4605_ = v_isSharedCheck_4609_;
                                        state = 42;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_a_4519_);
                                lean_dec(v_fst_4401_);
                                lean_dec(v_fst_4388_);
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
                            lean_dec(v_a_4519_);
                            lean_del_object(v___x_4404_);
                            lean_dec(v_snd_4402_);
                            lean_dec(v_fst_4401_);
                            lean_del_object(v___x_4399_);
                            lean_del_object(v___x_4391_);
                            lean_dec(v_snd_4389_);
                            lean_dec(v_fst_4388_);
                            lean_del_object(v___x_4386_);
                            lean_dec_ref(v___x_4357_);
                            lean_dec_ref(v_result_4347_);
                            lean_dec_ref(v_expectedType_4346_);
                            v_a_4611_ = lean_ctor_get(v___x_4521_, 0);
                            v_isSharedCheck_4618_ = (!lean_is_exclusive(v___x_4521_)) as u8;
                            if v_isSharedCheck_4618_ == 0 {
                                v___x_4613_ = v___x_4521_;
                                v_isShared_4614_ = v_isSharedCheck_4618_;
                                state = 44;
                                continue;
                            } else {
                                lean_inc(v_a_4611_);
                                lean_dec(v___x_4521_);
                                v___x_4613_ = lean_box(0);
                                v_isShared_4614_ = v_isSharedCheck_4618_;
                                state = 44;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_del_object(v___x_4404_);
                    lean_dec(v_snd_4402_);
                    lean_dec(v_fst_4401_);
                    lean_del_object(v___x_4399_);
                    lean_del_object(v___x_4391_);
                    lean_dec(v_snd_4389_);
                    lean_dec(v_fst_4388_);
                    lean_del_object(v___x_4386_);
                    lean_dec_ref(v___x_4357_);
                    lean_dec_ref(v_result_4347_);
                    lean_dec_ref(v_expectedType_4346_);
                    v_a_4619_ = lean_ctor_get(v___x_4518_, 0);
                    v_isSharedCheck_4626_ = (!lean_is_exclusive(v___x_4518_)) as u8;
                    if v_isSharedCheck_4626_ == 0 {
                        v___x_4621_ = v___x_4518_;
                        v_isShared_4622_ = v_isSharedCheck_4626_;
                        state = 46;
                        continue;
                    } else {
                        lean_inc(v_a_4619_);
                        lean_dec(v___x_4518_);
                        v___x_4621_ = lean_box(0);
                        v_isShared_4622_ = v_isSharedCheck_4626_;
                        state = 46;
                        continue;
                    }
                }
            }
            9 => {
                lean_inc(v_snd_4402_);
                lean_inc(v_snd_4389_);
                v___x_4412_ = l_Lean_Meta_isExprDefEqGuarded(
                    v_snd_4389_,
                    v_snd_4402_,
                    v___y_4408_,
                    v___y_4409_,
                    v___y_4410_,
                    v___y_4411_,
                );
                if lean_obj_tag(v___x_4412_) == 0 {
                    v_a_4413_ = lean_ctor_get(v___x_4412_, 0);
                    lean_inc(v_a_4413_);
                    lean_dec_ref_known(v___x_4412_, 1);
                    v___x_4414_ = (lean_unbox(v_a_4413_) as u8);
                    lean_dec(v_a_4413_);
                    if v___x_4414_ == 0 {
                        lean_dec_ref(v___x_4357_);
                        lean_dec_ref(v_result_4347_);
                        lean_dec_ref(v_expectedType_4346_);
                        v___x_4415_ = l_Lean_Meta_addPPExplicitToExposeDiff(
                            v_snd_4389_,
                            v_snd_4402_,
                            v___y_4408_,
                            v___y_4409_,
                            v___y_4410_,
                            v___y_4411_,
                        );
                        if lean_obj_tag(v___x_4415_) == 0 {
                            v_a_4416_ = lean_ctor_get(v___x_4415_, 0);
                            lean_inc(v_a_4416_);
                            lean_dec_ref_known(v___x_4415_, 1);
                            v_fst_4417_ = lean_ctor_get(v_a_4416_, 0);
                            v_snd_4418_ = lean_ctor_get(v_a_4416_, 1);
                            v_isSharedCheck_4501_ = (!lean_is_exclusive(v_a_4416_)) as u8;
                            if v_isSharedCheck_4501_ == 0 {
                                v___x_4420_ = v_a_4416_;
                                v_isShared_4421_ = v_isSharedCheck_4501_;
                                state = 10;
                                continue;
                            } else {
                                lean_inc(v_snd_4418_);
                                lean_inc(v_fst_4417_);
                                lean_dec(v_a_4416_);
                                v___x_4420_ = lean_box(0);
                                v_isShared_4421_ = v_isSharedCheck_4501_;
                                state = 10;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_4404_);
                            lean_del_object(v___x_4399_);
                            lean_del_object(v___x_4391_);
                            lean_del_object(v___x_4386_);
                            v_a_4502_ = lean_ctor_get(v___x_4415_, 0);
                            v_isSharedCheck_4509_ = (!lean_is_exclusive(v___x_4415_)) as u8;
                            if v_isSharedCheck_4509_ == 0 {
                                v___x_4504_ = v___x_4415_;
                                v_isShared_4505_ = v_isSharedCheck_4509_;
                                state = 26;
                                continue;
                            } else {
                                lean_inc(v_a_4502_);
                                lean_dec(v___x_4415_);
                                v___x_4504_ = lean_box(0);
                                v_isShared_4505_ = v_isSharedCheck_4509_;
                                state = 26;
                                continue;
                            }
                        }
                    } else {
                        lean_del_object(v___x_4404_);
                        lean_dec(v_snd_4402_);
                        lean_del_object(v___x_4399_);
                        lean_del_object(v___x_4391_);
                        lean_dec(v_snd_4389_);
                        lean_del_object(v___x_4386_);
                        if v_failed_4407_ == 0 {
                            v___y_4359_ = v___y_4408_;
                            v___y_4360_ = v___y_4409_;
                            v___y_4361_ = v___y_4410_;
                            v___y_4362_ = v___y_4411_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec_ref(v___x_4357_);
                            lean_dec_ref(v_result_4347_);
                            lean_dec_ref(v_expectedType_4346_);
                            v___y_4367_ = v___y_4408_;
                            v___y_4368_ = v___y_4409_;
                            v___y_4369_ = v___y_4410_;
                            v___y_4370_ = v___y_4411_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_4404_);
                    lean_dec(v_snd_4402_);
                    lean_del_object(v___x_4399_);
                    lean_del_object(v___x_4391_);
                    lean_dec(v_snd_4389_);
                    lean_del_object(v___x_4386_);
                    lean_dec_ref(v___x_4357_);
                    lean_dec_ref(v_result_4347_);
                    lean_dec_ref(v_expectedType_4346_);
                    v_a_4510_ = lean_ctor_get(v___x_4412_, 0);
                    v_isSharedCheck_4517_ = (!lean_is_exclusive(v___x_4412_)) as u8;
                    if v_isSharedCheck_4517_ == 0 {
                        v___x_4512_ = v___x_4412_;
                        v_isShared_4513_ = v_isSharedCheck_4517_;
                        state = 28;
                        continue;
                    } else {
                        lean_inc(v_a_4510_);
                        lean_dec(v___x_4412_);
                        v___x_4512_ = lean_box(0);
                        v_isShared_4513_ = v_isSharedCheck_4517_;
                        state = 28;
                        continue;
                    }
                }
            }
            10 => {
                lean_inc(v___y_4411_);
                lean_inc_ref(v___y_4410_);
                lean_inc(v___y_4409_);
                lean_inc_ref(v___y_4408_);
                lean_inc(v_fst_4417_);
                v___x_4422_ = lean_infer_type(
                    v_fst_4417_,
                    v___y_4408_,
                    v___y_4409_,
                    v___y_4410_,
                    v___y_4411_,
                );
                if lean_obj_tag(v___x_4422_) == 0 {
                    v_a_4423_ = lean_ctor_get(v___x_4422_, 0);
                    lean_inc(v_a_4423_);
                    lean_dec_ref_known(v___x_4422_, 1);
                    lean_inc(v___y_4411_);
                    lean_inc_ref(v___y_4410_);
                    lean_inc(v___y_4409_);
                    lean_inc_ref(v___y_4408_);
                    lean_inc(v_snd_4418_);
                    v___x_4424_ = lean_infer_type(
                        v_snd_4418_,
                        v___y_4408_,
                        v___y_4409_,
                        v___y_4410_,
                        v___y_4411_,
                    );
                    if lean_obj_tag(v___x_4424_) == 0 {
                        v_a_4425_ = lean_ctor_get(v___x_4424_, 0);
                        lean_inc(v_a_4425_);
                        lean_dec_ref_known(v___x_4424_, 1);
                        v___x_4426_ = l_Lean_Meta_addPPExplicitToExposeDiff(
                            v_a_4423_,
                            v_a_4425_,
                            v___y_4408_,
                            v___y_4409_,
                            v___y_4410_,
                            v___y_4411_,
                        );
                        if lean_obj_tag(v___x_4426_) == 0 {
                            v_a_4427_ = lean_ctor_get(v___x_4426_, 0);
                            lean_inc(v_a_4427_);
                            lean_dec_ref_known(v___x_4426_, 1);
                            v_fst_4428_ = lean_ctor_get(v_a_4427_, 0);
                            v_snd_4429_ = lean_ctor_get(v_a_4427_, 1);
                            v_isSharedCheck_4476_ = (!lean_is_exclusive(v_a_4427_)) as u8;
                            if v_isSharedCheck_4476_ == 0 {
                                v___x_4431_ = v_a_4427_;
                                v_isShared_4432_ = v_isSharedCheck_4476_;
                                state = 11;
                                continue;
                            } else {
                                lean_inc(v_snd_4429_);
                                lean_inc(v_fst_4428_);
                                lean_dec(v_a_4427_);
                                v___x_4431_ = lean_box(0);
                                v_isShared_4432_ = v_isSharedCheck_4476_;
                                state = 11;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_4420_);
                            lean_dec(v_snd_4418_);
                            lean_dec(v_fst_4417_);
                            lean_del_object(v___x_4404_);
                            lean_del_object(v___x_4399_);
                            lean_del_object(v___x_4391_);
                            lean_del_object(v___x_4386_);
                            v_a_4477_ = lean_ctor_get(v___x_4426_, 0);
                            v_isSharedCheck_4484_ = (!lean_is_exclusive(v___x_4426_)) as u8;
                            if v_isSharedCheck_4484_ == 0 {
                                v___x_4479_ = v___x_4426_;
                                v_isShared_4480_ = v_isSharedCheck_4484_;
                                state = 20;
                                continue;
                            } else {
                                lean_inc(v_a_4477_);
                                lean_dec(v___x_4426_);
                                v___x_4479_ = lean_box(0);
                                v_isShared_4480_ = v_isSharedCheck_4484_;
                                state = 20;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_4423_);
                        lean_del_object(v___x_4420_);
                        lean_dec(v_snd_4418_);
                        lean_dec(v_fst_4417_);
                        lean_del_object(v___x_4404_);
                        lean_del_object(v___x_4399_);
                        lean_del_object(v___x_4391_);
                        lean_del_object(v___x_4386_);
                        v_a_4485_ = lean_ctor_get(v___x_4424_, 0);
                        v_isSharedCheck_4492_ = (!lean_is_exclusive(v___x_4424_)) as u8;
                        if v_isSharedCheck_4492_ == 0 {
                            v___x_4487_ = v___x_4424_;
                            v_isShared_4488_ = v_isSharedCheck_4492_;
                            state = 22;
                            continue;
                        } else {
                            lean_inc(v_a_4485_);
                            lean_dec(v___x_4424_);
                            v___x_4487_ = lean_box(0);
                            v_isShared_4488_ = v_isSharedCheck_4492_;
                            state = 22;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_4420_);
                    lean_dec(v_snd_4418_);
                    lean_dec(v_fst_4417_);
                    lean_del_object(v___x_4404_);
                    lean_del_object(v___x_4399_);
                    lean_del_object(v___x_4391_);
                    lean_del_object(v___x_4386_);
                    v_a_4493_ = lean_ctor_get(v___x_4422_, 0);
                    v_isSharedCheck_4500_ = (!lean_is_exclusive(v___x_4422_)) as u8;
                    if v_isSharedCheck_4500_ == 0 {
                        v___x_4495_ = v___x_4422_;
                        v_isShared_4496_ = v_isSharedCheck_4500_;
                        state = 24;
                        continue;
                    } else {
                        lean_inc(v_a_4493_);
                        lean_dec(v___x_4422_);
                        v___x_4495_ = lean_box(0);
                        v_isShared_4496_ = v_isSharedCheck_4500_;
                        state = 24;
                        continue;
                    }
                }
            }
            11 => {
                v___x_4433_ = l_Lean_Elab_Term_instInhabitedCalcStepView_default;
                v___x_4434_ = lean_array_get_size(v_steps_4345_);
                v___x_4435_ = lean_unsigned_to_nat(1);
                v___x_4436_ = lean_nat_sub(v___x_4434_, v___x_4435_);
                v___x_4437_ = lean_array_get_borrowed(v___x_4433_, v_steps_4345_, v___x_4436_);
                lean_dec(v___x_4436_);
                v_term_4438_ = lean_ctor_get(v___x_4437_, 1);
                v___x_4439_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Term_throwCalcFailure___redArg___closed__5),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Term_throwCalcFailure___redArg___closed__5_once
                    ),
                    _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__5,
                );
                v___x_4440_ = l_Lean_MessageData_ofExpr(v_fst_4417_);
                v___x_4441_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3);
                if v_isShared_4432_ == 0 {
                    lean_ctor_set_tag(v___x_4431_, 7);
                    lean_ctor_set(v___x_4431_, 1, v___x_4441_);
                    lean_ctor_set(v___x_4431_, 0, v___x_4440_);
                    v___x_4443_ = v___x_4431_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4475_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4475_, 0, v___x_4440_);
                    lean_ctor_set(v_reuseFailAlloc_4475_, 1, v___x_4441_);
                    v___x_4443_ = v_reuseFailAlloc_4475_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_4444_ = l_Lean_MessageData_ofExpr(v_fst_4428_);
                if v_isShared_4421_ == 0 {
                    lean_ctor_set_tag(v___x_4420_, 7);
                    lean_ctor_set(v___x_4420_, 1, v___x_4444_);
                    lean_ctor_set(v___x_4420_, 0, v___x_4443_);
                    v___x_4446_ = v___x_4420_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4474_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4474_, 0, v___x_4443_);
                    lean_ctor_set(v_reuseFailAlloc_4474_, 1, v___x_4444_);
                    v___x_4446_ = v_reuseFailAlloc_4474_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_4447_ = l_Lean_indentD(v___x_4446_);
                if v_isShared_4405_ == 0 {
                    lean_ctor_set_tag(v___x_4404_, 7);
                    lean_ctor_set(v___x_4404_, 1, v___x_4447_);
                    lean_ctor_set(v___x_4404_, 0, v___x_4439_);
                    v___x_4449_ = v___x_4404_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4473_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4473_, 0, v___x_4439_);
                    lean_ctor_set(v_reuseFailAlloc_4473_, 1, v___x_4447_);
                    v___x_4449_ = v_reuseFailAlloc_4473_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_4450_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Term_throwCalcFailure___redArg___closed__7),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Term_throwCalcFailure___redArg___closed__7_once
                    ),
                    _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__7,
                );
                if v_isShared_4400_ == 0 {
                    lean_ctor_set_tag(v___x_4399_, 7);
                    lean_ctor_set(v___x_4399_, 1, v___x_4450_);
                    lean_ctor_set(v___x_4399_, 0, v___x_4449_);
                    v___x_4452_ = v___x_4399_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4472_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4472_, 0, v___x_4449_);
                    lean_ctor_set(v_reuseFailAlloc_4472_, 1, v___x_4450_);
                    v___x_4452_ = v_reuseFailAlloc_4472_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___x_4453_ = l_Lean_MessageData_ofExpr(v_snd_4418_);
                if v_isShared_4392_ == 0 {
                    lean_ctor_set_tag(v___x_4391_, 7);
                    lean_ctor_set(v___x_4391_, 1, v___x_4441_);
                    lean_ctor_set(v___x_4391_, 0, v___x_4453_);
                    v___x_4455_ = v___x_4391_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4471_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4471_, 0, v___x_4453_);
                    lean_ctor_set(v_reuseFailAlloc_4471_, 1, v___x_4441_);
                    v___x_4455_ = v_reuseFailAlloc_4471_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___x_4456_ = l_Lean_MessageData_ofExpr(v_snd_4429_);
                if v_isShared_4387_ == 0 {
                    lean_ctor_set_tag(v___x_4386_, 7);
                    lean_ctor_set(v___x_4386_, 1, v___x_4456_);
                    lean_ctor_set(v___x_4386_, 0, v___x_4455_);
                    v___x_4458_ = v___x_4386_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_4470_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4470_, 0, v___x_4455_);
                    lean_ctor_set(v_reuseFailAlloc_4470_, 1, v___x_4456_);
                    v___x_4458_ = v_reuseFailAlloc_4470_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_4459_ = l_Lean_indentD(v___x_4458_);
                v___x_4460_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4460_, 0, v___x_4452_);
                lean_ctor_set(v___x_4460_, 1, v___x_4459_);
                v___x_4461_ = l_Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1(
                    v_term_4438_,
                    v___x_4460_,
                    v___y_4408_,
                    v___y_4409_,
                    v___y_4410_,
                    v___y_4411_,
                );
                if lean_obj_tag(v___x_4461_) == 0 {
                    lean_dec_ref_known(v___x_4461_, 1);
                    v___y_4367_ = v___y_4408_;
                    v___y_4368_ = v___y_4409_;
                    v___y_4369_ = v___y_4410_;
                    v___y_4370_ = v___y_4411_;
                    state = 2;
                    continue;
                } else {
                    v_a_4462_ = lean_ctor_get(v___x_4461_, 0);
                    v_isSharedCheck_4469_ = (!lean_is_exclusive(v___x_4461_)) as u8;
                    if v_isSharedCheck_4469_ == 0 {
                        v___x_4464_ = v___x_4461_;
                        v_isShared_4465_ = v_isSharedCheck_4469_;
                        state = 18;
                        continue;
                    } else {
                        lean_inc(v_a_4462_);
                        lean_dec(v___x_4461_);
                        v___x_4464_ = lean_box(0);
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
                    v_reuseFailAlloc_4468_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4468_, 0, v_a_4462_);
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
                    v_reuseFailAlloc_4483_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4483_, 0, v_a_4477_);
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
                    v_reuseFailAlloc_4491_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4491_, 0, v_a_4485_);
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
                    v_reuseFailAlloc_4499_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4499_, 0, v_a_4493_);
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
                    v_reuseFailAlloc_4508_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4508_, 0, v_a_4502_);
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
                    v_reuseFailAlloc_4516_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4516_, 0, v_a_4510_);
                    v___x_4515_ = v_reuseFailAlloc_4516_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_4515_;
            }
            30 => {
                lean_inc(v_a_4351_);
                lean_inc_ref(v_a_4350_);
                lean_inc(v_a_4349_);
                lean_inc_ref(v_a_4348_);
                lean_inc(v_fst_4526_);
                v___x_4531_ =
                    lean_infer_type(v_fst_4526_, v_a_4348_, v_a_4349_, v_a_4350_, v_a_4351_);
                if lean_obj_tag(v___x_4531_) == 0 {
                    v_a_4532_ = lean_ctor_get(v___x_4531_, 0);
                    lean_inc(v_a_4532_);
                    lean_dec_ref_known(v___x_4531_, 1);
                    lean_inc(v_a_4351_);
                    lean_inc_ref(v_a_4350_);
                    lean_inc(v_a_4349_);
                    lean_inc_ref(v_a_4348_);
                    lean_inc(v_snd_4527_);
                    v___x_4533_ =
                        lean_infer_type(v_snd_4527_, v_a_4348_, v_a_4349_, v_a_4350_, v_a_4351_);
                    if lean_obj_tag(v___x_4533_) == 0 {
                        v_a_4534_ = lean_ctor_get(v___x_4533_, 0);
                        lean_inc(v_a_4534_);
                        lean_dec_ref_known(v___x_4533_, 1);
                        v___x_4535_ = l_Lean_Meta_addPPExplicitToExposeDiff(
                            v_a_4532_, v_a_4534_, v_a_4348_, v_a_4349_, v_a_4350_, v_a_4351_,
                        );
                        if lean_obj_tag(v___x_4535_) == 0 {
                            v_a_4536_ = lean_ctor_get(v___x_4535_, 0);
                            lean_inc(v_a_4536_);
                            lean_dec_ref_known(v___x_4535_, 1);
                            v_fst_4537_ = lean_ctor_get(v_a_4536_, 0);
                            v_snd_4538_ = lean_ctor_get(v_a_4536_, 1);
                            v_isSharedCheck_4576_ = (!lean_is_exclusive(v_a_4536_)) as u8;
                            if v_isSharedCheck_4576_ == 0 {
                                v___x_4540_ = v_a_4536_;
                                v_isShared_4541_ = v_isSharedCheck_4576_;
                                state = 31;
                                continue;
                            } else {
                                lean_inc(v_snd_4538_);
                                lean_inc(v_fst_4537_);
                                lean_dec(v_a_4536_);
                                v___x_4540_ = lean_box(0);
                                v_isShared_4541_ = v_isSharedCheck_4576_;
                                state = 31;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_4529_);
                            lean_dec(v_snd_4527_);
                            lean_dec(v_fst_4526_);
                            lean_dec(v_a_4519_);
                            lean_del_object(v___x_4404_);
                            lean_dec(v_snd_4402_);
                            lean_del_object(v___x_4399_);
                            lean_del_object(v___x_4391_);
                            lean_dec(v_snd_4389_);
                            lean_del_object(v___x_4386_);
                            lean_dec_ref(v___x_4357_);
                            lean_dec_ref(v_result_4347_);
                            lean_dec_ref(v_expectedType_4346_);
                            v_a_4577_ = lean_ctor_get(v___x_4535_, 0);
                            v_isSharedCheck_4584_ = (!lean_is_exclusive(v___x_4535_)) as u8;
                            if v_isSharedCheck_4584_ == 0 {
                                v___x_4579_ = v___x_4535_;
                                v_isShared_4580_ = v_isSharedCheck_4584_;
                                state = 36;
                                continue;
                            } else {
                                lean_inc(v_a_4577_);
                                lean_dec(v___x_4535_);
                                v___x_4579_ = lean_box(0);
                                v_isShared_4580_ = v_isSharedCheck_4584_;
                                state = 36;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_4532_);
                        lean_del_object(v___x_4529_);
                        lean_dec(v_snd_4527_);
                        lean_dec(v_fst_4526_);
                        lean_dec(v_a_4519_);
                        lean_del_object(v___x_4404_);
                        lean_dec(v_snd_4402_);
                        lean_del_object(v___x_4399_);
                        lean_del_object(v___x_4391_);
                        lean_dec(v_snd_4389_);
                        lean_del_object(v___x_4386_);
                        lean_dec_ref(v___x_4357_);
                        lean_dec_ref(v_result_4347_);
                        lean_dec_ref(v_expectedType_4346_);
                        v_a_4585_ = lean_ctor_get(v___x_4533_, 0);
                        v_isSharedCheck_4592_ = (!lean_is_exclusive(v___x_4533_)) as u8;
                        if v_isSharedCheck_4592_ == 0 {
                            v___x_4587_ = v___x_4533_;
                            v_isShared_4588_ = v_isSharedCheck_4592_;
                            state = 38;
                            continue;
                        } else {
                            lean_inc(v_a_4585_);
                            lean_dec(v___x_4533_);
                            v___x_4587_ = lean_box(0);
                            v_isShared_4588_ = v_isSharedCheck_4592_;
                            state = 38;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_4529_);
                    lean_dec(v_snd_4527_);
                    lean_dec(v_fst_4526_);
                    lean_dec(v_a_4519_);
                    lean_del_object(v___x_4404_);
                    lean_dec(v_snd_4402_);
                    lean_del_object(v___x_4399_);
                    lean_del_object(v___x_4391_);
                    lean_dec(v_snd_4389_);
                    lean_del_object(v___x_4386_);
                    lean_dec_ref(v___x_4357_);
                    lean_dec_ref(v_result_4347_);
                    lean_dec_ref(v_expectedType_4346_);
                    v_a_4593_ = lean_ctor_get(v___x_4531_, 0);
                    v_isSharedCheck_4600_ = (!lean_is_exclusive(v___x_4531_)) as u8;
                    if v_isSharedCheck_4600_ == 0 {
                        v___x_4595_ = v___x_4531_;
                        v_isShared_4596_ = v_isSharedCheck_4600_;
                        state = 40;
                        continue;
                    } else {
                        lean_inc(v_a_4593_);
                        lean_dec(v___x_4531_);
                        v___x_4595_ = lean_box(0);
                        v_isShared_4596_ = v_isSharedCheck_4600_;
                        state = 40;
                        continue;
                    }
                }
            }
            31 => {
                v___x_4542_ = l_Lean_Elab_Term_instInhabitedCalcStepView_default;
                v___x_4543_ = lean_unsigned_to_nat(0);
                v___x_4544_ = lean_array_get_borrowed(v___x_4542_, v_steps_4345_, v___x_4543_);
                v_term_4545_ = lean_ctor_get(v___x_4544_, 1);
                v___x_4546_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__1);
                v___x_4547_ = l_Lean_MessageData_ofExpr(v_fst_4526_);
                v___x_4548_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabCalcSteps_spec__1___closed__3);
                if v_isShared_4541_ == 0 {
                    lean_ctor_set_tag(v___x_4540_, 7);
                    lean_ctor_set(v___x_4540_, 1, v___x_4548_);
                    lean_ctor_set(v___x_4540_, 0, v___x_4547_);
                    v___x_4550_ = v___x_4540_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_4575_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4575_, 0, v___x_4547_);
                    lean_ctor_set(v_reuseFailAlloc_4575_, 1, v___x_4548_);
                    v___x_4550_ = v_reuseFailAlloc_4575_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                v___x_4551_ = l_Lean_MessageData_ofExpr(v_fst_4537_);
                if v_isShared_4530_ == 0 {
                    lean_ctor_set_tag(v___x_4529_, 7);
                    lean_ctor_set(v___x_4529_, 1, v___x_4551_);
                    lean_ctor_set(v___x_4529_, 0, v___x_4550_);
                    v___x_4553_ = v___x_4529_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_4574_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4574_, 0, v___x_4550_);
                    lean_ctor_set(v_reuseFailAlloc_4574_, 1, v___x_4551_);
                    v___x_4553_ = v_reuseFailAlloc_4574_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                v___x_4554_ = l_Lean_indentD(v___x_4553_);
                v___x_4555_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4555_, 0, v___x_4546_);
                lean_ctor_set(v___x_4555_, 1, v___x_4554_);
                v___x_4556_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Term_throwCalcFailure___redArg___closed__7),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Term_throwCalcFailure___redArg___closed__7_once
                    ),
                    _init_l_Lean_Elab_Term_throwCalcFailure___redArg___closed__7,
                );
                v___x_4557_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4557_, 0, v___x_4555_);
                lean_ctor_set(v___x_4557_, 1, v___x_4556_);
                v___x_4558_ = l_Lean_MessageData_ofExpr(v_snd_4527_);
                v___x_4559_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4559_, 0, v___x_4558_);
                lean_ctor_set(v___x_4559_, 1, v___x_4548_);
                v___x_4560_ = l_Lean_MessageData_ofExpr(v_snd_4538_);
                v___x_4561_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4561_, 0, v___x_4559_);
                lean_ctor_set(v___x_4561_, 1, v___x_4560_);
                v___x_4562_ = l_Lean_indentD(v___x_4561_);
                v___x_4563_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4563_, 0, v___x_4557_);
                lean_ctor_set(v___x_4563_, 1, v___x_4562_);
                v___x_4564_ = l_Lean_logErrorAt___at___00Lean_Elab_Term_throwCalcFailure_spec__1(
                    v_term_4545_,
                    v___x_4563_,
                    v_a_4348_,
                    v_a_4349_,
                    v_a_4350_,
                    v_a_4351_,
                );
                if lean_obj_tag(v___x_4564_) == 0 {
                    lean_dec_ref_known(v___x_4564_, 1);
                    v___x_4565_ = (lean_unbox(v_a_4519_) as u8);
                    lean_dec(v_a_4519_);
                    v_failed_4407_ = v___x_4565_;
                    v___y_4408_ = v_a_4348_;
                    v___y_4409_ = v_a_4349_;
                    v___y_4410_ = v_a_4350_;
                    v___y_4411_ = v_a_4351_;
                    state = 9;
                    continue;
                } else {
                    lean_dec(v_a_4519_);
                    lean_del_object(v___x_4404_);
                    lean_dec(v_snd_4402_);
                    lean_del_object(v___x_4399_);
                    lean_del_object(v___x_4391_);
                    lean_dec(v_snd_4389_);
                    lean_del_object(v___x_4386_);
                    lean_dec_ref(v___x_4357_);
                    lean_dec_ref(v_result_4347_);
                    lean_dec_ref(v_expectedType_4346_);
                    v_a_4566_ = lean_ctor_get(v___x_4564_, 0);
                    v_isSharedCheck_4573_ = (!lean_is_exclusive(v___x_4564_)) as u8;
                    if v_isSharedCheck_4573_ == 0 {
                        v___x_4568_ = v___x_4564_;
                        v_isShared_4569_ = v_isSharedCheck_4573_;
                        state = 34;
                        continue;
                    } else {
                        lean_inc(v_a_4566_);
                        lean_dec(v___x_4564_);
                        v___x_4568_ = lean_box(0);
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
                    v_reuseFailAlloc_4572_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4572_, 0, v_a_4566_);
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
                    v_reuseFailAlloc_4583_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4583_, 0, v_a_4577_);
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
                    v_reuseFailAlloc_4591_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4591_, 0, v_a_4585_);
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
                    v_reuseFailAlloc_4599_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4599_, 0, v_a_4593_);
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
                    v_reuseFailAlloc_4608_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4608_, 0, v_a_4602_);
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
                    v_reuseFailAlloc_4617_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4617_, 0, v_a_4611_);
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
                    v_reuseFailAlloc_4625_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4625_, 0, v_a_4619_);
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
                    v_reuseFailAlloc_4639_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4639_, 0, v_a_4633_);
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
    mut v_steps_4641_: *mut LeanObject,
    mut v_expectedType_4642_: *mut LeanObject,
    mut v_result_4643_: *mut LeanObject,
    mut v_a_4644_: *mut LeanObject,
    mut v_a_4645_: *mut LeanObject,
    mut v_a_4646_: *mut LeanObject,
    mut v_a_4647_: *mut LeanObject,
    mut v_a_4648_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4649_: *mut LeanObject = core::ptr::null_mut();
    v_res_4649_ = l_Lean_Elab_Term_throwCalcFailure___redArg(
        v_steps_4641_,
        v_expectedType_4642_,
        v_result_4643_,
        v_a_4644_,
        v_a_4645_,
        v_a_4646_,
        v_a_4647_,
    );
    lean_dec(v_a_4647_);
    lean_dec_ref(v_a_4646_);
    lean_dec(v_a_4645_);
    lean_dec_ref(v_a_4644_);
    lean_dec_ref(v_steps_4641_);
    return v_res_4649_;
}
pub unsafe fn l_Lean_Elab_Term_throwCalcFailure(
    mut v_00_u03b1_4650_: *mut LeanObject,
    mut v_steps_4651_: *mut LeanObject,
    mut v_expectedType_4652_: *mut LeanObject,
    mut v_result_4653_: *mut LeanObject,
    mut v_a_4654_: *mut LeanObject,
    mut v_a_4655_: *mut LeanObject,
    mut v_a_4656_: *mut LeanObject,
    mut v_a_4657_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4659_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_4660_: *mut LeanObject,
    mut v_steps_4661_: *mut LeanObject,
    mut v_expectedType_4662_: *mut LeanObject,
    mut v_result_4663_: *mut LeanObject,
    mut v_a_4664_: *mut LeanObject,
    mut v_a_4665_: *mut LeanObject,
    mut v_a_4666_: *mut LeanObject,
    mut v_a_4667_: *mut LeanObject,
    mut v_a_4668_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4669_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_4667_);
    lean_dec_ref(v_a_4666_);
    lean_dec(v_a_4665_);
    lean_dec_ref(v_a_4664_);
    lean_dec_ref(v_steps_4661_);
    return v_res_4669_;
}
pub unsafe fn l_Lean_Elab_Term_elabCalc___lam__0(
    mut v_a_4670_: *mut LeanObject,
    mut v_x_4671_: *mut LeanObject,
    mut v___y_4672_: *mut LeanObject,
    mut v___y_4673_: *mut LeanObject,
    mut v___y_4674_: *mut LeanObject,
    mut v___y_4675_: *mut LeanObject,
    mut v___y_4676_: *mut LeanObject,
    mut v___y_4677_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4679_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_4680_: *mut LeanObject,
    mut v_x_4681_: *mut LeanObject,
    mut v___y_4682_: *mut LeanObject,
    mut v___y_4683_: *mut LeanObject,
    mut v___y_4684_: *mut LeanObject,
    mut v___y_4685_: *mut LeanObject,
    mut v___y_4686_: *mut LeanObject,
    mut v___y_4687_: *mut LeanObject,
    mut v___y_4688_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4689_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_4687_);
    lean_dec_ref(v___y_4686_);
    lean_dec(v___y_4685_);
    lean_dec_ref(v___y_4684_);
    lean_dec(v_x_4681_);
    lean_dec_ref(v_a_4680_);
    return v_res_4689_;
}
pub unsafe fn l_Lean_Elab_Term_elabCalc___lam__1(
    mut v_a_4690_: *mut LeanObject,
    mut v_x_4691_: *mut LeanObject,
    mut v___y_4692_: *mut LeanObject,
    mut v___y_4693_: *mut LeanObject,
    mut v___y_4694_: *mut LeanObject,
    mut v___y_4695_: *mut LeanObject,
    mut v___y_4696_: *mut LeanObject,
    mut v___y_4697_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4699_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_4700_: *mut LeanObject,
    mut v_x_4701_: *mut LeanObject,
    mut v___y_4702_: *mut LeanObject,
    mut v___y_4703_: *mut LeanObject,
    mut v___y_4704_: *mut LeanObject,
    mut v___y_4705_: *mut LeanObject,
    mut v___y_4706_: *mut LeanObject,
    mut v___y_4707_: *mut LeanObject,
    mut v___y_4708_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4709_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_4707_);
    lean_dec_ref(v___y_4706_);
    lean_dec(v___y_4705_);
    lean_dec_ref(v___y_4704_);
    lean_dec(v_x_4701_);
    lean_dec_ref(v_a_4700_);
    return v_res_4709_;
}
pub unsafe fn l_Lean_Elab_Term_elabCalc(
    mut v_x_4714_: *mut LeanObject,
    mut v_x_4715_: *mut LeanObject,
    mut v_a_4716_: *mut LeanObject,
    mut v_a_4717_: *mut LeanObject,
    mut v_a_4718_: *mut LeanObject,
    mut v_a_4719_: *mut LeanObject,
    mut v_a_4720_: *mut LeanObject,
    mut v_a_4721_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4724_: u8 = 0;
    let mut v___x_4725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_steps_4727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4729_: u8 = 0;
    let mut v___x_4730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_4731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_4743_: u8 = 0;
    let mut v_cancelTk_x3f_4744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4745_: u8 = 0;
    let mut v_inheritedTraceOptions_4746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tk_4748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4762_: u8 = 0;
    let mut v___x_4764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4766_: u8 = 0;
    let mut v_a_4767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4770_: u8 = 0;
    let mut v___x_4772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4774_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4723_ = l_Lean_Elab_Term_elabCalc___closed__1;
                lean_inc(v_x_4714_);
                v___x_4724_ = l_Lean_Syntax_isOfKind(v_x_4714_, v___x_4723_);
                if v___x_4724_ == 0 {
                    lean_dec(v_x_4715_);
                    lean_dec(v_x_4714_);
                    v___x_4725_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
                    return v___x_4725_;
                } else {
                    v___x_4726_ = lean_unsigned_to_nat(1);
                    v_steps_4727_ = l_Lean_Syntax_getArg(v_x_4714_, v___x_4726_);
                    v___x_4728_ = l_Lean_Elab_Term_mkCalcStepViews___closed__1;
                    lean_inc(v_steps_4727_);
                    v___x_4729_ = l_Lean_Syntax_isOfKind(v_steps_4727_, v___x_4728_);
                    if v___x_4729_ == 0 {
                        lean_dec(v_steps_4727_);
                        lean_dec(v_x_4715_);
                        lean_dec(v_x_4714_);
                        v___x_4730_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Term_mkCalcFirstStepView_spec__0___redArg();
                        return v___x_4730_;
                    } else {
                        v_fileName_4731_ = lean_ctor_get(v_a_4720_, 0);
                        v_fileMap_4732_ = lean_ctor_get(v_a_4720_, 1);
                        v_options_4733_ = lean_ctor_get(v_a_4720_, 2);
                        v_currRecDepth_4734_ = lean_ctor_get(v_a_4720_, 3);
                        v_maxRecDepth_4735_ = lean_ctor_get(v_a_4720_, 4);
                        v_ref_4736_ = lean_ctor_get(v_a_4720_, 5);
                        v_currNamespace_4737_ = lean_ctor_get(v_a_4720_, 6);
                        v_openDecls_4738_ = lean_ctor_get(v_a_4720_, 7);
                        v_initHeartbeats_4739_ = lean_ctor_get(v_a_4720_, 8);
                        v_maxHeartbeats_4740_ = lean_ctor_get(v_a_4720_, 9);
                        v_quotContext_4741_ = lean_ctor_get(v_a_4720_, 10);
                        v_currMacroScope_4742_ = lean_ctor_get(v_a_4720_, 11);
                        v_diag_4743_ = lean_ctor_get_uint8(
                            v_a_4720_,
                            (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                        );
                        v_cancelTk_x3f_4744_ = lean_ctor_get(v_a_4720_, 12);
                        v_suppressElabErrors_4745_ = lean_ctor_get_uint8(
                            v_a_4720_,
                            (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                        );
                        v_inheritedTraceOptions_4746_ = lean_ctor_get(v_a_4720_, 13);
                        v___x_4747_ = lean_unsigned_to_nat(0);
                        v_tk_4748_ = l_Lean_Syntax_getArg(v_x_4714_, v___x_4747_);
                        lean_dec(v_x_4714_);
                        v_ref_4749_ = l_Lean_replaceRef(v_tk_4748_, v_ref_4736_);
                        lean_dec(v_tk_4748_);
                        lean_inc_ref(v_inheritedTraceOptions_4746_);
                        lean_inc(v_cancelTk_x3f_4744_);
                        lean_inc(v_currMacroScope_4742_);
                        lean_inc(v_quotContext_4741_);
                        lean_inc(v_maxHeartbeats_4740_);
                        lean_inc(v_initHeartbeats_4739_);
                        lean_inc(v_openDecls_4738_);
                        lean_inc(v_currNamespace_4737_);
                        lean_inc(v_maxRecDepth_4735_);
                        lean_inc(v_currRecDepth_4734_);
                        lean_inc_ref(v_options_4733_);
                        lean_inc_ref(v_fileMap_4732_);
                        lean_inc_ref(v_fileName_4731_);
                        v___x_4750_ = lean_alloc_ctor(0, 14, (2) as u32);
                        lean_ctor_set(v___x_4750_, 0, v_fileName_4731_);
                        lean_ctor_set(v___x_4750_, 1, v_fileMap_4732_);
                        lean_ctor_set(v___x_4750_, 2, v_options_4733_);
                        lean_ctor_set(v___x_4750_, 3, v_currRecDepth_4734_);
                        lean_ctor_set(v___x_4750_, 4, v_maxRecDepth_4735_);
                        lean_ctor_set(v___x_4750_, 5, v_ref_4749_);
                        lean_ctor_set(v___x_4750_, 6, v_currNamespace_4737_);
                        lean_ctor_set(v___x_4750_, 7, v_openDecls_4738_);
                        lean_ctor_set(v___x_4750_, 8, v_initHeartbeats_4739_);
                        lean_ctor_set(v___x_4750_, 9, v_maxHeartbeats_4740_);
                        lean_ctor_set(v___x_4750_, 10, v_quotContext_4741_);
                        lean_ctor_set(v___x_4750_, 11, v_currMacroScope_4742_);
                        lean_ctor_set(v___x_4750_, 12, v_cancelTk_x3f_4744_);
                        lean_ctor_set(v___x_4750_, 13, v_inheritedTraceOptions_4746_);
                        lean_ctor_set_uint8(
                            v___x_4750_,
                            (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                            v_diag_4743_,
                        );
                        lean_ctor_set_uint8(
                            v___x_4750_,
                            (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
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
                        if lean_obj_tag(v___x_4751_) == 0 {
                            v_a_4752_ = lean_ctor_get(v___x_4751_, 0);
                            lean_inc(v_a_4752_);
                            lean_dec_ref_known(v___x_4751_, 1);
                            v___x_4753_ = l_Lean_Elab_Term_elabCalcSteps(
                                v_a_4752_,
                                v_a_4716_,
                                v_a_4717_,
                                v_a_4718_,
                                v_a_4719_,
                                v___x_4750_,
                                v_a_4721_,
                            );
                            if lean_obj_tag(v___x_4753_) == 0 {
                                v_a_4754_ = lean_ctor_get(v___x_4753_, 0);
                                lean_inc(v_a_4754_);
                                lean_dec_ref_known(v___x_4753_, 1);
                                v_fst_4755_ = lean_ctor_get(v_a_4754_, 0);
                                lean_inc(v_fst_4755_);
                                lean_dec(v_a_4754_);
                                lean_inc(v_a_4752_);
                                v___f_4756_ = lean_alloc_closure(
                                    l_Lean_Elab_Term_elabCalc___lam__0___boxed
                                        as *mut core::ffi::c_void,
                                    9,
                                    1,
                                );
                                lean_closure_set(v___f_4756_, 0, v_a_4752_);
                                v___f_4757_ = lean_alloc_closure(
                                    l_Lean_Elab_Term_elabCalc___lam__1___boxed
                                        as *mut core::ffi::c_void,
                                    9,
                                    1,
                                );
                                lean_closure_set(v___f_4757_, 0, v_a_4752_);
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
                                lean_dec_ref_known(v___x_4750_, 14);
                                return v___x_4758_;
                            } else {
                                lean_dec(v_a_4752_);
                                lean_dec_ref_known(v___x_4750_, 14);
                                lean_dec(v_x_4715_);
                                v_a_4759_ = lean_ctor_get(v___x_4753_, 0);
                                v_isSharedCheck_4766_ = (!lean_is_exclusive(v___x_4753_)) as u8;
                                if v_isSharedCheck_4766_ == 0 {
                                    v___x_4761_ = v___x_4753_;
                                    v_isShared_4762_ = v_isSharedCheck_4766_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_a_4759_);
                                    lean_dec(v___x_4753_);
                                    v___x_4761_ = lean_box(0);
                                    v_isShared_4762_ = v_isSharedCheck_4766_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref_known(v___x_4750_, 14);
                            lean_dec(v_x_4715_);
                            v_a_4767_ = lean_ctor_get(v___x_4751_, 0);
                            v_isSharedCheck_4774_ = (!lean_is_exclusive(v___x_4751_)) as u8;
                            if v_isSharedCheck_4774_ == 0 {
                                v___x_4769_ = v___x_4751_;
                                v_isShared_4770_ = v_isSharedCheck_4774_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_4767_);
                                lean_dec(v___x_4751_);
                                v___x_4769_ = lean_box(0);
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
                    v_reuseFailAlloc_4765_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4765_, 0, v_a_4759_);
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
                    v_reuseFailAlloc_4773_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4773_, 0, v_a_4767_);
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
    mut v_x_4775_: *mut LeanObject,
    mut v_x_4776_: *mut LeanObject,
    mut v_a_4777_: *mut LeanObject,
    mut v_a_4778_: *mut LeanObject,
    mut v_a_4779_: *mut LeanObject,
    mut v_a_4780_: *mut LeanObject,
    mut v_a_4781_: *mut LeanObject,
    mut v_a_4782_: *mut LeanObject,
    mut v_a_4783_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4784_: *mut LeanObject = core::ptr::null_mut();
    v_res_4784_ = l_Lean_Elab_Term_elabCalc(
        v_x_4775_, v_x_4776_, v_a_4777_, v_a_4778_, v_a_4779_, v_a_4780_, v_a_4781_, v_a_4782_,
    );
    lean_dec(v_a_4782_);
    lean_dec_ref(v_a_4781_);
    lean_dec(v_a_4780_);
    lean_dec_ref(v_a_4779_);
    lean_dec(v_a_4778_);
    lean_dec_ref(v_a_4777_);
    return v_res_4784_;
}
pub unsafe fn l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1()
-> *mut LeanObject {
    let mut v___x_4792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4796_: *mut LeanObject = core::ptr::null_mut();
    v___x_4792_ = l_Lean_Elab_Term_termElabAttribute;
    v___x_4793_ = l_Lean_Elab_Term_elabCalc___closed__1;
    v___x_4794_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1;
    v___x_4795_ = lean_alloc_closure(
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
    mut v_a_4797_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4798_: *mut LeanObject = core::ptr::null_mut();
    v_res_4798_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1();
    return v_res_4798_;
}
pub unsafe fn l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_docString__3()
-> *mut LeanObject {
    let mut v___x_4801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4803_: *mut LeanObject = core::ptr::null_mut();
    v___x_4801_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1;
    v___x_4802_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_docString__3___closed__0;
    v___x_4803_ = l_Lean_addBuiltinDocString(v___x_4801_, v___x_4802_);
    return v___x_4803_;
}
pub unsafe fn l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_docString__3___boxed(
    mut v_a_4804_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4805_: *mut LeanObject = core::ptr::null_mut();
    v_res_4805_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_docString__3();
    return v_res_4805_;
}
pub unsafe fn l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5()
-> *mut LeanObject {
    let mut v___x_4832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4834_: *mut LeanObject = core::ptr::null_mut();
    v___x_4832_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1___closed__1;
    v___x_4833_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___closed__6;
    v___x_4834_ = l_Lean_addBuiltinDeclarationRanges(v___x_4832_, v___x_4833_);
    return v___x_4834_;
}
pub unsafe fn l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5___boxed(
    mut v_a_4835_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4836_: *mut LeanObject = core::ptr::null_mut();
    v_res_4836_ = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5();
    return v_res_4836_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Calc(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_App(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_docString__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_elabCalc___regBuiltin_Lean_Elab_Term_elabCalc_declRange__5();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Calc(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Calc(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_App(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Calc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Calc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Calc(builtin);
}
